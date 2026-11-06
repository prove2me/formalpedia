-- Prove2me | solution 1 for QEC.Locality.generatorRank_ge_two_correctable_region_cards
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:23:34.721046+00:00
-- url     : https://prove2.me/submissions/a77bd88c-5f03-4e24-9b34-2aadde08df7a

import Definitions.Def_QEC_Coding_Stabilizer_Parameters
import Definitions.Def_QEC_Locality_CorrectableRegions_SemanticDistanceErasure
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Theorems.Thm_QEC_Locality_finrank_coordinateSubspace
import Theorems.Thm_QEC_Locality_orthogonal_coordinateSubspace
import Theorems.Thm_QEC_Locality_coordinateSubspace_le_coordinateSubspace_compl
import Theorems.Thm_QEC_Locality_normalizer_inf_coordinateSubspace_le_stabilizer
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_isAlt
import Theorems.Thm_QEC_Coding_FiniteSymplectic_form_nondegenerate
import Theorems.Thm_QEC_Coding_StabilizerCode_generatedVectorSubspace_isotropic

section
noncomputable section
namespace QEC
namespace Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
private theorem orthogonal_sup (U V : Submodule (ZMod 2)
    (SymplecticVector (ZMod 2) ι)) :
    FiniteSymplectic.form.orthogonal (U ⊔ V) =
      FiniteSymplectic.form.orthogonal U ⊓ FiniteSymplectic.form.orthogonal V := by
  ext x
  constructor
  · intro hx
    exact ⟨fun u hu => hx u (Submodule.mem_sup_left hu),
      fun v hv => hx v (Submodule.mem_sup_right hv)⟩
  · rintro ⟨hU, hV⟩ y hy
    rcases Submodule.mem_sup.mp hy with ⟨u, hu, v, hv, rfl⟩
    change FiniteSymplectic.form (u + v) x = 0
    rw [map_add]
    change FiniteSymplectic.form u x + FiniteSymplectic.form v x = 0
    rw [hU u hu, hV v hv, add_zero]
omit [DecidableEq ι] in
private theorem stabilizer_rank_coordinate_identity
    (L W : Submodule (ZMod 2) (SymplecticVector (ZMod 2) ι))
    (hIsotropic : L ≤ FiniteSymplectic.form.orthogonal L)
    (hLocalNormalizer : FiniteSymplectic.form.orthogonal L ⊓ W ≤ L) :
    Module.finrank (ZMod 2) L + Module.finrank (ZMod 2) ↥(L ⊓ W) =
      Module.finrank (ZMod 2) W +
        Module.finrank (ZMod 2) ↥(L ⊓ FiniteSymplectic.form.orthogonal W) := by
  have hLocalEq : FiniteSymplectic.form.orthogonal L ⊓ W = L ⊓ W := by
    apply le_antisymm
    · intro x hx
      exact ⟨hLocalNormalizer hx, hx.2⟩
    · intro x hx
      exact ⟨hIsotropic hx.1, hx.2⟩
  have hOrthogonalSup :
      FiniteSymplectic.form.orthogonal
          (L ⊔ FiniteSymplectic.form.orthogonal W) =
        FiniteSymplectic.form.orthogonal L ⊓ W := by
    rw [orthogonal_sup,
      LinearMap.BilinForm.orthogonal_orthogonal FiniteSymplectic.form_nondegenerate
        FiniteSymplectic.form_isAlt.isRefl]
  have hSup := Submodule.finrank_sup_add_finrank_inf_eq L
    (FiniteSymplectic.form.orthogonal W)
  have hOuter := LinearMap.BilinForm.finrank_orthogonal
    FiniteSymplectic.form_nondegenerate
    (L ⊔ FiniteSymplectic.form.orthogonal W)
  have hInner := LinearMap.BilinForm.finrank_orthogonal
    FiniteSymplectic.form_nondegenerate W
  rw [hOrthogonalSup, hLocalEq] at hOuter
  have hOuterAdd :
      Module.finrank (ZMod 2) ↥(L ⊓ W) +
        Module.finrank (ZMod 2) ↥(L ⊔ FiniteSymplectic.form.orthogonal W) =
      Module.finrank (ZMod 2) (SymplecticVector (ZMod 2) ι) := by
    rw [hOuter, Nat.sub_add_cancel (Submodule.finrank_le _)]
  have hInnerAdd :
      Module.finrank (ZMod 2) ↥(FiniteSymplectic.form.orthogonal W) +
        Module.finrank (ZMod 2) W =
      Module.finrank (ZMod 2) (SymplecticVector (ZMod 2) ι) := by
    rw [hInner, Nat.sub_add_cancel (Submodule.finrank_le _)]
  omega
end Locality
end QEC
end
end

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Locality
open QEC Semantics Coding
open PauliSymplectic
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    {κ : Type v} [Fintype κ]
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (A B : FiniteSubsystem ι)
    (hDisjoint : Disjoint A.selected B.selected)
    (recoveryA : QuantumChannel A.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryA : Correctable (Qubit.QubitRegister ι) A.complementSystem P.semanticCode
      A.erasureChannelFromRegister recoveryA)
    (recoveryB : QuantumChannel B.complementSystem (Qubit.QubitRegister ι))
    (hRecoveryB : Correctable (Qubit.QubitRegister ι) B.complementSystem P.semanticCode
      B.erasureChannelFromRegister recoveryB) :
    A.selected.card + B.selected.card ≤ P.generatorRank := by
  have hRankA := stabilizer_rank_coordinate_identity
    P.code.1.generatedVectorSubspace (coordinateSubspace A.selected)
    P.code.1.generatedVectorSubspace_isotropic
    (normalizer_inf_coordinateSubspace_le_stabilizer P A recoveryA hRecoveryA)
  have hRankB := stabilizer_rank_coordinate_identity
    P.code.1.generatedVectorSubspace (coordinateSubspace B.selected)
    P.code.1.generatedVectorSubspace_isotropic
    (normalizer_inf_coordinateSubspace_le_stabilizer P B recoveryB hRecoveryB)
  have hBInAOrthogonal : coordinateSubspace B.selected ≤
      FiniteSymplectic.form.orthogonal (coordinateSubspace A.selected) := by
    rw [orthogonal_coordinateSubspace]
    exact coordinateSubspace_le_coordinateSubspace_compl hDisjoint
  have hAInBOrthogonal : coordinateSubspace A.selected ≤
      FiniteSymplectic.form.orthogonal (coordinateSubspace B.selected) := by
    rw [orthogonal_coordinateSubspace]
    exact coordinateSubspace_le_coordinateSubspace_compl hDisjoint.symm
  have hInfB : P.code.1.generatedVectorSubspace ⊓ coordinateSubspace B.selected ≤
      P.code.1.generatedVectorSubspace ⊓
        FiniteSymplectic.form.orthogonal (coordinateSubspace A.selected) := by
    intro x hx
    exact ⟨hx.1, hBInAOrthogonal hx.2⟩
  have hInfA : P.code.1.generatedVectorSubspace ⊓ coordinateSubspace A.selected ≤
      P.code.1.generatedVectorSubspace ⊓
        FiniteSymplectic.form.orthogonal (coordinateSubspace B.selected) := by
    intro x hx
    exact ⟨hx.1, hAInBOrthogonal hx.2⟩
  have hDimB := Submodule.finrank_mono hInfB
  have hDimA := Submodule.finrank_mono hInfA
  rw [finrank_coordinateSubspace] at hRankA hRankB
  change A.selected.card + B.selected.card ≤
    Module.finrank (ZMod 2) P.code.1.generatedVectorSubspace
  omega
end QEC.Locality
