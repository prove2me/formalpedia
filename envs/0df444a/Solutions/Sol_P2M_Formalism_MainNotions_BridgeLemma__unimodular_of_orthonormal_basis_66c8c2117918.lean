-- Prove2me | solution 1 for P2M_Formalism_MainNotions_BridgeLemma__unimodular_of_orthonormal_basis_66c8c2117918
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:55:24.669696+00:00
-- url     : https://prove2.me/submissions/26d496d9-a1d1-4f83-b812-a0cdd0854738

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_GenusOrthonormalIntegralUnimodular
import Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__integral_of_orthonormal_basis_bf41afc29196
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.MainNotions.BridgeLemma₂
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsUnimodular h L := by
  have hint := integral_of_orthonormal_basis h L hL
  obtain ⟨e, -, hsp, rfl, he⟩ := hL
  apply le_antisymm
  · intro z hz
    rw [dualBasic_mem_dual] at hz
    have hz' : z ∈ Submodule.span K (Set.range e) := by rw [hsp]; trivial
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hz'
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 := hz (e i) (Submodule.subset_span ⟨i, rfl⟩)
    have h2 : h (e i) (∑ j, c j • e j) = c i := by
      simp only [map_sum, map_smul, he, smul_eq_mul]
      simp [Finset.sum_ite_eq]
    rw [h2] at h1
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro z hz
    rw [dualBasic_mem_dual]
    intro y hy
    exact hint y hy z hz
end Formalism.MainNotions.BridgeLemma₂
