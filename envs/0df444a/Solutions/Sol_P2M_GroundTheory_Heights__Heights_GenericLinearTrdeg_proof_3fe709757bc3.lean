-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_proof_3fe709757bc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:23:09.020833+00:00
-- url     : https://prove2.me/submissions/2ee5026d-25e4-47e3-ba62-0a71288dfc76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PGenericLinearTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_algebraicIndependent_rows_8439d4126368
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericLinearTrdeg_exists_indep_0c0d576242a7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
namespace GroundTheory.Heights₂.Heights
namespace GenericLinearTrdeg
theorem _root_.solution : GenericLinearTrdeg.Statement := by
  intro F E _ _ _ N k d η hd
  classical
  set S := Algebra.adjoin F
    (Set.range (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E)) ∪
      Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m))) with hSdef
  obtain ⟨j, hj⟩ := GenericLinearTrdeg.exists_indep η d hd
  have hrk : min k d ≤ k := min_le_left _ _
  have hrd : min k d ≤ d := min_le_right _ _
  have hind := GenericLinearTrdeg.algebraicIndependent_rows F E N k (min k d) η hrk
    (j ∘ Fin.castLE hrd) (hj.comp _ (Fin.castLE_injective hrd))
  have hlow : ((k * N + min k d : ℕ) : Cardinal) ≤ Algebra.trdeg F S := by
    have hmem : ∀ t, Sum.elim (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E))
        (fun l : Fin (min k d) => ∑ m, X (Fin.castLE hrk l, m) * C (η m)) t ∈ S := by
      rintro (ab | l)
      · exact Algebra.subset_adjoin (Or.inl ⟨ab, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inr ⟨Fin.castLE hrk l, rfl⟩)
    let G' : (Fin k × Fin N) ⊕ Fin (min k d) → S := fun t => ⟨_, hmem t⟩
    have hG : AlgebraicIndependent F G' := AlgebraicIndependent.of_comp S.val hind
    have := hG.cardinalMk_le_trdeg
    have hc : Cardinal.mk ((Fin k × Fin N) ⊕ Fin (min k d)) = ((k * N + min k d : ℕ) : Cardinal) := by
      rw [Cardinal.mk_fintype]
      simp
    rwa [hc] at this
  have hup1 : Algebra.trdeg F S ≤ ((k * N + k : ℕ) : Cardinal) := by
    let G : (Fin k × Fin N) ⊕ Fin k → MvPolynomial (Fin k × Fin N) E :=
      Sum.elim (fun ij => X ij) (fun i => ∑ m, X (i, m) * C (η m))
    have hS : S = (MvPolynomial.aeval (R := F) G).range := by
      rw [← Algebra.adjoin_range_eq_range_aeval, Set.Sum.elim_range]
    have h1 := trdeg_le_of_surjective (MvPolynomial.aeval (R := F) G).rangeRestrict
      (AlgHom.rangeRestrict_surjective _)
    rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype] at h1
    rw [hS]
    convert h1 using 1
    simp
  have hup2 : Algebra.trdeg F S ≤ ((k * N + d : ℕ) : Cardinal) := by
    set D := Algebra.adjoin F (Set.range η)
    let φ : MvPolynomial (Fin k × Fin N) D →ₐ[F] MvPolynomial (Fin k × Fin N) E :=
      MvPolynomial.mapAlgHom D.val
    have hle : S ≤ φ.range := by
      rw [hSdef, Algebra.adjoin_le_iff]
      rintro _ (⟨ab, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨X ab, by simp [φ]⟩
      · refine ⟨∑ m, X (i, m) * C ⟨η m, Algebra.subset_adjoin ⟨m, rfl⟩⟩, ?_⟩
        simp [φ]
    have h1 := trdeg_le_of_injective (Subalgebra.inclusion hle) (Subalgebra.inclusion_injective hle)
    have h2 := trdeg_le_of_surjective φ.rangeRestrict (AlgHom.rangeRestrict_surjective _)
    have : FaithfulSMul F D :=
      (faithfulSMul_iff_algebraMap_injective F D).mpr (algebraMap F D).injective
    have : FaithfulSMul D (MvPolynomial (Fin k × Fin N) D) :=
      (faithfulSMul_iff_algebraMap_injective _ _).mpr (MvPolynomial.C_injective _ _)
    have h3 := trdeg_add_eq F D (A := MvPolynomial (Fin k × Fin N) D)
    rw [MvPolynomial.trdeg_of_isDomain, hd, Cardinal.lift_id, Cardinal.mk_fintype] at h3
    refine h1.trans (h2.trans (le_of_eq ?_))
    rw [← h3]
    simp [add_comm]
  refine le_antisymm ?_ hlow
  rcases le_total k d with h | h
  · rw [min_eq_left h]; exact hup1
  · rw [min_eq_right h]; exact hup2
end GenericLinearTrdeg
end GroundTheory.Heights₂.Heights
