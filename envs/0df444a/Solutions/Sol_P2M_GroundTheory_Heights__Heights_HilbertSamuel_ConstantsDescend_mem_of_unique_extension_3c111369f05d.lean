-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_mem_of_unique_extension_3c111369f05d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:05:49.835149+00:00
-- url     : https://prove2.me/submissions/c6c14e6a-9a71-4e6d-9184-56db05726ae8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_algebraMap_surjective_46fcacb94b77

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution {Ω : Type*} [Field Ω] [CharZero Ω] (A : Subalgebra ℚ Ω) [Algebra.FiniteType ℚ A]
    (θ : Ω) (hθ : IsIntegral ℚ θ)
    (huniq : ∀ w w' : Algebra.adjoin A {θ} →+* ℂ,
      w.comp (algebraMap A (Algebra.adjoin A {θ})) = w'.comp (algebraMap A (Algebra.adjoin A {θ})) →
        w ⟨θ, Algebra.subset_adjoin rfl⟩ = w' ⟨θ, Algebra.subset_adjoin rfl⟩) :
    θ ∈ A := by
  have hgen : Algebra.adjoin A {(⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})} = ⊤ := by
    have := Algebra.adjoin_adjoin_coe_preimage (R := A) (s := ({θ} : Set Ω))
    convert this using 2
    ext x
    simp [Subtype.ext_iff]
  have hinj : Function.Injective (algebraMap A (Algebra.adjoin A {θ})) := by
    intro x y h
    apply Subtype.ext
    have := congrArg (Algebra.adjoin A {θ}).val h
    rw [AlgHom.commutes, AlgHom.commutes] at this
    exact this
  have hpB : aeval (⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})
      ((minpoly ℚ θ).map (algebraMap ℚ A)) = 0 := by
    have h := aeval_algHom_apply (Algebra.adjoin A {θ}).val ⟨θ, Algebra.subset_adjoin rfl⟩
      ((minpoly ℚ θ).map (algebraMap ℚ A))
    rw [aeval_map_algebraMap] at h
    have h0 : (Algebra.adjoin A {θ}).val (aeval (⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})
        ((minpoly ℚ θ).map (algebraMap ℚ A))) = 0 := by
      rw [← h]
      exact minpoly.aeval ℚ θ
    exact (map_eq_zero_iff _ Subtype.val_injective).1 h0
  obtain ⟨a, ha⟩ := algebraMap_surjective hinj _ hgen (minpoly ℚ θ) (minpoly.monic hθ)
    (minpoly.irreducible hθ).separable hpB huniq ⟨θ, Algebra.subset_adjoin rfl⟩
  have h1 : (Algebra.adjoin A {θ}).val (algebraMap A _ a) = θ := congrArg Subtype.val ha
  rw [AlgHom.commutes] at h1
  rw [← h1]
  exact a.2
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
