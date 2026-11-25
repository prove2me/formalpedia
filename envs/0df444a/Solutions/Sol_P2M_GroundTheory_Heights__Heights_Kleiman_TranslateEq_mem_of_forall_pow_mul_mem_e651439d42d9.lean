-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_mem_of_forall_pow_mul_mem_e651439d42d9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:07:04.875802+00:00
-- url     : https://prove2.me/submissions/7570c95e-dcb4-4a9a-9fba-67b986c33a7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundleLocal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_exists_sum_mul_pow_eq_one_09868cad90a2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
open scoped Pointwise
variable {S : Type*} [CommRing S] {Ω : Type*} [Field Ω] [Algebra S Ω]
variable (A : Subalgebra S Ω) {k : ℕ} (f c : Fin k → Ω)
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
theorem _root_.solution (hf : ∀ l, f l ∈ A) (hc : ∀ l, c l ∈ A) (hs : ∑ l, c l * f l = 1)
    (P : Submodule A Ω) {z : Ω} (hz : ∀ l, ∃ m : ℕ, f l ^ m * z ∈ P) : z ∈ P := by
  choose m hm using hz
  obtain ⟨d, hd, hsum⟩ := exists_sum_mul_pow_eq_one A f c hf hc hs (Finset.univ.sup m)
  have key : z = ∑ l, (⟨d l * f l ^ (Finset.univ.sup m - m l), mul_mem (hd l) (pow_mem (hf l) _)⟩ : A) •
      (f l ^ m l * z) := by
    simp only [Subalgebra.smul_def, smul_eq_mul]
    calc z = (∑ l, d l * f l ^ Finset.univ.sup m) * z := by rw [hsum, one_mul]
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [← pow_sub_mul_pow (f l) (Finset.le_sup (Finset.mem_univ l))]
        ring
  rw [key]
  exact sum_mem fun l _ => P.smul_mem _ (hm l)
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
