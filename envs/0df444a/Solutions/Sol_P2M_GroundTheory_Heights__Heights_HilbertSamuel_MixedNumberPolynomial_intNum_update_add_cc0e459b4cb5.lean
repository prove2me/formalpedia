-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_update_add_cc0e459b4cb5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:42:20.463974+00:00
-- url     : https://prove2.me/submissions/5276fefa-32ee-43b8-8de5-2c808518d7bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PMixedNumberPolynomial
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_mixedDiff_cons_be1bace3a907
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_intNum_perm_42358017be47
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_MixedNumberPolynomial_eventualValue_step_add_d4bcf2015b36

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
variable {K : Type*}
variable [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
theorem _root_.solution (F : Type*) [Field F] {ι : K → Type*} (q : Ideal (MRing ι F)) {d : ℕ}
    (hex : ∀ bs : Fin d → K → ℤ, ∃ c, ∀ᶠ m in atTop, mixedDiff bs (hilbFn q) m = c)
    (bs : Fin d → K → ℤ) (j : Fin d) (x y : K → ℤ) :
    intNum F q (Function.update bs j (x + y)) =
      intNum F q (Function.update bs j x) + intNum F q (Function.update bs j y) := by
  cases d with
  | zero => exact j.elim0
  | succ n =>
    set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j with hσ
    set t : Fin n → K → ℤ := fun i => bs (σ i.succ) with ht
    have key : ∀ v, intNum F q (Function.update bs j v) =
        eventualValue (gStep v (mixedDiff t (hilbFn q))) := by
      intro v
      rw [← intNum_perm F q σ]
      have hc : Function.update bs j v ∘ σ = Fin.cons v t := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i
        · simp [hσ]
        · have hne : σ i.succ ≠ j := by
            intro hij
            have h0 : σ 0 = j := by simp [hσ]
            exact Fin.succ_ne_zero i (σ.injective (hij.trans h0.symm))
          simp only [Function.comp_apply, Fin.cons_succ, ht]
          rw [Function.update_of_ne hne]
      rw [hc]
      unfold intNum
      rw [mixedDiff_cons]
    rw [key, key, key]
    apply eventualValue_step_add
    · simpa only [mixedDiff_cons] using hex (Fin.cons x t)
    · simpa only [mixedDiff_cons] using hex (Fin.cons y t)
end GroundTheory.Heights₂.Heights.HilbertSamuel.MixedNumberPolynomial
