-- Prove2me | solution 1 for PI.OmVe.notFree_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:00:37.016138+00:00
-- url     : https://prove2.me/submissions/4a3147e4-b01b-4b6c-b64a-a8f4bc5410f8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_CountGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_FfHSelfOfSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmVe
open PI.VolStabSW Matrix
variable {k : Type} [Field k] {M : ℕ} (J : Matrix (Fin M) (Fin M) (k × k))
namespace PI.OmVe
theorem _root_.solution (x : Fin M → k × k) :
    (¬ ∀ c : k × k, c • x = 0 → c = 0) ↔ (∀ l, (x l).1 = 0) ∨ (∀ l, (x l).2 = 0) := by
  constructor
  · intro h
    push_neg at h
    obtain ⟨c, hc, hne⟩ := h
    by_cases h1 : c.1 = 0
    · right
      have h2 : c.2 ≠ 0 := fun h2 => hne (Prod.ext h1 h2)
      intro l
      have hl := congrArg Prod.snd (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.snd_mul, Pi.zero_apply, Prod.snd_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h2
    · left
      intro l
      have hl := congrArg Prod.fst (congrFun hc l)
      simp only [Pi.smul_apply, smul_eq_mul, Prod.fst_mul, Pi.zero_apply, Prod.fst_zero] at hl
      exact (mul_eq_zero.1 hl).resolve_left h1
  · rintro (h | h) hfree
    · have h1 := hfree (1, 0) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1
    · have h1 := hfree (0, 1) (by
        funext l
        refine Prod.ext ?_ ?_ <;> simp [h l])
      simp at h1
end PI.OmVe
