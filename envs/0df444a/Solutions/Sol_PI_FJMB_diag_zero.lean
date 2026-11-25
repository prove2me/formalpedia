-- Prove2me | solution 1 for PI.FJMB.diag_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:14:30.887412+00:00
-- url     : https://prove2.me/submissions/87a53415-3db5-478e-b754-0e52d4f5ac63

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurDiag
import Theorems.Thm_PI_FJMB_elim_step
import Theorems.Thm_PI_FJMB_aeval_killS_empty
import Theorems.Thm_PI_FJMB_aeval_killS_union
import Theorems.Thm_PI_FJMB_hwb_restrict
import Theorems.Thm_PI_FJMB_offD_step


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Classical
open PI PI.FJMB
variable {σ : Type*}
namespace PI.FJMB
theorem _root_.solution : ∀ (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι → ∀ f : MvPolynomial σ ℂ,
    HWB ι f → aeval (killS (offD ι)) f = 0 → f = 0 := by
  intro m
  induction m with
  | zero =>
    intro n ι _ f _ hg
    have hempty : offD ι = ∅ := by
      ext v
      simp only [offD, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨i, _, _, _⟩
      exact Fin.elim0 i
    rw [hempty, aeval_killS_empty] at hg
    exact hg
  | succ m ih =>
    intro n
    cases n with
    | zero =>
      intro ι _ f _ hg
      have hempty : offD ι = ∅ := by
        ext v
        simp only [offD, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, k, _, _⟩
        exact Fin.elim0 k
      rw [hempty, aeval_killS_empty] at hg
      exact hg
    | succ n =>
      intro ι hι f hf hg
      have hinj : Function.Injective (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) := by
        intro x y hxy
        have h := hι hxy
        simp only [Prod.mk.injEq, Fin.succ_inj] at h
        exact Prod.ext h.1 h.2
      apply elim_step ι hι f hf
      apply ih n (fun x : Fin m × Fin n => ι (x.1.succ, x.2.succ)) hinj _ (hwb_restrict ι hι f hf)
      rw [aeval_killS_union, offD_step ι hι]
      exact hg
end PI.FJMB
