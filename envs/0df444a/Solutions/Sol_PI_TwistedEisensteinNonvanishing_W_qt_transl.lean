-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_transl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:09:36.220691+00:00
-- url     : https://prove2.me/submissions/e2aa94c5-e177-4c0b-9709-7c0430585867

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_id
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_comp
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_congr
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_em
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Module
noncomputable section
open PI PI.TwistedEisensteinNonvanishing PI.TwistedEisensteinNonvanishing.W
open Loc LocE Function Matrix
variable {E K : Type} [Field E] [NumberField E] [Field K]
variable {P : HeightOneSpectrum (𝓞 E)} (hN : NTAll) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (hq : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hK : ((qOf P : ℕ) : K) ≠ 0)
include hN hp hq hK
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace PI.TwistedEisensteinNonvanishing.W
theorem _root_.solution (τ : ι → E) : QT P (fun v : ι → E => v + τ) (1 : K) := by
  classical
  have key : ∀ s : Finset ι, QT P (fun v : ι → E => fun k => if k ∈ s then v k + τ k else v k) (1 : K) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact qt_congr qt_id (fun v => by funext k; simp) rfl
    | insert a s ha ih =>
      refine qt_congr (qt_comp (qt_em hN hp hq hK a a one_ne_zero 0 (τ a) (Or.inr rfl)) ih) (fun v => ?_) ?_
      · funext k
        by_cases hk : k = a
        · subst hk
          simp [em, ha]
        · simp [em, hk, Function.update_apply]
      · rw [vq_one, zpow_zero, one_mul]
        all_goals assumption
  exact qt_congr (key Finset.univ) (fun v => by funext k; simp) rfl
end PI.TwistedEisensteinNonvanishing.W
