-- Prove2me | solution 1 for PI.TwistedEisensteinNonvanishing.W.qt_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:13:23.140296+00:00
-- url     : https://prove2.me/submissions/9898347d-5fdf-4fb3-ba7f-9be889c38b48

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_WeightedSumToGaussSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TwistedEisensteinCoset_ChangeVariablesDeterminantOne
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_id
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_comp
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_congr
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_qt_em
import Theorems.Thm_PI_TwistedEisensteinNonvanishing_W_vq_prod


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
theorem _root_.solution (D : ι → E) (hD : ∀ i, D i ≠ 0) :
    QT P (fun v => diagonal D *ᵥ v) ((qOf P : K) ^ vq P (diagonal D).det) := by
  classical
  have key : ∀ s : Finset ι, QT P (fun v : ι → E => fun k => if k ∈ s then D k * v k else v k)
      ((qOf P : K) ^ (∑ k ∈ s, vq P (D k))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact qt_congr qt_id (fun v => by funext k; simp) (by simp)
    | insert a s ha ih =>
      refine qt_congr (qt_comp (qt_em hN hp hq hK a a (hD a) 0 0 (Or.inr rfl)) ih) (fun v => ?_) ?_
      · funext k
        by_cases hk : k = a
        · subst hk
          simp [em, ha]
        · simp [em, hk, Function.update_apply]
      · rw [Finset.sum_insert ha, zpow_add₀ hK, mul_comm]
  refine qt_congr (key Finset.univ) (fun v => by funext k; simp [Matrix.mulVec_diagonal]) ?_
  rw [Matrix.det_diagonal, vq_prod (s := Finset.univ) (f := D) (hf := fun i _ => hD i)]
  all_goals assumption
end PI.TwistedEisensteinNonvanishing.W
