-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.rep_zT_sat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:35:08.557207+00:00
-- url     : https://prove2.me/submissions/3bca092f-ce56-4c5b-939e-2dc1d0ee40f8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepHSelfInt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepExact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepSingleSat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_single_sat
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_add
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_of_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_rep_sat_sub


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
  (m : Type) [Fintype m] [DecidableEq m]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (hOK : CmOK a b c d) (Λ : AddSubgroup (m → ℂ))
    (hΛ : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λ) (hθ : ∀ z ∈ Λ, cmTheta b d • z ∈ Λ)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (T : Finset m)
    (hT : ∀ j ∈ T, SatMem l Λ (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d)))) {z : m → ℂ} (hz : z ∈ Λ) :
    SatMem l Λ (zT T z) := by
  have hsum : SatMem l Λ (∑ j ∈ T, Pi.single j (z j)) :=
    Finset.sum_induction _ (SatMem l Λ) (fun _ _ h1 h2 => rep_sat_add (l := l) (Λ := Λ) hl h1 h2) (rep_sat_zero l Λ hl)
      (fun j hj => rep_single_sat a b c d ha hd lam hlam m hOK Λ hΛ hθ hl x y hQ j (hT j hj) hz)
  have e : zT T z = z - ∑ j ∈ T, Pi.single j (z j) := by
    funext i
    simp only [zT, Pi.sub_apply, Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  rw [e]
  exact rep_sat_sub (l := l) (Λ := Λ) hl (rep_sat_of_mem (l := l) (Λ := Λ) hz hl) hsum
end PI.UnitaryGroupMassFormula.UnimodLocStd
