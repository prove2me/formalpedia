-- Prove2me | solution 1 for PI.FglTriFactor.Wk.pr_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:25.746297+00:00
-- url     : https://prove2.me/submissions/3a21bbce-4a07-4383-8e26-f04abc7d8f59

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_SubstUpdateVarTwoLiftedThirdRoot
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglTriFactor.Wk
theorem _root_.solution (g : MvPowerSeries (Fin 2) ℂ_[p]) (hg : MvPowerSeries.constantCoeff g = 0) :
    pr (0 : MvPowerSeries (Fin 3) ℂ_[p]) 0 g = 0 := by
  unfold pr
  ext e
  have hz : ∀ i, MvPowerSeries.constantCoeff (![(0 : MvPowerSeries (Fin 3) ℂ_[p]), 0] i) = 0 := fun i => by
    fin_cases i <;> simp
  have ha : MvPowerSeries.HasSubst ![(0 : MvPowerSeries (Fin 3) ℂ_[p]), 0] := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero hz
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by rw [hz i]; exact IsNilpotent.zero)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero hz
  rw [MvPowerSeries.coeff_subst ha, finsum_eq_single _ 0]
  · simp [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg]
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hs
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)]
    · simp
    · fin_cases s <;> simp <;> exact hs
end PI.FglTriFactor.Wk
