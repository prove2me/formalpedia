-- Prove2me | solution 1 for PI.BeDiagZp.IdentW.ident_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:53:12.875305+00:00
-- url     : https://prove2.me/submissions/9858d5db-5c72-447a-a309-a06af682e4a1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_SubstOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalPadicSubstitution_CoeffOneLNeZero
import Theorems.Thm_PI_BeDiagZp_IdentW_constantCoeff_l
import Theorems.Thm_PI_BeDiagZp_IdentW_l_ex_apply
import Theorems.Thm_PI_BeDiagZp_IdentW_ex_l_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.BeDiagZp PI.BeDiagZp.IdentW
variable {p : ℕ} [Fact p.Prime]
namespace PI.BeDiagZp.IdentW
theorem _root_.solution : Ident := by
  intro p _ l ex hex0 h
  have hl0 := constantCoeff_l hex0 h
  refine ⟨hl0, fun σ a b ha hb => ?_⟩
  have hla : MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero ha l hl0
  have hlb : MvPowerSeries.constantCoeff (PowerSeries.subst b l) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hb l hl0
  have hCa : ∀ c : ℂ_[p], MvPowerSeries.constantCoeff (MvPowerSeries.C c * PowerSeries.subst a l) = 0 :=
    fun c => by rw [map_mul, hla, mul_zero]
  have lmul : ∀ c : ℂ_[p], PowerSeries.subst (mulBy l ex c a) l = MvPowerSeries.C c * PowerSeries.subst a l :=
    fun c => l_ex_apply hex0 h _ (hCa c)
  refine ⟨PowerSeries.constantCoeff_subst_eq_zero (by rw [map_add, hla, hlb, add_zero]) ex hex0,
    fun c => PowerSeries.constantCoeff_subst_eq_zero (hCa c) ex hex0, ?_, ?_, fun c d => ?_, fun c => ?_, ?_, ?_⟩
  · unfold add; rw [add_comm]
  · unfold add mulBy; rw [map_ofNat, two_mul]
  · unfold add; rw [lmul, lmul, ← add_mul, ← map_add]; rfl
  · unfold add; rw [lmul]; unfold mulBy; rw [map_add, map_one, add_mul, one_mul]
  · unfold mulBy; rw [map_one, one_mul]; exact ex_l_apply hex0 h a ha
  · unfold mulBy; rw [map_zero, zero_mul]; exact PowerSeries.subst_zero_of_constantCoeff_zero hex0
end PI.BeDiagZp.IdentW
