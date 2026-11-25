-- Prove2me | solution 1 for PI.WGL.LTA.exp_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:30.93867+00:00
-- url     : https://prove2.me/submissions/5ef3ce25-9075-43d1-8e48-2f617f2fbf40

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftDefs
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LRowdivLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleA
import Theorems.Thm_PI_WGL_LTA_rowGen_gmin
import Theorems.Thm_PI_WGL_LTA_sum_finset_castSucc
import Theorems.Thm_PI_WGL_LTA_liftR_castSucc
import Theorems.Thm_PI_WGL_LTA_liftR_last
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTA
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial
namespace PI.WGL.LTA
theorem _root_.solution {r c n m : ℕ} (e : Fin n → Fin r) (he : Function.Injective e) (z : Fin r)
    (hz : ∀ b, e b ≠ z) (κ : Fin (m + 1) → Fin c) :
    Exp e (fun ρ : Fin m → Fin n => gmin (liftR e z ρ) κ) := by
  intro a b ρ
  beta_reduce
  rw [rowGen_gmin, sum_finset_castSucc]
  · refine Finset.sum_congr rfl fun S _ => ?_
    beta_reduce
    have h1 : (∀ p ∈ S.map Fin.castSuccEmb, liftR e z ρ p = e b) ↔ (∀ p ∈ S, ρ p = b) := by
      simp [liftR_castSucc, he.eq_iff]
    have h2 : upd (liftR e z ρ) (S.map Fin.castSuccEmb) (e a) = liftR e z (upd ρ S a) := by
      funext p
      induction p using Fin.lastCases with
      | last =>
        have hl : Fin.last m ∉ S.map Fin.castSuccEmb := by
          simp only [Finset.mem_map, Fin.coe_castSuccEmb, not_exists, not_and]
          intro q _ hq
          exact (Fin.castSucc_lt_last q).ne hq
        simp [upd, hl, liftR_last]
      | cast q =>
        have hm : Fin.castSucc q ∈ S.map Fin.castSuccEmb ↔ q ∈ S := Finset.mem_map' Fin.castSuccEmb
        simp only [upd, liftR_castSucc, hm]
        split_ifs <;> rfl
    by_cases hc : ∀ p ∈ S, ρ p = b
    · rw [if_pos (h1.mpr hc), if_pos hc, h2, Finset.card_map]
    · rw [if_neg (fun h => hc (h1.mp h)), if_neg hc]
  · intro S hS
    beta_reduce
    rw [if_neg]
    intro hall
    exact hz b ((liftR_last e z ρ).symm.trans (hall _ hS)).symm
end PI.WGL.LTA
