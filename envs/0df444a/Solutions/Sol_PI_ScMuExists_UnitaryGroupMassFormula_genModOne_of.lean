-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.genModOne_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:04.067361+00:00
-- url     : https://prove2.me/submissions/6592025d-ab5e-4df5-8a1c-ca5076de2297

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ModOne
import Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_conj_eq_smul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Pointwise
noncomputable section
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution (hHaar : GenHaarSub) : GenModOne := by
  intro G _ _ _ _ _ _ _ _ N H hN hnorm hdec h hh
  obtain ⟨_, _, _, _, hfin, hpos⟩ := hHaar G N hN
  have hm : ∀ a : G, Measurable (fun x : G => a * x * a⁻¹) := fun a =>
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hcomp : ∀ a b : G, (fun x : G => a * b * x * (a * b)⁻¹) =
      (fun x : G => a * x * a⁻¹) ∘ (fun x : G => b * x * b⁻¹) := fun a b => by
    funext x
    simp only [Function.comp, mul_inv_rev, mul_assoc]
  have hmap : ∀ a b : G, (haarSub N hN).map (fun x => a * b * x * (a * b)⁻¹) =
      ((haarSub N hN).map (fun x => b * x * b⁻¹)).map (fun x => a * x * a⁻¹) := fun a b => by
    rw [Measure.map_map (hm a) (hm b), hcomp]
  have hid : ∀ a : G, (haarSub N hN).map (fun x => a * a⁻¹ * x * (a * a⁻¹)⁻¹) = haarSub N hN :=
    fun a => by
      simp only [mul_inv_cancel, one_mul, inv_one, mul_one]
      exact Measure.map_id'
  have hsc : ∀ g ∈ H, ∃ c : ℝ≥0, (haarSub N hN).map (fun x => g * x * g⁻¹) = c • haarSub N hN :=
    fun g hg => conj_eq_smul N hN g (hnorm g hg) (fun x hx => by
      simpa using hnorm g⁻¹ (H.inv_mem hg) x hx)
  obtain ⟨k, hk, p, hp, σ, hσ, hkp, hσp, C, hC, hC1, hCk⟩ := hdec h hh
  have hCpos : 0 < haarSub N hN C :=
    lt_of_lt_of_le (hpos _ isOpen_interior hC1) (measure_mono interior_subset)
  have hCfin : haarSub N hN C < ⊤ := hfin C hC
  have key : ∀ a b : ℝ≥0∞, a * haarSub N hN C = b * haarSub N hN C → a = b := fun a b hab => by
    first
      | exact (ENNReal.mul_left_inj hCpos.ne' hCfin.ne).mp hab
      | exact (ENNReal.mul_eq_mul_right hCpos.ne' hCfin.ne).mp hab
      | (rw [mul_comm a, mul_comm b] at hab; exact (ENNReal.mul_right_inj hCpos.ne' hCfin.ne).mp hab)
      | (rw [mul_comm a, mul_comm b] at hab; exact (ENNReal.mul_eq_mul_left hCpos.ne' hCfin.ne).mp hab)
  have cancel : ∀ c d : ℝ≥0, c • haarSub N hN = d • haarSub N hN → c = d := fun c d hcd => by
    have e := congrArg (fun μ : Measure G => μ C) hcd
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e
    exact_mod_cast key _ _ e
  have hk1 : (haarSub N hN).map (fun x => k * x * k⁻¹) = haarSub N hN := by
    obtain ⟨ck, hck⟩ := hsc k hk
    have hpre : (fun x : G => k * x * k⁻¹) ⁻¹' C = C := Set.ext fun x => hCk x
    have e1 : (haarSub N hN).map (fun x => k * x * k⁻¹) C = haarSub N hN C := by
      rw [Measure.map_apply (hm k) hC.measurableSet, hpre]
    rw [hck] at e1
    have e3 : (ck : ℝ≥0∞) * haarSub N hN C = 1 * haarSub N hN C := by
      simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at e1
      rw [one_mul]
      exact e1
    have hck1 : ck = 1 := by exact_mod_cast key _ _ e3
    rw [hck, hck1, one_smul]
  have hp1 : (haarSub N hN).map (fun x => p * x * p⁻¹) = haarSub N hN := by
    obtain ⟨cp, hcp⟩ := hsc p hp
    obtain ⟨cs, hcs⟩ := hsc σ hσ
    obtain ⟨cs', hcs'⟩ := hsc σ⁻¹ (H.inv_mem hσ)
    have e1 : (cs' * cs) • haarSub N hN = (1 : ℝ≥0) • haarSub N hN := by
      have e := hid σ
      rw [hmap, hcs', Measure.map_smul, hcs, smul_smul] at e
      rw [e, one_smul]
    have hss : cs' * cs = 1 := cancel _ _ e1
    have hpinv : (fun x : G => p⁻¹ * x * p⁻¹⁻¹) =
        (fun x : G => σ * p * σ⁻¹ * x * (σ * p * σ⁻¹)⁻¹) := by
      rw [hσp]
    have e2 : (haarSub N hN).map (fun x => p⁻¹ * x * p⁻¹⁻¹) = (cs' * cp * cs) • haarSub N hN := by
      rw [hpinv, hmap (σ * p) σ⁻¹, hcs', Measure.map_smul, hmap σ p, hcp, Measure.map_smul, hcs,
        smul_smul, smul_smul]
    have e3 : (cs' * cp * cs * cp) • haarSub N hN = (1 : ℝ≥0) • haarSub N hN := by
      have e := hid p
      rw [hmap p p⁻¹, e2, Measure.map_smul, hcp, smul_smul] at e
      rw [e, one_smul]
    have hcp1 : cp = 1 := by
      have h4 := cancel _ _ e3
      have h5 : cp * cp = 1 := by
        calc cp * cp = (cs' * cs) * (cp * cp) := by rw [hss, one_mul]
          _ = cs' * cp * cs * cp := by ring
          _ = 1 := h4
      have h6 : (cp : ℝ) * cp = 1 := by exact_mod_cast h5
      have h7 : (cp : ℝ) = 1 := by nlinarith [cp.2]
      exact_mod_cast h7
    rw [hcp, hcp1, one_smul]
  rw [hkp, hmap, hp1, hk1]
end PI.ScMuExists.UnitaryGroupMassFormula
