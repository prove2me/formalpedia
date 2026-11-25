-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.parahoricIdxZ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:15:24.989323+00:00
-- url     : https://prove2.me/submissions/2326c893-2949-4290-9de2-d604deb632c9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ParahoricIdxZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Theorems.Thm_PI_ParahoricIdxZ_W_qE_pos
import Theorems.Thm_PI_ParahoricIdxZ_W_card_gt_one
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lemmaUSplit
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_volII
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_volJadd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate Finset
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
namespace PI.ParahoricIdxZ.W
theorem _root_.solution (h3 : IdxStep) (h4 : CardStep) : PI.ParahoricIdxZ := by
  intro F _ _ _ _ _ _ _ O hO ϖ hϖ hϖ0 hloc hfin a t J' hKJ hJint hJc ρ hρ χ nrm lam hlam c hc hc1
    μ _ hμ ν₁ _ _ hν₁ ν₂ _ _ hν₂ J hJ
  intro q
  simp only [q]
  clear q
  have := hfin

  have hZ := Formalism.DoubleCosetMeasures.P.lemmaUSplit F a t O hO ϖ hϖ0 J' hJc (fun k hk => (hJint hk).1) ρ hρ χ nrm
    lam hlam c hc μ ν₁ ν₂
  rw [hZ, hμ, hc1]

  have hJv := Formalism.DoubleCosetMeasures.P.volJadd F O hO ϖ hϖ hϖ0 hloc hfin a ν₁ J' hKJ hJint
  rw [hν₁, mul_one] at hJv
  have hII := Formalism.DoubleCosetMeasures.P.volII F O hO ϖ hϖ hϖ0 hfin t a ν₂
  rw [hν₂] at hII
  have hJr := congrArg ENNReal.toReal hJv
  have hIIr := congrArg ENNReal.toReal hII
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_one] at hJr hIIr

  have hI := h3 F O ϖ hϖ hϖ0 hloc hfin a t J' hKJ hJint J hJ
  have hIr : ((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index : ℝ) *
      (Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') : ℝ) *
        (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) : ℝ) ^ (a * t) *
        (Nat.card (GL (Fin t) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : ℝ) =
      (Nat.card (GL (Fin (a + t)) (Formalism.DoubleCosetMeasures.kF O ϖ hϖ)) : ℝ) := by
    exact_mod_cast hI
  rw [h4 F O ϖ hϖ hϖ0 hloc hfin t, h4 F O ϖ hϖ hϖ0 hloc hfin (a + t)] at hIr
  have hq1 : (1 : ℝ) < (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) : ℝ) := by
    exact_mod_cast card_gt_one F O ϖ hϖ hloc
  set q : ℝ := (Nat.card (Formalism.DoubleCosetMeasures.kF O ϖ hϖ) : ℝ) with hqdef
  set idx : ℝ := ((J.subgroupOf (Formalism.DoubleCosetMeasures.GLint O (a + t))).index : ℝ) with hidx
  set N : ℝ := (Nat.card (J' ⧸ (Formalism.DoubleCosetMeasures.congSub O ϖ a).subgroupOf J') : ℝ) with hN
  have hq0 : q ≠ 0 := by positivity
  have hE1 := (qE_pos hq1 (a + t)).ne'
  have hE2 := (qE_pos hq1 t).ne'
  have hpow : q ^ ((a + t) * (a + t)) = q ^ (a * a) * q ^ (t * a) * q ^ (a * t) * q ^ (t * t) := by
    rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
  rw [hpow] at hIr
  have hqa : q ^ (a * a) ≠ 0 := pow_ne_zero _ hq0
  have hqta : q ^ (t * a) ≠ 0 := pow_ne_zero _ hq0
  have hqat : q ^ (a * t) ≠ 0 := pow_ne_zero _ hq0
  have hqtt : q ^ (t * t) ≠ 0 := pow_ne_zero _ hq0
  have hIr' : idx * N * qE q 1 t = q ^ (a * a) * q ^ (t * a) * qE q 1 (a + t) := by
    apply mul_right_cancel₀ (mul_ne_zero hqat hqtt)
    linear_combination hIr
  have h5 : idx * N = q ^ (a * a) * q ^ (t * a) * qE q 1 (a + t) * (qE q 1 t)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hE2]; exact hIr'
  have e1 : (ν₁ (Formalism.DoubleCosetMeasures.Jset J')).toReal = N / q ^ (a * a) := by
    rw [eq_div_iff hqa]; exact hJr
  have e2 : (ν₂ (Formalism.DoubleCosetMeasures.IIset O ϖ)).toReal = 1 / q ^ (t * a) := by
    rw [eq_div_iff hqta]; exact hIIr
  have key : idx * zetaProd q (a + t) *
      (ENNReal.toReal 1 * (ν₁ (Formalism.DoubleCosetMeasures.Jset J')).toReal * (ν₂ (Formalism.DoubleCosetMeasures.IIset O ϖ)).toReal) =
        zetaProd q t := by
    unfold zetaProd
    rw [e1, e2, ENNReal.toReal_one]
    calc idx * (qE q 1 (a + t))⁻¹ * (1 * (N / q ^ (a * a)) * (1 / q ^ (t * a)))
        = (idx * N) * ((qE q 1 (a + t))⁻¹ * (q ^ (a * a))⁻¹ * (q ^ (t * a))⁻¹) := by ring
      _ = (qE q 1 t)⁻¹ := by rw [h5]; field_simp
  have key' := congrArg (fun x : ℝ => (x : ℂ)) key
  rw [← key']
  push_cast
  rw [map_one, mul_one, hidx, Complex.ofReal_natCast]
end PI.ParahoricIdxZ.W
