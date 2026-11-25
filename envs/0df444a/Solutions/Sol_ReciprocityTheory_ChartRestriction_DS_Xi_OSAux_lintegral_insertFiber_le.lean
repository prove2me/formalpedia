-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.OSAux.lintegral_insertFiber_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:58:32.69331+00:00
-- url     : https://prove2.me/submissions/7c345812-dbf8-49a9-a4a2-27bdc11a615c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_RhoSqInsSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LintegralInsertFiberLe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_ge_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_Lsq_ins
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_bco_ins_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_de_ge_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_OSAux_de_ins_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ReciprocityTheory.ChartRestriction.DS.Xi
namespace OSAux
private lemma rpow_sq_half {a : ℝ} (ha : 0 ≤ a) (r : ℝ) : a ^ r = (a ^ 2) ^ (r / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  push_cast
  ring
private lemma nnorm_ae (γ : ℝ) (f : ℂ → ℝ≥0∞) :
    ∫⁻ z : ℂ, f z * (‖z‖₊ : ℝ≥0∞) ^ (-γ) = ∫⁻ z : ℂ, f z * ENNReal.ofReal (‖z‖ ^ (-γ)) := by
  apply lintegral_congr_ae
  have h0 : ∀ᵐ z : ℂ, z ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))
  filter_upwards [h0] with z hz
  congr 1
  rw [← ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hz)]
  congr 1
  rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
private lemma core {e0 γ C : ℝ}
    (hC : ∀ (c : ℂ) (D : ℝ), 0 < D →
      (∫⁻ x : ℂ, ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e0 / 2)) *
        ENNReal.ofReal (‖x‖ ^ (-γ))) ≤ ENNReal.ofReal (C * (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e0) / 2)))
    {L d1 d0 : ℝ} (c : ℂ) (f : ℂ → ℝ) (hL : 0 < L) (hd1 : 0 < d1) (hd0 : 0 ≤ d0)
    (h0 : d0 ^ 2 = L * ‖c‖ ^ 2 + d1 ^ 2 / L) (hf0 : ∀ z, 0 ≤ f z)
    (hf : ∀ z, f z ^ 2 = L * ‖z - c‖ ^ 2 + d1 ^ 2 / L) :
    ∫⁻ z : ℂ, ENNReal.ofReal (f z ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ)) ≤
      ENNReal.ofReal (max C 1 * L ^ (-1 + γ / 2) * d0 ^ (-(γ - e0))) := by
  have hD : 0 < d1 / L := div_pos hd1 hL
  have hsq : ∀ t : ℝ, L * t + d1 ^ 2 / L = L * (t + (d1 / L) ^ 2) := by
    intro t
    have := hL.ne'
    field_simp
  have he : -(2 - e0) / 2 = -1 + e0 / 2 := by ring
  have hpt : ∀ z, f z ^ (-(2 - e0)) =
      L ^ (-1 + e0 / 2) * (‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2) := by
    intro z
    rw [rpow_sq_half (hf0 z), hf z, hsq, he, Real.mul_rpow hL.le (by positivity)]
  have hX : ‖c‖ ^ 2 + (d1 / L) ^ 2 = d0 ^ 2 / L := by
    rw [h0, hsq]; field_simp
  have hLp : L ^ (-1 + γ / 2) = L ^ (-1 + e0 / 2) / L ^ (-(γ - e0) / 2) := by
    rw [← Real.rpow_sub hL]; congr 1; ring
  have hd0p : (d0 ^ 2) ^ (-(γ - e0) / 2) = d0 ^ (-(γ - e0)) := (rpow_sq_half hd0 _).symm
  calc ∫⁻ z : ℂ, ENNReal.ofReal (f z ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ))
      = ∫⁻ z : ℂ, ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          (ENNReal.ofReal ((‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2)) *
            ENNReal.ofReal (‖z‖ ^ (-γ))) := by
        refine lintegral_congr (fun z => ?_)
        rw [hpt z, ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _), mul_assoc]
    _ = ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ∫⁻ z : ℂ, ENNReal.ofReal ((‖z - c‖ ^ 2 + (d1 / L) ^ 2) ^ (-1 + e0 / 2)) *
            ENNReal.ofReal (‖z‖ ^ (-γ)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ENNReal.ofReal (C * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2)) := by
        gcongr
        exact hC c _ hD
    _ ≤ ENNReal.ofReal (L ^ (-1 + e0 / 2)) *
          ENNReal.ofReal (max C 1 * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2)) := by
        gcongr
        exact le_max_left _ _
    _ = ENNReal.ofReal (L ^ (-1 + e0 / 2) *
          (max C 1 * (‖c‖ ^ 2 + (d1 / L) ^ 2) ^ (-(γ - e0) / 2))) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)).symm
    _ = ENNReal.ofReal (max C 1 * L ^ (-1 + γ / 2) * d0 ^ (-(γ - e0))) := by
        congr 1
        rw [hX, Real.div_rpow (sq_nonneg _) hL.le, hd0p, hLp]
        ring
end OSAux
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
namespace ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
theorem _root_.solution (hC1 : C1) (hK : KER) {e0 γ : ℝ} (he0 : 0 < e0) (hγ : e0 < γ) (hγ2 : γ < 2) :
    ∃ CK : ℝ, 0 < CK ∧ ∀ {p m : ℕ} (y : Yp p m),
      ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * (‖z‖₊ : ℝ≥0∞) ^ (-γ) ≤
        ENNReal.ofReal (CK * Lsq (tailPt y) 1 ^ (-1 + γ / 2) * de (tailPt y) 0 ^ (-(γ - e0))) := by
  obtain ⟨C, hC⟩ := hK e0 γ he0 hγ hγ2
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro p m y
  have hf : ∀ z : ℂ, de (ins y z) 0 ^ 2 =
      Lsq (tailPt y) 1 * ‖z - y.1 0 * bco (tailPt y) 1 / (Lsq (tailPt y) 1 : ℂ)‖ ^ 2 +
        de (tailPt y) 1 ^ 2 / Lsq (tailPt y) 1 := by
    intro z
    have hb : bco (ins y z) 1 = bco (tailPt y) 1 := by simpa using bco_ins_succ y z 0
    have hd : de (ins y z) 1 = de (tailPt y) 1 := by simpa using de_ins_succ y z 0
    have h := hC1 p m (ins y z)
    rw [hb, hd, Lsq_ins] at h
    simp only [ins, Fin.cons_zero] at h
    exact h
  have h0 : de (tailPt y) 0 ^ 2 =
      Lsq (tailPt y) 1 * ‖y.1 0 * bco (tailPt y) 1 / (Lsq (tailPt y) 1 : ℂ)‖ ^ 2 +
        de (tailPt y) 1 ^ 2 / Lsq (tailPt y) 1 := by
    have := hf 0
    rw [zero_sub, norm_neg] at this
    exact this
  calc _ = ∫⁻ z : ℂ, ENNReal.ofReal (de (ins y z) 0 ^ (-(2 - e0))) * ENNReal.ofReal (‖z‖ ^ (-γ)) :=
        nnorm_ae γ _
    _ ≤ _ := core hC _ (fun z => de (ins y z) 0) (lt_of_lt_of_le one_pos (Lsq_ge_one _ _))
        (lt_of_lt_of_le one_pos (de_ge_one _ _)) (le_trans zero_le_one (de_ge_one _ _)) h0
        (fun z => le_trans zero_le_one (de_ge_one _ _)) hf
end ReciprocityTheory.ChartRestriction.DS.Xi.OSAux
