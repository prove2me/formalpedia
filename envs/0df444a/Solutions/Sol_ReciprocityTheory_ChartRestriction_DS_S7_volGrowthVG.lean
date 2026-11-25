-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.volGrowthVG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:51:06.734538+00:00
-- url     : https://prove2.me/submissions/38d9fd4a-acfc-4c55-96cd-a0cca746d530

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_O_bddRV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_RLV_det
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_ballFiniteVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_continuous_toM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_entryRV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_cont
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hs_contVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_of_RLV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_smallRV
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toM_mulVG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toM_mul_invVG


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) (ν : Measure (UJ ε)) [ν.IsHaarMeasure] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ν {g | hs (toM g) ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * (n * Fintype.card (SgIxV ε s)))) := by
  classical
  let Q := SgIxV ε s
  let lam : Measure (REV n Q) := Measure.addHaar
  let O : Set (REV n Q) := {x | hsRV (Matrix.of x - signedIdentityColumns ε s) < 1 / 16}
  let r0 : ℝ := n + 2 * (5 / 2 * Real.sqrt n + 1 / 2) ^ 2
  let W : Set (UJ ε) := {k | hs (toM k) ≤ r0}
  let N : ℕ := 2 * (n * Fintype.card Q)
  have hof : Continuous (fun x : REV n Q => (Matrix.of x : Matrix (Fin n) Q ℂ)) := continuous_id
  have hofs : Continuous (fun x : Matrix (Fin n) Q ℂ => (Matrix.of.symm x : REV n Q)) := continuous_id
  have hO_open : IsOpen O :=
    isOpen_lt (hsRV_cont.comp (hof.sub continuous_const)) continuous_const
  have hO_pos : 0 < lam O := hO_open.measure_pos lam ⟨Matrix.of.symm (signedIdentityColumns ε s), by simp [O, hsRV]⟩
  have hO_fin : lam O < ⊤ :=
    (measure_mono (fun x hx => O_bddRV hx)).trans_lt measure_closedBall_lt_top
  have hW_fin : ν W < ⊤ := ballFiniteVG ε ν r0
  have hB_fin : lam (ball 0 1) < ⊤ := measure_ball_lt_top
  set K : ENNReal := ν W * lam (ball 0 1) / lam O with hK
  have hK_fin : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top hW_fin.ne hB_fin.ne) hO_pos.ne'
  refine ⟨K.toReal * (Real.sqrt n + 1) ^ N, by positivity, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  set ρ : ℝ := R * (Real.sqrt n + 1) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set S : Set (UJ ε) := {g | hs (toM g) ≤ R ^ 2} with hS
  have hS_meas : MeasurableSet S :=
    (isClosed_le (hs_contVG.comp (continuous_toM ε)) continuous_const).measurableSet
  let Φ : UJ ε × REV n Q → REV n Q := fun p => RLV (toM p.1⁻¹) p.2
  have hΦ : Continuous Φ := by
    show Continuous fun p : UJ ε × REV n Q =>
      (Matrix.of.symm (toM p.1⁻¹ * Matrix.of p.2) : REV n Q)
    exact hofs.comp (((continuous_toM ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd))
  let T : Set (UJ ε × REV n Q) := {p | hs (toM p.1) ≤ R ^ 2} ∩ Φ ⁻¹' O
  have hT : MeasurableSet T :=
    (isClosed_le ((hs_contVG.comp (continuous_toM ε)).comp continuous_fst)
      continuous_const).measurableSet.inter (hO_open.preimage hΦ).measurableSet
  have h1 : (ν.prod lam) T = ν S * lam O := by
    rw [Measure.prod_apply hT]
    have : ∀ g, lam (Prod.mk g ⁻¹' T) = S.indicator (fun _ => lam O) g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hdet : LinearMap.det (RLV (Q := Q) (toM g⁻¹)) = 1 := RLV_det (g⁻¹).2
        have e : Prod.mk g ⁻¹' T = RLV (Q := Q) (toM g⁻¹) ⁻¹' O := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Φ]
          exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
        rw [e, Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
        simp
      · rw [Set.indicator_of_notMem hg]
        have e : Prod.mk g ⁻¹' T = ∅ := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [e, measure_empty]
    simp_rw [this]
    rw [lintegral_indicator_const hS_meas, mul_comm]
  have h2 : (ν.prod lam) T ≤ ν W * lam (closedBall 0 ρ) := by
    rw [Measure.prod_apply_symm hT]
    calc ∫⁻ x, ν ((fun g => (g, x)) ⁻¹' T) ∂lam
        ≤ ∫⁻ x, (closedBall (0 : REV n Q) ρ).indicator (fun _ => ν W) x ∂lam := by
          refine lintegral_mono fun x => ?_
          by_cases hne : ((fun g => (g, x)) ⁻¹' T).Nonempty
          · obtain ⟨h, hh⟩ := hne
            have hh1 : hs (toM h) ≤ R ^ 2 := hh.1
            have hh2 : hsRV (Matrix.of (RLV (toM h⁻¹) x) - signedIdentityColumns ε s) < 1 / 16 := hh.2
            rw [of_RLV] at hh2
            have hx : x ∈ closedBall (0 : REV n Q) ρ := by
              rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0]
              intro i
              rw [pi_norm_le_iff_of_nonneg hρ0]
              intro j
              have := entryRV (g := toM h) hR0 hh1 hh2 i j
              rw [← Matrix.mul_assoc, toM_mul_invVG, Matrix.one_mul] at this
              exact this
            rw [Set.indicator_of_mem hx]
            calc ν ((fun g => (g, x)) ⁻¹' T) ≤ ν ((fun g => h⁻¹ * g) ⁻¹' W) := by
                  refine measure_mono fun g hg => ?_
                  have hg2 : hsRV (Matrix.of (RLV (toM g⁻¹) x) - signedIdentityColumns ε s) < 1 / 16 := hg.2
                  rw [of_RLV] at hg2
                  show hs (toM (h⁻¹ * g)) ≤ r0
                  refine smallRV (h⁻¹ * g).2 hg2 hh2 ?_
                  rw [toM_mulVG, ← Matrix.mul_assoc, Matrix.mul_assoc (toM h⁻¹),
                    toM_mul_invVG, Matrix.mul_one]
              _ = ν W := measure_preimage_mul ν h⁻¹ W
          · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
            exact bot_le
      _ = ν W * lam (closedBall 0 ρ) := lintegral_indicator_const measurableSet_closedBall _
  have hfr : Module.finrank ℝ (REV n Q) = N := by
    simp [REV, N, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have h3 : lam (closedBall 0 ρ) = ENNReal.ofReal (ρ ^ N) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hρ0, hfr]
  have h4 : ν S * lam O ≤ K * ENNReal.ofReal (ρ ^ N) * lam O := by
    rw [← h1]
    refine h2.trans (le_of_eq ?_)
    rw [h3, hK, div_eq_mul_inv]
    have : (lam O)⁻¹ * lam O = 1 := ENNReal.inv_mul_cancel hO_pos.ne' hO_fin.ne
    calc ν W * (ENNReal.ofReal (ρ ^ N) * lam (ball 0 1))
        = ν W * (ENNReal.ofReal (ρ ^ N) * lam (ball 0 1)) * ((lam O)⁻¹ * lam O) := by
          rw [this, mul_one]
      _ = _ := by ring
  have h5 : ν S ≤ K * ENNReal.ofReal (ρ ^ N) :=
    (ENNReal.mul_le_mul_iff_left hO_pos.ne' hO_fin.ne).1 h4
  refine h5.trans (le_of_eq ?_)
  rw [hρ, mul_pow, ← ENNReal.ofReal_toReal hK_fin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 1
  ring
end ReciprocityTheory.ChartRestriction.DS.S7
