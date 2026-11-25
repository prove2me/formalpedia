-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.lang_semilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:09.119514+00:00
-- url     : https://prove2.me/submissions/0ea1fa27-a6bb-46bb-b233-bd7a5a4db2a7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_KurDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_SemilinNormPowSubPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_semilin_norm_add_of_lt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_semilin_norm_sub_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_FrobField_norm_sq_sub_pow_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_semilin_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
open Formalism.L2.Th1.CM
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]
open Filter Topology
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {l : ℕ} {σ : K →+* K} (h : FrobField K l σ) (hR : ResClosed K l)
    (c : K) (hc : ‖c‖ = 1) : ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * σ (σ ε) := by
  have hl2 : 2 ≤ l := h.prime.two_le
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc]; norm_num)
  have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc0
  have hci : ‖c⁻¹‖ = 1 := by rw [norm_inv, hc, inv_one]
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.mpr h.prime.ne_zero
  have hl1 := h.norm_l
  have hq4 : 4 ≤ l ^ 2 := by nlinarith

  let P : ℕ → K → Prop := fun n ε => ‖ε‖ = 1 ∧ ‖ε - c * σ (σ ε)‖ ≤ ‖(l : K)‖ ^ (n + 1)
  have h0 : ∃ ε, P 0 ε := by
    obtain ⟨x, hx, hev⟩ := semilin_root hR (m := l ^ 2 - 1) (by omega) 0 (-c⁻¹) (by simp)
      (by rw [norm_neg, hci])
    rw [zero_mul, add_zero, ← sub_eq_add_neg] at hev
    have hx1 : ‖x‖ = 1 := by
      have h1 : ‖x ^ (l ^ 2 - 1)‖ = 1 := by
        have e : x ^ (l ^ 2 - 1) = c⁻¹ + (x ^ (l ^ 2 - 1) - c⁻¹) := by ring
        rw [e, semilin_norm_add_of_lt (by rw [hci]; exact hev.trans_lt hl1), hci]
      rw [norm_pow] at h1
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).mp h1
    refine ⟨x, hx1, ?_⟩
    have hxq : x ^ (l ^ 2) = x * x ^ (l ^ 2 - 1) := by
      rw [← pow_succ']; congr 1; omega
    have e : x - c * σ (σ x) = -(c * x) * (x ^ (l ^ 2 - 1) - c⁻¹) - c * (σ (σ x) - x ^ (l ^ 2)) := by
      rw [hxq]
      linear_combination (-x) * hcc
    rw [e, zero_add, pow_one]
    refine semilin_norm_sub_le ?_ ?_
    · rw [norm_mul, norm_neg, norm_mul, hc, hx1, one_mul, one_mul]; exact hev
    · rw [norm_mul, hc, one_mul]; exact h.norm_sq_sub_pow_le x hx
  have hstep : ∀ n ε, P n ε → ∃ ε', P (n + 1) ε' ∧ ‖ε' - ε‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
    rintro n ε ⟨hε1, hε2⟩
    have hlam0 : (l : K) ^ (n + 1) ≠ 0 := pow_ne_zero _ hl0
    have hnl : ‖(l : K) ^ (n + 1)‖ = ‖(l : K)‖ ^ (n + 1) := norm_pow _ _
    have hsm : ‖(l : K)‖ ^ (n + 1) < 1 := pow_lt_one₀ (norm_nonneg _) hl1 (Nat.succ_ne_zero n)
    obtain ⟨ρ, hρ⟩ : ∃ ρ, ε - c * σ (σ ε) = (l : K) ^ (n + 1) * ρ :=
      ⟨(ε - c * σ (σ ε)) / (l : K) ^ (n + 1), by field_simp⟩
    have hρ1 : ‖ρ‖ ≤ 1 := by
      have hpos : 0 < ‖(l : K)‖ ^ (n + 1) := by rw [← hnl]; exact norm_pos_iff.mpr hlam0
      rw [hρ, norm_mul, hnl] at hε2
      exact le_of_mul_le_mul_left (by rwa [mul_one]) hpos
    obtain ⟨δ, hδ, hev⟩ := semilin_root hR (m := l ^ 2) (by omega) (-c⁻¹) (-(c⁻¹ * ρ))
      (by rw [norm_neg, hci]) (by rw [norm_neg, norm_mul, hci, one_mul]; exact hρ1)
    have hσl : σ (σ ((l : K) ^ (n + 1))) = (l : K) ^ (n + 1) := by simp [map_pow, map_natCast]
    have hlδ : ‖(l : K) ^ (n + 1) * δ‖ ≤ ‖(l : K)‖ ^ (n + 1) := by
      rw [norm_mul, hnl]
      calc ‖(l : K)‖ ^ (n + 1) * ‖δ‖ ≤ ‖(l : K)‖ ^ (n + 1) * 1 :=
            mul_le_mul_of_nonneg_left hδ (by positivity)
        _ = _ := mul_one _
    refine ⟨ε + (l : K) ^ (n + 1) * δ, ⟨?_, ?_⟩, ?_⟩
    · rw [semilin_norm_add_of_lt (by rw [hε1]; exact hlδ.trans_lt hsm), hε1]
    · have e : ε + (l : K) ^ (n + 1) * δ - c * σ (σ (ε + (l : K) ^ (n + 1) * δ)) =
          (l : K) ^ (n + 1) * (-c * (δ ^ (l ^ 2) + -c⁻¹ * δ + -(c⁻¹ * ρ)) - c * (σ (σ δ) - δ ^ (l ^ 2))) := by
        rw [map_add, map_add, map_mul, map_mul, hσl]
        linear_combination hρ - ((l : K) ^ (n + 1) * ρ + (l : K) ^ (n + 1) * δ) * hcc
      rw [e, norm_mul, hnl, pow_succ ‖(l : K)‖ (n + 1)]
      refine mul_le_mul_of_nonneg_left (semilin_norm_sub_le ?_ ?_) (by positivity)
      · rw [norm_mul, norm_neg, hc, one_mul]; exact hev
      · rw [norm_mul, hc, one_mul]; exact h.norm_sq_sub_pow_le δ hδ
    · rw [add_sub_cancel_left]; exact hlδ

  obtain ⟨ε0, hε0⟩ := h0
  choose g hg using hstep
  let v : (n : ℕ) → {x : K // P n x} := fun n =>
    Nat.rec (motive := fun n => {x : K // P n x}) ⟨ε0, hε0⟩
      (fun n ih => ⟨g n ih.1 ih.2, (hg n ih.1 ih.2).1⟩) n
  let u : ℕ → K := fun n => (v n).1
  have hu : ∀ n, P n (u n) := fun n => (v n).2
  have hud : ∀ n, ‖u (n + 1) - u n‖ ≤ ‖(l : K)‖ ^ (n + 1) := fun n => (hg n (u n) (hu n)).2
  have hcau : CauchySeq u := by
    refine cauchySeq_of_le_geometric ‖(l : K)‖ ‖(l : K)‖ hl1 fun n => ?_
    rw [dist_eq_norm, norm_sub_rev, ← pow_succ']
    exact hud n
  obtain ⟨ε, hlim⟩ := cauchySeq_tendsto_of_complete hcau
  have hσc : Continuous σ := ((AddMonoidHomClass.isometry_iff_norm σ).mpr h.isom).continuous
  have hres : Tendsto (fun n => u n - c * σ (σ (u n))) atTop (𝓝 (ε - c * σ (σ ε))) :=
    hlim.sub ((((hσc.comp hσc).tendsto ε).comp hlim).const_mul c)
  have hres0 : Tendsto (fun n => u n - c * σ (σ (u n))) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => (hu n).2.trans (pow_le_pow_of_le_one (norm_nonneg _) hl1.le (Nat.le_succ n)))
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl1)
  have hn : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖ε‖) := hlim.norm
  have hconst : (fun n => ‖u n‖) = fun _ => (1 : ℝ) := funext fun n => (hu n).1
  rw [hconst] at hn
  exact ⟨ε, tendsto_nhds_unique hn tendsto_const_nhds, sub_eq_zero.mp (tendsto_nhds_unique hres hres0)⟩
end ReciprocityTheory.ChartRestriction.L1
