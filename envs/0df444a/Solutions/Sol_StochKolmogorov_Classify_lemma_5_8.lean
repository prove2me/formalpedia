-- Prove2me | solution 1 for StochKolmogorov.Classify.lemma_5_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T14:06:29.41875+00:00
-- url     : https://prove2.me/submissions/efe59198-7925-40f5-8277-467d29be9ccc

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Model
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_1
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_4
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_6
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_7
import Theorems.Thm_StochKolmogorov_Classify_log_lln_squares
import Theorems.Thm_StochKolmogorov_Extinct_lemma_3_1
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2

set_option linter.all false
set_option Elab.async false


-- ===== module Shift =====
section Mod_Shift

/-! Path-shift invariance of the sink event (deterministic part of K4b): if the path `ω'` of `X'`
from `x'` is the path `ω` of `X` from `x` shifted by `t`, then `ω' ∈ extinctEvent C X' x' μ ↔
ω ∈ extinctEvent C X x μ`. The occupation measures differ by `O(t/T)`, the log rates by a factor
`(t+s)/s → 1`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Shift

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem occ_integral (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) {T : ℝ} (hT : 0 < T) (h : SDEState n →ᵇ ℝ) :
    ∫ y, h y ∂(occ X x T ω) = T⁻¹ * ∫ s in (0 : ℝ)..T, h (X x s.toNNReal ω) := by
  have hm : Measurable fun s : ℝ => X x s.toNNReal ω :=
    (hc.comp continuous_real_toNNReal).measurable
  unfold occ
  rw [integral_smul_measure, integral_map hm.aemeasurable h.continuous.aestronglyMeasurable,
    intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hT.le, smul_eq_mul]

theorem tendsto_of_close {a b e : ℕ → ℝ} {L : ℝ} (he : Tendsto e atTop (𝓝 0))
    (hab : ∀ k, |a k - b k| ≤ e k) (ha : Tendsto a atTop (𝓝 L)) : Tendsto b atTop (𝓝 L) := by
  have h0 : Tendsto (fun k => b k - a k) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by rw [Real.norm_eq_abs, abs_sub_comm]; exact hab k) he
  simpa using ha.add h0

/-- The occupation integrals of a path and of its `t`-shift differ by at most `2 t ‖h‖ / T`. -/
theorem occ_shift_close (X X' : SDEState n → ℝ≥0 → Ω → SDEState n) (x x' : SDEState n)
    (ω ω' : Ω) (t : ℝ≥0) (hs : ∀ s, X' x' s ω' = X x (t + s) ω)
    (hc : Continuous fun s => X x s ω) {T : ℝ} (hT : 0 < T) (h : SDEState n →ᵇ ℝ) :
    |∫ y, h y ∂(occ X x T ω) - ∫ y, h y ∂(occ X' x' T ω')| ≤ 2 * t * ‖h‖ / T := by
  have hc' : Continuous fun s => X' x' s ω' := by
    simp_rw [hs]; exact hc.comp (continuous_const.add continuous_id)
  rw [occ_integral X x ω hc hT h, occ_integral X' x' ω' hc' hT h]
  set p : ℝ → ℝ := fun u => h (X x u.toNNReal ω) with hp
  have hpc : Continuous p := h.continuous.comp (hc.comp continuous_real_toNNReal)
  have hpb : ∀ u, ‖p u‖ ≤ ‖h‖ := fun u => h.norm_coe_le_norm _
  have e1 : ∫ s in (0 : ℝ)..T, h (X' x' s.toNNReal ω') = ∫ s in (0 : ℝ)..T, p ((t : ℝ) + s) := by
    refine intervalIntegral.integral_congr fun s hs' => ?_
    have hs0 : 0 ≤ s := by
      rw [Set.uIcc_of_le hT.le] at hs'; exact hs'.1
    simp only [hp, hs]
    congr 2
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ hs0]
    exact (Real.coe_toNNReal _ (add_nonneg t.2 hs0)).symm
  rw [e1, intervalIntegral.integral_comp_add_left p (t : ℝ), add_zero]
  have hint : ∀ a b : ℝ, IntervalIntegrable p volume a b := fun a b => hpc.intervalIntegrable a b
  have e2 : (∫ u in (t : ℝ)..(t : ℝ) + T, p u) - ∫ u in (0 : ℝ)..T, p u =
      (∫ u in T..(t : ℝ) + T, p u) - ∫ u in (0 : ℝ)..(t : ℝ), p u := by
    have A := intervalIntegral.integral_add_adjacent_intervals (hint 0 t) (hint t (t + T))
    have B := intervalIntegral.integral_add_adjacent_intervals (hint 0 T) (hint T (t + T))
    linarith
  have b1 : ‖∫ u in T..(t : ℝ) + T, p u‖ ≤ ‖h‖ * |(t : ℝ) + T - T| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => hpb u
  have b2 : ‖∫ u in (0 : ℝ)..(t : ℝ), p u‖ ≤ ‖h‖ * |(t : ℝ) - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => hpb u
  rw [Real.norm_eq_abs] at b1 b2
  have ht0 : (0 : ℝ) ≤ t := t.2
  rw [add_sub_cancel_right, abs_of_nonneg ht0] at b1
  rw [sub_zero, abs_of_nonneg ht0] at b2
  rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.2 hT), abs_sub_comm, e2]
  rw [inv_mul_eq_div, div_le_div_iff_of_pos_right hT]
  have := abs_sub (∫ u in T..(t : ℝ) + T, p u) (∫ u in (0 : ℝ)..(t : ℝ), p u)
  linarith

theorem limitSet_shift (X X' : SDEState n → ℝ≥0 → Ω → SDEState n) (x x' : SDEState n)
    (ω ω' : Ω) (t : ℝ≥0) (hs : ∀ s, X' x' s ω' = X x (t + s) ω)
    (hc : Continuous fun s => X x s ω) : limitSet X' x' ω' = limitSet X x ω := by
  have key : ∀ (ts : ℕ → ℝ), (∀ k, 1 ≤ ts k) → Tendsto ts atTop atTop →
      ∀ h : SDEState n →ᵇ ℝ, Tendsto (fun k => 2 * t * ‖h‖ / ts k) atTop (𝓝 0) :=
    fun ts _ hts h => tendsto_const_nhds.div_atTop hts
  ext π
  constructor
  · rintro ⟨hπ, ts, h1, h2, h3⟩
    refine ⟨hπ, ts, h1, h2, fun h => tendsto_of_close (key ts h1 h2 h) (fun k => ?_) (h3 h)⟩
    rw [abs_sub_comm]
    exact occ_shift_close X X' x x' ω ω' t hs hc (by linarith [h1 k]) h
  · rintro ⟨hπ, ts, h1, h2, h3⟩
    refine ⟨hπ, ts, h1, h2, fun h => tendsto_of_close (key ts h1 h2 h) (fun k => ?_) (h3 h)⟩
    exact occ_shift_close X X' x x' ω ω' t hs hc (by linarith [h1 k]) h

theorem ratio_tendsto (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => ((t : ℝ) + s) / s) atTop (𝓝 1) := by
  have h1 : Tendsto (fun s : ℝ≥0 => (t : ℝ) / s) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have h2 := h1.const_add 1
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  have hs' : (0 : ℝ) < s := hs
  rw [add_div, div_self hs'.ne']
  ring

theorem ratio_tendsto' (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => (s : ℝ) / ((t : ℝ) + s)) atTop (𝓝 1) := by
  have := (ratio_tendsto t).inv₀ one_ne_zero
  rw [inv_one] at this
  refine this.congr' (Eventually.of_forall fun s => ?_)
  simp only [inv_div]

set_option maxHeartbeats 400000 in
theorem rate_shift (F : ℝ≥0 → ℝ) (t : ℝ≥0) (L : ℝ) :
    Tendsto (fun s : ℝ≥0 => F (t + s) / (s : ℝ)) atTop (𝓝 L) ↔
      Tendsto (fun u : ℝ≥0 => F u / (u : ℝ)) atTop (𝓝 L) := by
  have hadd : Tendsto (fun s : ℝ≥0 => t + s) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b, fun s hs => le_add_left hs⟩
  have hsub : Tendsto (fun u : ℝ≥0 => u - t) atTop atTop :=
    tendsto_atTop_atTop.2 fun b => ⟨b + t, fun u hu => le_tsub_of_add_le_right hu⟩
  constructor
  · intro hF
    have hm := hF.mul (ratio_tendsto' t)
    rw [mul_one] at hm
    have hG : Tendsto (fun s : ℝ≥0 => F (t + s) / ((t : ℝ) + s)) atTop (𝓝 L) := by
      refine hm.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with s hs
      have hs' : (0 : ℝ) < s := hs
      have ht' : (0 : ℝ) < (t : ℝ) + s := by have := t.2; linarith
      rw [div_mul_div_comm, mul_comm (s : ℝ), mul_div_mul_right _ _ hs'.ne']
    refine (hG.comp hsub).congr' ?_
    filter_upwards [eventually_ge_atTop t] with u hu
    simp only [Function.comp_apply]
    rw [← NNReal.coe_add, add_tsub_cancel_of_le hu]
  · intro hF
    have hm := (hF.comp hadd).mul (ratio_tendsto t)
    rw [mul_one] at hm
    refine hm.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    have hs' : (0 : ℝ) < s := hs
    have ht' : (0 : ℝ) < (t : ℝ) + s := by have := t.2; linarith
    simp only [Function.comp_apply, NNReal.coe_add]
    rw [div_mul_div_comm, mul_comm _ ((t : ℝ) + s), mul_div_mul_left _ _ ht'.ne']

/-- The sink event is invariant under shifting the path. -/
theorem extinctEvent_shift (C : Coeffs n) (X X' : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x x' : SDEState n) (μ : Measure (SDEState n)) (ω ω' : Ω) (t : ℝ≥0)
    (hs : ∀ s, X' x' s ω' = X x (t + s) ω) (hc : Continuous fun s => X x s ω) :
    ω' ∈ extinctEvent C X' x' μ ↔ ω ∈ extinctEvent C X x μ := by
  unfold extinctEvent
  simp only [Set.mem_setOf_eq, limitSet_shift X X' x x' ω ω' t hs hc, hs]
  refine and_congr Iff.rfl (forall_congr' fun i => imp_congr Iff.rfl (and_congr ?_ Iff.rfl))
  exact rate_shift (fun u => Real.log (X x u ω i)) t _

end StochKolmogorov.Classify.Shift

end Mod_Shift

-- ===== module UcGlue =====
section Mod_UcGlue

/-! U-c of 8f909832 (paper p.28, "similar to Lemma 5.8"): a.s. no limit point of the occupation
measures lies in `Conv(M²)`. Formal Assumption 1.5 is pointwise (`∃ i, λᵢ(ν) > 0` on `Conv(M²)`),
so no minimax is needed: it suffices that `λᵢ(π) ≤ 0` for every `π ∈ U(ω)` and every `i`.
`lyap_nonpos` derives that from Lemma 5.6 (sibling), Lemma 5.4 clause 1 (sibling), Lemma 5.7
clause 2 (sibling) and two pathwise facts along INTEGER times (hB) and SQUARES (hL):
 hL: `ln Xᵢ(m²)/m² − ∫ hᵢ dΠ̃_{m²} → 0` (Itô for ln Xᵢ + L² martingale bound + Borel–Cantelli), and
 hB: `ln Xᵢ(N) ≤ εN` eventually (moment bound + Borel–Cantelli).
The limit sequence `t_k` is replaced by `⌊√t_k⌋²` (`occ_close`, `tendsto_sq`). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.UcGlue

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- `M² = ∅` or the pointwise Assumption 1.5, plus `λᵢ ≤ 0` on `U(ω)`, keep `U(ω)` off `Conv(M²)`. -/
theorem not_conv_M2 [MeasurableSpace Ω] {P : Measure Ω} {C : Coeffs n}
    {X : SDEState n → ℝ≥0 → Ω → SDEState n} {x : SDEState n}
    (h15 : Assumption15 P C X)
    (hlyap : ∀ᵐ ω ∂P, ∀ π ∈ limitSet X x ω, ∀ i, lyap C i π ≤ 0) :
    ∀ᵐ ω ∂P, ∀ π ∈ limitSet X x ω, π ∉ conv (M2 P C X) := by
  filter_upwards [hlyap] with ω hω π hπ hc
  rcases h15 with h | h
  · rw [h] at hc
    obtain ⟨s, p, hs, -, hsum, -⟩ := hc
    have hs0 : s = ∅ := by
      ext μ
      simp only [Finset.notMem_empty, iff_false]
      intro hμ
      exact hs hμ
    rw [hs0, Finset.sum_empty] at hsum
    exact zero_ne_one hsum
  · obtain ⟨i, hi⟩ := h π hc
    linarith [hω π hπ i]

/-- Occupation averages at `T ≥ 1` and at `⌊T⌋` differ by at most `2‖h‖/T`. -/
theorem occ_floor_close (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) {T : ℝ} (hT : 1 ≤ T) (h : SDEState n →ᵇ ℝ) :
    |∫ y, h y ∂(occ X x T ω) - ∫ y, h y ∂(occ X x (⌊T⌋₊ : ℝ) ω)| ≤ 2 * ‖h‖ / T := by
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hN1 : (1 : ℝ) ≤ (⌊T⌋₊ : ℝ) := by
    have : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    exact_mod_cast this
  have hN0 : (0 : ℝ) < (⌊T⌋₊ : ℝ) := lt_of_lt_of_le one_pos hN1
  have hNT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le hT0.le
  have hTN : T - (⌊T⌋₊ : ℝ) ≤ 1 := by
    have := Nat.lt_floor_add_one T
    linarith
  rw [Shift.occ_integral X x ω hc hT0 h, Shift.occ_integral X x ω hc hN0 h]
  set N : ℝ := (⌊T⌋₊ : ℝ) with hNdef
  set p : ℝ → ℝ := fun u => h (X x u.toNNReal ω) with hp
  have hpc : Continuous p := h.continuous.comp (hc.comp continuous_real_toNNReal)
  set M : ℝ := ‖h‖ with hM
  have hpb : ∀ u, ‖p u‖ ≤ M := fun u => h.norm_coe_le_norm _
  set AT : ℝ := ∫ s in (0 : ℝ)..T, p s with hAT
  set AN : ℝ := ∫ s in (0 : ℝ)..N, p s with hAN
  have hdiff : AT - AN = ∫ s in N..T, p s :=
    intervalIntegral.integral_interval_sub_left (hpc.intervalIntegrable _ _)
      (hpc.intervalIntegrable _ _)
  have hD : |AT - AN| ≤ M := by
    rw [hdiff]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := N) (b := T)
      (f := p) (C := M) (fun u _ => hpb u)
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - N)] at this
    have hM0 : 0 ≤ M := norm_nonneg _
    nlinarith
  have hA : |AN| ≤ M * N := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := N)
      (f := p) (C := M) (fun u _ => hpb u)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hN0] at this
    exact this
  have heq : T⁻¹ * AT - N⁻¹ * AN = (AT - AN) / T - AN * (T - N) / (T * N) := by
    field_simp
    ring
  rw [heq]
  have h1 : |(AT - AN) / T| ≤ M / T := by
    rw [abs_div, abs_of_pos hT0]
    exact div_le_div_of_nonneg_right hD hT0.le
  have h2 : |AN * (T - N) / (T * N)| ≤ M / T := by
    rw [abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - N),
      abs_of_pos (mul_pos hT0 hN0)]
    rw [div_le_div_iff₀ (mul_pos hT0 hN0) hT0]
    have hM0 : 0 ≤ M := norm_nonneg _
    have e1 : |AN| * (T - N) ≤ M * N * 1 :=
      mul_le_mul hA hTN (by linarith) (mul_nonneg hM0 hN0.le)
    have e2 : M * N * 1 * T = M * (T * N) := by ring
    calc |AN| * (T - N) * T ≤ M * N * 1 * T := mul_le_mul_of_nonneg_right e1 hT0.le
      _ = M * (T * N) := e2
  calc |(AT - AN) / T - AN * (T - N) / (T * N)|
      ≤ |(AT - AN) / T| + |AN * (T - N) / (T * N)| := abs_sub _ _
    _ ≤ M / T + M / T := add_le_add h1 h2
    _ = 2 * M / T := by ring

/-- Limit points of the occupation measures along `t_k` are limit points along `⌊t_k⌋`. -/
theorem tendsto_floor (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (π : Measure (SDEState n)) (ts : ℕ → ℝ)
    (h1 : ∀ k, 1 ≤ ts k) (hts : Tendsto ts atTop atTop)
    (hconv : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occ X x (ts k) ω)) atTop (𝓝 (∫ y, h y ∂π)))
    (h : SDEState n →ᵇ ℝ) :
    Tendsto (fun k => ∫ y, h y ∂(occ X x ((⌊ts k⌋₊ : ℕ) : ℝ) ω)) atTop (𝓝 (∫ y, h y ∂π)) := by
  refine Shift.tendsto_of_close (e := fun k => 2 * ‖h‖ / ts k)
    (tendsto_const_nhds.div_atTop hts) (fun k => occ_floor_close X x ω hc (h1 k) h) (hconv h)

/-- Occupation averages at `T` and at `S ∈ (0, T]` differ by at most `2‖h‖(T−S)/T`. -/
theorem occ_close (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) {S T : ℝ} (hS : 0 < S) (hST : S ≤ T)
    (h : SDEState n →ᵇ ℝ) :
    |∫ y, h y ∂(occ X x T ω) - ∫ y, h y ∂(occ X x S ω)| ≤ 2 * ‖h‖ * (T - S) / T := by
  have hT0 : 0 < T := lt_of_lt_of_le hS hST
  rw [Shift.occ_integral X x ω hc hT0 h, Shift.occ_integral X x ω hc hS h]
  set p : ℝ → ℝ := fun u => h (X x u.toNNReal ω) with hp
  have hpc : Continuous p := h.continuous.comp (hc.comp continuous_real_toNNReal)
  set M : ℝ := ‖h‖ with hM
  have hM0 : 0 ≤ M := norm_nonneg _
  have hpb : ∀ u, ‖p u‖ ≤ M := fun u => h.norm_coe_le_norm _
  set AT : ℝ := ∫ s in (0 : ℝ)..T, p s with hAT
  set AS : ℝ := ∫ s in (0 : ℝ)..S, p s with hAS
  have hdiff : AT - AS = ∫ s in S..T, p s :=
    intervalIntegral.integral_interval_sub_left (hpc.intervalIntegrable _ _)
      (hpc.intervalIntegrable _ _)
  have hD : |AT - AS| ≤ M * (T - S) := by
    rw [hdiff]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := S) (b := T)
      (f := p) (C := M) (fun u _ => hpb u)
    rwa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - S)] at this
  have hA : |AS| ≤ M * S := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := S)
      (f := p) (C := M) (fun u _ => hpb u)
    rwa [Real.norm_eq_abs, sub_zero, abs_of_pos hS] at this
  have heq : T⁻¹ * AT - S⁻¹ * AS = (AT - AS) / T - AS * (T - S) / (T * S) := by
    field_simp
    ring
  rw [heq]
  have h1 : |(AT - AS) / T| ≤ M * (T - S) / T := by
    rw [abs_div, abs_of_pos hT0]
    exact div_le_div_of_nonneg_right hD hT0.le
  have h2 : |AS * (T - S) / (T * S)| ≤ M * (T - S) / T := by
    rw [abs_div, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T - S),
      abs_of_pos (mul_pos hT0 hS), div_le_div_iff₀ (mul_pos hT0 hS) hT0]
    have e1 : |AS| * (T - S) * T ≤ M * S * (T - S) * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (by linarith)) hT0.le
    calc |AS| * (T - S) * T ≤ M * S * (T - S) * T := e1
      _ = M * (T - S) * (T * S) := by ring
  calc |(AT - AS) / T - AS * (T - S) / (T * S)|
      ≤ |(AT - AS) / T| + |AS * (T - S) / (T * S)| := abs_sub _ _
    _ ≤ M * (T - S) / T + M * (T - S) / T := add_le_add h1 h2
    _ = 2 * M * (T - S) / T := by ring

/-- Limit points along `t_k` are limit points along the squares `⌊√t_k⌋²`. -/
theorem tendsto_sq (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (π : Measure (SDEState n)) (ts : ℕ → ℝ)
    (h1 : ∀ k, 1 ≤ ts k) (hts : Tendsto ts atTop atTop)
    (hconv : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occ X x (ts k) ω)) atTop (𝓝 (∫ y, h y ∂π)))
    (h : SDEState n →ᵇ ℝ) :
    Tendsto (fun k => ∫ y, h y ∂(occ X x (((⌊√(ts k)⌋₊ ^ 2 : ℕ)) : ℝ) ω)) atTop
      (𝓝 (∫ y, h y ∂π)) := by
  refine Shift.tendsto_of_close (e := fun k => 6 * ‖h‖ / √(ts k))
    (tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hts)) (fun k => ?_) (hconv h)
  set T := ts k with hTdef
  have hT1 : 1 ≤ T := h1 k
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  set r : ℝ := √T with hr
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.2 hT1
  have hrr : r * r = T := Real.mul_self_sqrt hT0.le
  set m : ℕ := ⌊r⌋₊ with hm
  have hm1 : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := Nat.le_floor (by exact_mod_cast hr1)
    exact_mod_cast this
  have hmr : (m : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hrm : r < m + 1 := Nat.lt_floor_add_one r
  have hS : (((m ^ 2 : ℕ)) : ℝ) = (m : ℝ) * m := by push_cast; ring
  have hS0 : (0 : ℝ) < (((m ^ 2 : ℕ)) : ℝ) := by rw [hS]; nlinarith
  have hST : (((m ^ 2 : ℕ)) : ℝ) ≤ T := by rw [hS, ← hrr]; nlinarith
  have hTS : T - (((m ^ 2 : ℕ)) : ℝ) ≤ 3 * r := by rw [hS, ← hrr]; nlinarith
  refine le_trans (occ_close X x ω hc hS0 hST h) ?_
  have hM0 : 0 ≤ ‖h‖ := norm_nonneg _
  have hr0 : 0 < r := by linarith
  rw [div_le_div_iff₀ hT0 hr0]
  have e1 : 2 * ‖h‖ * (T - (((m ^ 2 : ℕ)) : ℝ)) * r ≤ 2 * ‖h‖ * (3 * r) * r :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hTS (by positivity)) hr0.le
  calc 2 * ‖h‖ * (T - (((m ^ 2 : ℕ)) : ℝ)) * r ≤ 2 * ‖h‖ * (3 * r) * r := e1
    _ = 6 * ‖h‖ * (r * r) := by ring
    _ = 6 * ‖h‖ * T := by rw [hrr]

/-- The Lyapunov integrand `hᵢ = fᵢ − σᵢᵢgᵢ²/2` is dominated by the growth weight with `δ = 0`. -/
theorem lyapF_bound (C : Coeffs n) (c : SDEState n) (i : Fin n) (y : SDEState n) :
    |C.f i y - C.sig i i * C.g i y ^ 2 / 2| < (1 + |C.sig i i|) * growthWeight C c 0 y := by
  unfold growthWeight
  rw [Real.rpow_zero, one_mul]
  have hs : |C.f i y| + C.g i y ^ 2 ≤ ∑ j, (|C.f j y| + C.g j y ^ 2) :=
    Finset.single_le_sum (f := fun j => |C.f j y| + C.g j y ^ 2)
      (fun j _ => add_nonneg (abs_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
  have hg : 0 ≤ C.g i y ^ 2 := sq_nonneg _
  have hσ : 0 ≤ |C.sig i i| := abs_nonneg _
  have hf : 0 ≤ |C.f i y| := abs_nonneg _
  have habs : |C.f i y - C.sig i i * C.g i y ^ 2 / 2| ≤ |C.f i y| + |C.sig i i| * C.g i y ^ 2 := by
    calc |C.f i y - C.sig i i * C.g i y ^ 2 / 2|
        ≤ |C.f i y| + |C.sig i i * C.g i y ^ 2 / 2| := abs_sub _ _
      _ = |C.f i y| + |C.sig i i| * C.g i y ^ 2 / 2 := by
          rw [abs_div, abs_mul, abs_of_nonneg hg, abs_two]
      _ ≤ |C.f i y| + |C.sig i i| * C.g i y ^ 2 := by
          have : 0 ≤ |C.sig i i| * C.g i y ^ 2 := mul_nonneg hσ hg
          linarith
  have hS0 : 0 ≤ ∑ j, (|C.f j y| + C.g j y ^ 2) := le_trans (add_nonneg hf hg) hs
  have key : |C.f i y| + |C.sig i i| * C.g i y ^ 2
      ≤ (1 + |C.sig i i|) * (∑ j, (|C.f j y| + C.g j y ^ 2)) := by
    have e1 : |C.sig i i| * C.g i y ^ 2 ≤ |C.sig i i| * ∑ j, (|C.f j y| + C.g j y ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hσ
    have e2 : |C.f i y| ≤ ∑ j, (|C.f j y| + C.g j y ^ 2) := by linarith
    nlinarith
  have hlt : (1 + |C.sig i i|) * (∑ j, (|C.f j y| + C.g j y ^ 2))
      < (1 + |C.sig i i|) * (1 + ∑ j, (|C.f j y| + C.g j y ^ 2)) := by
    have : 0 < 1 + |C.sig i i| := by linarith
    nlinarith
  linarith

/-- Lemma-5.8-style core of U-c: every limit point `π ∈ U(ω)` has `λᵢ(π) ≤ 0`, a.s.
Inputs: Lemma 5.6 (`h56`, at this `x`), Lemma 5.4 clause 1 (`h54`), Lemma 5.7 clause 2 (`h57`),
the pathwise log-LLN along integers (`hL`) and the integer-time log upper bound (`hB`). -/
theorem lyap_nonpos [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c : SDEState n) (δ₁ : ℝ) (hδ₁ : 0 < δ₁)
    (hfc : ∀ i, ContinuousOn (C.f i) (orthant n)) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hcont : ∀ ω, Continuous fun s => X x s ω)
    (h56 : ∀ ω : Ω, (∀ t, X x t ω ∈ orthant n) → ∀ Khat : ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) →
      ∀ (Ts : ℕ → ℝ) (π : Measure (SDEState n)), Tendsto Ts atTop atTop → IsInvariant P X π →
      (∀ h : SDEState n →ᵇ ℝ,
        Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))) →
      ∀ (h : SDEState n → ℝ) (Kh δ : ℝ), ContinuousOn h (orthant n) → 0 < Kh → 0 ≤ δ →
        δ < δ₁ → (∀ y ∈ orthant n, |h y| < Kh * growthWeight C c δ y) →
        Integrable h π ∧
          Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π)))
    (h54 : ∃ Khat : ℝ, 0 < Khat ∧ ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t))
    (h57 : ∀ᵐ ω ∂P, ∀ π ∈ limitSet X x ω, IsInvariant P X π)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    (hL : ∀ᵐ ω ∂P, ∀ i, Tendsto (fun m : ℕ =>
      Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω i) / ((m ^ 2 : ℕ) : ℝ)
      - ∫ y, (C.f i y - C.sig i i * C.g i y ^ 2 / 2) ∂(occ X x ((m ^ 2 : ℕ) : ℝ) ω))
        atTop (𝓝 0))
    (hB : ∀ᵐ ω ∂P, ∀ i, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, Real.log (X x (N : ℝ≥0) ω i) ≤ ε * N) :
    ∀ᵐ ω ∂P, ∀ π ∈ limitSet X x ω, ∀ i, lyap C i π ≤ 0 := by
  obtain ⟨Khat, -, hK⟩ := h54
  filter_upwards [hK, h57, hstay, hL, hB] with ω hKω h57ω hsω hLω hBω
  intro π hπ i
  have hinv := h57ω π hπ
  obtain ⟨-, ts, h1, hts, hconv⟩ := hπ
  set m : ℕ → ℕ := fun k => ⌊√(ts k)⌋₊ with hm
  have hmt : Tendsto m atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_sqrt_atTop.comp hts)
  set q : ℕ → ℕ := fun k => m k ^ 2 with hq
  have hqt : Tendsto q atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_self_pow two_ne_zero (m k)) hmt
  have hmr : Tendsto (fun k => ((q k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hqt
  have hconv' : ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occ X x ((q k : ℕ) : ℝ) ω)) atTop (𝓝 (∫ y, h y ∂π)) :=
    fun h => tendsto_sq X x ω (hcont ω) π ts h1 hts hconv h
  set hF : SDEState n → ℝ := fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2 with hhF
  have hFc : ContinuousOn hF (orthant n) :=
    (hfc i).sub ((continuousOn_const.mul ((hgc i).pow 2)).div_const 2)
  have hlim := (h56 ω hsω Khat hKω (fun k => ((q k : ℕ) : ℝ)) π hmr hinv hconv' hF
    (1 + |C.sig i i|) 0 hFc (by positivity) le_rfl hδ₁
    (fun y _ => lyapF_bound C c i y)).2
  have hlog : Tendsto (fun k => Real.log (X x ((q k : ℕ) : ℝ≥0) ω i) / ((q k : ℕ) : ℝ))
      atTop (𝓝 (lyap C i π)) := by
    have h2 := ((hLω i).comp hmt).add hlim
    rw [zero_add] at h2
    refine h2.congr (fun k => ?_)
    simp only [Function.comp, hhF]
    ring
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  have hev : ∀ᶠ k in atTop,
      Real.log (X x ((q k : ℕ) : ℝ≥0) ω i) / ((q k : ℕ) : ℝ) ≤ ε := by
    filter_upwards [hqt.eventually (hBω i ε hε), hqt.eventually (eventually_ge_atTop 1)]
      with k hk hk1
    have hpos : (0 : ℝ) < ((q k : ℕ) : ℝ) := by exact_mod_cast hk1
    rw [div_le_iff₀ hpos]
    exact hk
  exact le_of_tendsto hlog hev

end StochKolmogorov.Classify.UcGlue

end Mod_UcGlue

-- ===== module HB =====
section Mod_HB

/-! hB of 8f909832 (paper (5.22), integer times): a uniform moment bound
`E (1 + cᵀX_N)^δ ≤ K` (Persist Lemma 3.2 (3.7), Proved 15eaca53, via the persistCoeffs bridge)
gives, by Markov + Borel–Cantelli, a.s. `ln Xᵢ(N) ≤ εN` eventually, for all `i`, `ε > 0`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.HB

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- Borel–Cantelli for one coordinate and one `ε`. -/
theorem log_le_one [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x c : SDEState n) (hc : c ∈ openOrthant n)
    (hmeas : ∀ t, Measurable (X x t)) {δ K : ℝ} (hδ : 0 < δ)
    (hmom : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x (N : ℝ≥0) ω i) ^ δ) ∂P ≤ ENNReal.ofReal K)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n) (i : Fin n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, Real.log (X x (N : ℝ≥0) ω i) ≤ ε * N := by
  have hci : 0 < c i := hc i
  set a : ℕ → ℝ := fun N => Real.exp (ε * N) * c i with ha
  have ha0 : ∀ N, 0 < a N := fun N => mul_pos (Real.exp_pos _) hci
  set A : ℕ → Set Ω := fun N => {ω | a N ≤ 1 + ∑ j, c j * X x (N : ℝ≥0) ω j} with hA
  set F : ℕ → Ω → ℝ≥0∞ := fun N ω =>
    ENNReal.ofReal ((1 + ∑ j, c j * X x (N : ℝ≥0) ω j) ^ δ) with hF
  have hFm : ∀ N, Measurable (F N) := by
    intro N
    refine ENNReal.measurable_ofReal.comp ?_
    have h1 : Measurable fun ω => 1 + ∑ j, c j * X x (N : ℝ≥0) ω j := by
      refine measurable_const.add (Finset.measurable_sum _ fun j _ => ?_)
      exact measurable_const.mul
        (((continuous_apply j).comp (PiLp.continuous_ofLp 2 _)).measurable.comp (hmeas _))
    exact h1.pow_const δ
  -- bound on P(A N)
  set b : ℕ → ℝ := fun N => |K| / c i ^ δ * Real.exp (-(δ * ε)) ^ N with hb
  have hAle : ∀ N, 1 ≤ N → P (A N) ≤ ENNReal.ofReal (b N) := by
    intro N hN
    have hsub : A N ⊆ {ω | ENNReal.ofReal (a N ^ δ) ≤ F N ω} := by
      intro ω hω
      simp only [hA, Set.mem_setOf_eq] at hω
      simp only [Set.mem_setOf_eq, hF]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (ha0 N).le hω hδ.le)
    have hmk := mul_meas_ge_le_lintegral₀ (hFm N).aemeasurable (ENNReal.ofReal (a N ^ δ)) (μ := P)
    have hapos : 0 < a N ^ δ := Real.rpow_pos_of_pos (ha0 N) δ
    have h2 : ENNReal.ofReal (a N ^ δ) * P (A N) ≤ ENNReal.ofReal |K| :=
      le_trans (mul_le_mul' le_rfl (measure_mono hsub))
        (le_trans hmk (le_trans (hmom N hN) (ENNReal.ofReal_le_ofReal (le_abs_self K))))
    have hne : ENNReal.ofReal (a N ^ δ) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hapos
    have h3 : P (A N) ≤ ENNReal.ofReal |K| / ENNReal.ofReal (a N ^ δ) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]
      exact h2
    refine le_trans h3 (le_of_eq ?_)
    rw [← ENNReal.ofReal_div_of_pos hapos]
    congr 1
    have e1 : a N ^ δ = Real.exp (δ * ε) ^ N * c i ^ δ := by
      simp only [ha]
      rw [Real.mul_rpow (Real.exp_pos _).le hci.le, ← Real.exp_mul, ← Real.exp_nat_mul]
      congr 2
      ring
    rw [e1, hb, Real.exp_neg]
    beta_reduce
    rw [inv_pow]
    field_simp
  -- summability
  have hr : Real.exp (-(δ * ε)) < 1 := by
    have hneg : -(δ * ε) < 0 := by nlinarith
    calc Real.exp (-(δ * ε)) < Real.exp 0 := Real.exp_lt_exp.2 hneg
      _ = 1 := Real.exp_zero
  have hbs : Summable b :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left _
  have hb0 : ∀ N, 0 ≤ b N := fun N =>
    mul_nonneg (div_nonneg (abs_nonneg _) (Real.rpow_nonneg hci.le _))
      (pow_nonneg (Real.exp_pos _).le _)
  set A' : ℕ → Set Ω := fun N => A (N + 1) with hA'
  have hsum : ∑' N, P (A' N) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' N, b (N + 1))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg (fun N => hb0 (N + 1))
      ((summable_nat_add_iff 1).2 hbs)]
    exact ENNReal.tsum_le_tsum fun N => hAle (N + 1) (by omega)
  have hae : ∀ᵐ ω ∂P, ∀ᶠ N in atTop, ω ∉ A' N := ae_eventually_notMem hsum
  filter_upwards [hae, hstay] with ω hω hs
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hω
  refine eventually_atTop.2 ⟨N0 + 1, fun N hN => ?_⟩
  have hNA : ω ∉ A N := by
    have h1 := hN0 (N - 1) (by omega)
    simp only [hA'] at h1
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ N)] at h1
  simp only [hA, Set.mem_setOf_eq, not_le] at hNA
  have hterm : c i * X x (N : ℝ≥0) ω i ≤ ∑ j, c j * X x (N : ℝ≥0) ω j :=
    Finset.single_le_sum (f := fun j => c j * X x (N : ℝ≥0) ω j)
      (fun j _ => mul_nonneg (hc j).le (hs _ j)) (Finset.mem_univ i)
  have hXi : X x (N : ℝ≥0) ω i < Real.exp (ε * N) := by
    have h2 : c i * X x (N : ℝ≥0) ω i < c i * Real.exp (ε * N) := by
      simp only [ha] at hNA
      linarith
    exact lt_of_mul_lt_mul_left h2 hci.le
  rcases (hs (N : ℝ≥0) i).eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero]
    positivity
  · exact (Real.log_le_iff_le_exp hpos).2 hXi.le

/-- hB: a.s., for all `i` and `ε > 0`, eventually `ln Xᵢ(N) ≤ εN` along integers. -/
theorem log_le [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x c : SDEState n) (hc : c ∈ openOrthant n)
    (hmeas : ∀ t, Measurable (X x t)) {δ K : ℝ} (hδ : 0 < δ)
    (hmom : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x (N : ℝ≥0) ω i) ^ δ) ∂P ≤ ENNReal.ofReal K)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n) :
    ∀ᵐ ω ∂P, ∀ i, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, Real.log (X x (N : ℝ≥0) ω i) ≤ ε * N := by
  have h : ∀ i (m : ℕ), ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
      Real.log (X x (N : ℝ≥0) ω i) ≤ (1 / ((m : ℝ) + 1)) * N :=
    fun i m => log_le_one P X x c hc hmeas hδ hmom hstay i (by positivity)
  have h' : ∀ᵐ ω ∂P, ∀ i (m : ℕ), ∀ᶠ N : ℕ in atTop,
      Real.log (X x (N : ℝ≥0) ω i) ≤ (1 / ((m : ℝ) + 1)) * N := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact h i
  filter_upwards [h'] with ω hω i ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω i m] with N hN
  exact le_trans hN (mul_le_mul_of_nonneg_right hm.le (Nat.cast_nonneg N))

end StochKolmogorov.Classify.HB

end Mod_HB

-- ===== module HLglue =====
section Mod_HLglue

/-! s13: parent-side glue for `hL`. The NEW child `log_lln_squares` (statement `LogLLNSq` below:
linear growth of `∫₀ᵗ gᵢ²` ⇒ `ln Xᵢ(m²)/m² − (1/m²)∫₀^{m²} hᵢ(X) → 0` a.s.) gives `hL` of
`UcGlue.lyap_nonpos` once `∫₀ᵗ gᵢ²` is bounded by lemma 5.4 clause 1 and the time average is
rewritten as an occupation integral. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.HLglue

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- Conclusion of the NEW child `log_lln_squares` at one starting point. -/
def LogLLNSq [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) : Prop :=
  (∃ K : ℝ, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2 ≤ K * t) →
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun m : ℕ =>
      Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω i) / ((m ^ 2 : ℕ) : ℝ)
      - ((m ^ 2 : ℕ) : ℝ)⁻¹ * ∫ u in (0 : ℝ)..((m ^ 2 : ℕ) : ℝ),
          (C.f i (X x u.toNNReal ω) - C.sig i i * C.g i (X x u.toNNReal ω) ^ 2 / 2))
        atTop (𝓝 0)

theorem sq_le_growthWeight (C : Coeffs n) {c : SDEState n} (hc : c ∈ openOrthant n) {δ : ℝ}
    (hδ : 0 ≤ δ) {y : SDEState n} (hy : y ∈ orthant n) (i : Fin n) :
    C.g i y ^ 2 ≤ growthWeight C c δ y := by
  unfold growthWeight
  have h1 : 1 ≤ (1 + ∑ j, c j * y j) ^ δ := Real.one_le_rpow
    (le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => mul_nonneg (hc j).le (hy j))) hδ
  have h2 : C.g i y ^ 2 ≤ 1 + ∑ j, (|C.f j y| + C.g j y ^ 2) := by
    have := Finset.single_le_sum (f := fun j => |C.f j y| + C.g j y ^ 2)
      (fun j _ => add_nonneg (abs_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
    linarith [abs_nonneg (C.f i y)]
  have h3 : 0 ≤ 1 + ∑ j, (|C.f j y| + C.g j y ^ 2) := le_trans (sq_nonneg _) h2
  calc C.g i y ^ 2 ≤ 1 + ∑ j, (|C.f j y| + C.g j y ^ 2) := h2
    _ = 1 * (1 + ∑ j, (|C.f j y| + C.g j y ^ 2)) := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 h3

/-- The quadratic-variation bound of the child from lemma 5.4 clause 1. -/
theorem hQ_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c : SDEState n) (hc : c ∈ openOrthant n)
    (hgc : ∀ i, ContinuousOn (C.g i) (orthant n)) (x : SDEState n)
    (hcont : ∀ ω, Continuous fun s => X x s ω) (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (h54 : ∃ Khat : ℝ, 0 < Khat ∧ ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) :
    ∃ K : ℝ, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ t : ℝ in atTop,
      ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2 ≤ K * t := by
  obtain ⟨Kh, hKh, hK⟩ := h54
  refine ⟨Kh + 1, ?_⟩
  filter_upwards [hK, hstay] with ω hω hs i
  filter_upwards [hω 1 one_pos, eventually_ge_atTop (0 : ℝ)] with t ht ht0
  have hpc : Continuous fun u : ℝ => X x u.toNNReal ω :=
    (hcont ω).comp continuous_real_toNNReal
  have hgc' : Continuous fun u : ℝ => C.g i (X x u.toNNReal ω) ^ 2 :=
    ((hgc i).comp_continuous hpc (fun u => hs _)).pow 2
  have hint : IntegrableOn (fun u : ℝ => C.g i (X x u.toNNReal ω) ^ 2) (Set.Icc 0 t) :=
    hgc'.continuousOn.integrableOn_compact isCompact_Icc
  have heq : ∫ u in (0 : ℝ)..t, C.g i (X x u.toNNReal ω) ^ 2
      = ∫ u in Set.Icc (0 : ℝ) t, C.g i (X x u.toNNReal ω) ^ 2 := by
    rw [intervalIntegral.integral_of_le ht0, integral_Icc_eq_integral_Ioc]
  rw [heq]
  have hle : ENNReal.ofReal (∫ u in Set.Icc (0 : ℝ) t, C.g i (X x u.toNNReal ω) ^ 2)
      ≤ ENNReal.ofReal ((Kh + 1) * t) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun u => sq_nonneg _)]
    refine le_trans (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_) ht
    exact sq_le_growthWeight C hc hδ (hs _) i
  have hR : 0 ≤ (Kh + 1) * t := mul_nonneg (by linarith) ht0
  exact (ENNReal.ofReal_le_ofReal_iff hR).1 hle

theorem measurableSet_orthant' : MeasurableSet (orthant n) := by
  have e : orthant n = ⋂ i, {x : SDEState n | 0 ≤ x i} := by
    ext x; simp [orthant]
  rw [e]
  exact MeasurableSet.iInter fun i =>
    measurableSet_le measurable_const (PiLp.continuous_apply 2 _ i).measurable

/-- `occ_integral` for an unbounded `h` continuous on the orthant (path in the orthant). -/
theorem occ_integral_cont (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (hs : ∀ s, X x s ω ∈ orthant n) {T : ℝ} (hT : 0 < T)
    {h : SDEState n → ℝ} (hh : ContinuousOn h (orthant n)) :
    ∫ y, h y ∂(occ X x T ω) = T⁻¹ * ∫ s in (0 : ℝ)..T, h (X x s.toNNReal ω) := by
  have hm : Measurable fun s : ℝ => X x s.toNNReal ω :=
    (hc.comp continuous_real_toNNReal).measurable
  have hae : ∀ᵐ y ∂((volume.restrict (Set.Icc (0 : ℝ) T)).map (fun s => X x s.toNNReal ω)),
      y ∈ orthant n :=
    (ae_map_iff hm.aemeasurable measurableSet_orthant').2 (ae_of_all _ fun s => hs _)
  have hsm : AEStronglyMeasurable h
      ((volume.restrict (Set.Icc (0 : ℝ) T)).map (fun s => X x s.toNNReal ω)) := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]
    exact hh.aestronglyMeasurable measurableSet_orthant'
  unfold occ
  rw [integral_smul_measure, integral_map hm.aemeasurable hsm,
    intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hT.le, smul_eq_mul]

/-- `hL` of `UcGlue.lyap_nonpos` at `x` from the child `log_lln_squares` and lemma 5.4 cl. 1. -/
theorem hL_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c : SDEState n) (hc : c ∈ openOrthant n)
    (hfc : ∀ i, ContinuousOn (C.f i) (orthant n)) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n))
    (x : SDEState n) (hcont : ∀ ω, Continuous fun s => X x s ω)
    (hstay : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n) {δ : ℝ} (hδ : 0 ≤ δ)
    (h54 : ∃ Khat : ℝ, 0 < Khat ∧ ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t))
    (hchild : LogLLNSq P C X x) :
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun m : ℕ =>
      Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω i) / ((m ^ 2 : ℕ) : ℝ)
      - ∫ y, (C.f i y - C.sig i i * C.g i y ^ 2 / 2) ∂(occ X x ((m ^ 2 : ℕ) : ℝ) ω))
        atTop (𝓝 0) := by
  have hQ := hQ_of P C X c hc hgc x hcont hstay hδ h54
  filter_upwards [hchild hQ, hstay] with ω h1 hs i
  refine (h1 i).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with m hm
  have hT : (0 : ℝ) < ((m ^ 2 : ℕ) : ℝ) := by
    have : 0 < m ^ 2 := pow_pos (by omega) 2
    exact_mod_cast this
  have hcon : ContinuousOn (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) (orthant n) :=
    (hfc i).sub ((continuousOn_const.mul ((hgc i).pow 2)).div_const 2)
  have e : ∫ y, (C.f i y - C.sig i i * C.g i y ^ 2 / 2) ∂(occ X x ((m ^ 2 : ℕ) : ℝ) ω)
      = ((m ^ 2 : ℕ) : ℝ)⁻¹ * ∫ u in (0 : ℝ)..((m ^ 2 : ℕ) : ℝ),
          (C.f i (X x u.toNNReal ω) - C.sig i i * C.g i (X x u.toNNReal ω) ^ 2 / 2) :=
    occ_integral_cont X x ω (hcont ω) hs hT hcon
  rw [e]

end StochKolmogorov.Classify.HLglue

end Mod_HLglue

-- ===== tail =====

/-! Reduction glue for Lemma 5.8 (Hening-Nguyen, arXiv:1704.06984, p. 25). -/

section L58Glue

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.L58

open StochKolmogorov.Classify EthierKurtz


theorem isProb_occ {n : ℕ} {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) {T : ℝ} (hT : 0 < T) :
    IsProbabilityMeasure (occ X x T ω) := by
  have hm : Measurable fun s : ℝ => X x s.toNNReal ω :=
    (hc.comp continuous_real_toNNReal).measurable
  constructor
  unfold occ
  rw [Measure.smul_apply, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, smul_eq_mul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hT).ne' ENNReal.ofReal_ne_top]

/-- `U(ω)` is nonempty when the occupation measures are tight (Prokhorov). -/
theorem nonempty_of_tight {n : ℕ} {Ω : Type*} (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω)
    (hT : IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X x t ω}) :
    (limitSet X x ω).Nonempty := by
  let ts : ℕ → ℝ := fun k => (k : ℝ) + 1
  have h1 : ∀ k, 1 ≤ ts k := fun k => by
    show (1 : ℝ) ≤ (k : ℝ) + 1
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hts : Tendsto ts atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  let S : Set (ProbabilityMeasure (SDEState n)) :=
    {ν | ∃ t : ℝ, 1 ≤ t ∧ (ν : Measure (SDEState n)) = occ X x t ω}
  have hS : IsTightMeasureSet {((ν : ProbabilityMeasure (SDEState n)) : Measure (SDEState n)) |
      ν ∈ S} := by
    refine hT.subset ?_
    rintro _ ⟨ν, ⟨t, ht, he⟩, rfl⟩
    exact ⟨t, ht, he⟩
  have hK := isCompact_closure_of_isTightMeasureSet hS
  let νs : ℕ → ProbabilityMeasure (SDEState n) := fun k =>
    ⟨occ X x (ts k) ω, isProb_occ X x ω hc (lt_of_lt_of_le one_pos (h1 k))⟩
  have hmem : ∀ k, νs k ∈ closure S := fun k => subset_closure ⟨ts k, h1 k, rfl⟩
  obtain ⟨π, -, φ, hφ, hπ⟩ := hK.tendsto_subseq hmem
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hπ
  exact ⟨π, inferInstance, fun k => ts (φ k), fun k => h1 _, hts.comp hφ.tendsto_atTop,
    fun g => hint g⟩

/-- renormalising a finite positive-weight combination into an element of `conv S`. -/
theorem renorm {n : ℕ} (S : Set (Measure (SDEState n))) (t : Finset (Measure (SDEState n)))
    (p : Measure (SDEState n) → ℝ≥0) (ht : (↑t : Set (Measure (SDEState n))) ⊆ S)
    (hp : ∀ ν ∈ t, 0 < p ν) (hne : t.Nonempty) :
    ∃ ν' ∈ conv S, ∑ ν ∈ t, (p ν : ℝ≥0∞) • ν = ((∑ ν ∈ t, p ν : ℝ≥0) : ℝ≥0∞) • ν' ∧
      0 < ∑ ν ∈ t, p ν := by
  have hr0 : 0 < ∑ ν ∈ t, p ν := Finset.sum_pos hp hne
  refine ⟨∑ ν ∈ t, ((p ν / ∑ ν ∈ t, p ν : ℝ≥0) : ℝ≥0∞) • ν,
    ⟨t, fun ν => p ν / ∑ ν ∈ t, p ν, ht, fun ν hν => div_pos (hp ν hν) hr0, ?_, rfl⟩, ?_, hr0⟩
  · rw [← Finset.sum_div, div_self hr0.ne']
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [smul_smul, ← ENNReal.coe_mul]
    congr 2
    field_simp

/-- if `I_μ = ∅` then `M_μ = ∅`, hence `Conv(M_μ) = ∅`. -/
theorem conv_sub_empty {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (μ : Measure (SDEState n)) (h : supp μ = ∅) :
    conv (subErgodic P X μ) = ∅ := by
  have hS : subErgodic P X μ = ∅ := by
    ext ν
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨⟨⟨hprob, -⟩, -⟩, -⟩, h0⟩
    have hb : faceBdry μ = ∅ := by
      ext y
      simp [faceBdry, faceInt, h]
    rw [hb, Set.compl_empty] at h0
    haveI := hprob
    simp at h0
  rw [hS]
  ext π
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨s, p, hs, -, hsum, -⟩
  have hs0 : s = ∅ := by
    ext ν
    simp only [Finset.notMem_empty, iff_false]
    intro hν
    exact hs hν
  subst hs0
  simp at hsum

theorem core {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (μ : Measure (SDEState n)) (hμ : μ ∈ M1 P C X)
    (h51 : ∀ i ∈ supp μ,
      Integrable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) μ ∧ lyap C i μ = 0)
    (π : Measure (SDEState n)) (hπ : π ∈ conv (subErgodic P X μ ∪ {μ}))
    (hle : ∀ i, lyap C i π ≤ 0) : π = μ := by
  classical
  obtain ⟨s, p, hs, hp, hsum, rfl⟩ := hπ
  have key : ∀ (A : Measure (SDEState n)) (t : Finset (Measure (SDEState n))),
      (↑t : Set (Measure (SDEState n))) ⊆ subErgodic P X μ → t.Nonempty →
      (∀ ν ∈ t, 0 < p ν) →
      (∀ i ∈ supp μ, Integrable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) A ∧
        ∫ y, (C.f i y - C.sig i i * C.g i y ^ 2 / 2) ∂A = 0) →
      ¬ (∀ i, lyap C i (A + ∑ ν ∈ t, (p ν : ℝ≥0∞) • ν) ≤ 0) := by
    intro A t ht htne htp hA hall
    obtain ⟨ν', hν', heq, hr⟩ := renorm _ t p ht htp htne
    have hsupp : (supp μ).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [conv_sub_empty P X μ h0] at hν'
      exact hν'
    obtain ⟨i, hi, hpos⟩ := hμ.2.2 hsupp ν' hν'
    unfold lyap at hpos
    have hint : Integrable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) ν' := by
      by_contra hni
      rw [integral_undef hni] at hpos
      exact lt_irrefl _ hpos
    have h := hall i
    unfold lyap at h
    rw [heq, integral_add_measure (hA i hi).1 (hint.smul_measure ENNReal.coe_ne_top),
      integral_smul_measure, (hA i hi).2, ENNReal.coe_toReal, smul_eq_mul] at h
    have := mul_pos (NNReal.coe_pos.2 hr) hpos
    linarith
  by_cases hμs : μ ∈ s
  · by_cases hemp : (s.erase μ).Nonempty
    · exfalso
      refine key ((p μ : ℝ≥0∞) • μ) (s.erase μ) ?_ hemp
        (fun ν hν => hp ν (Finset.mem_of_mem_erase hν)) ?_ ?_
      · intro ν hν
        rcases hs (Finset.mem_of_mem_erase hν) with h | h
        · exact h
        · exact absurd (Set.mem_singleton_iff.1 h) (Finset.ne_of_mem_erase hν)
      · intro i hi
        refine ⟨(h51 i hi).1.smul_measure ENNReal.coe_ne_top, ?_⟩
        have h2 := (h51 i hi).2
        unfold lyap at h2
        rw [integral_smul_measure, h2, smul_zero]
      · intro i
        rw [Finset.add_sum_erase s (fun ν => (p ν : ℝ≥0∞) • ν) hμs]
        exact hle i
    · have he : s.erase μ = ∅ := Finset.not_nonempty_iff_eq_empty.1 hemp
      have hs1 : s = {μ} := by
        rw [← Finset.insert_erase hμs, he]
        rfl
      subst hs1
      simp only [Finset.sum_singleton] at hsum ⊢
      rw [hsum]
      simp
  · exfalso
    have hsub : (↑s : Set (Measure (SDEState n))) ⊆ subErgodic P X μ := by
      intro ν hν
      rcases hs hν with h | h
      · exact h
      · exact absurd (by rw [← Set.mem_singleton_iff.1 h]; exact hν) hμs
    have hne : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      simp at hsum
    refine key 0 s hsub hne hp (fun i _ => ⟨integrable_zero_measure, by simp⟩) ?_
    intro i
    rw [zero_add]
    exact hle i

theorem event_eq {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (μ : Measure (SDEState n))
    (hμ : μ ∈ M1 P C X)
    (h51 : ∀ i ∈ supp μ,
      Integrable (fun y => C.f i y - C.sig i i * C.g i y ^ 2 / 2) μ ∧ lyap C i μ = 0)
    (hgood : ∀ᵐ ω ∂P, (limitSet X x ω).Nonempty ∧
      ∀ π ∈ limitSet X x ω, ∀ i, lyap C i π ≤ 0) :
    P {ω | limitSet X x ω ⊆ conv (subErgodic P X μ ∪ {μ})}
      = P {ω | limitSet X x ω = {μ}} := by
  refine le_antisymm (measure_mono_ae ?_) (measure_mono ?_)
  · filter_upwards [hgood] with ω hω hsub
    exact Set.eq_singleton_iff_nonempty_unique_mem.2
      ⟨hω.1, fun π hπ => core P C X μ hμ h51 π (hsub hπ) (hω.2 π hπ)⟩
  · intro ω hω
    change limitSet X x ω = {μ} at hω
    change limitSet X x ω ⊆ _
    rw [hω, Set.singleton_subset_iff]
    exact ⟨{μ}, fun _ => 1, by simp, fun _ _ => one_pos, by simp, by simp⟩

/-- `δ₀` of (3.2) exists (copied from 1733f857_lib ItoLib.exists_isDelta0, Classify coefficients). -/
theorem exists_isDelta0 {n : ℕ} (C : Coeffs n) (γb : ℝ) (hγ : 0 < γb) :
    ∃ δ₀ : ℝ, IsDelta0 C γb δ₀ := by
  set S : ℝ := ∑ i, ∑ j, |C.sig i j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsij : ∀ i j, |C.sig i j| ≤ S := by
    intro i j
    calc |C.sig i j| ≤ ∑ j', |C.sig i j'| :=
          Finset.single_le_sum (f := fun j' => |C.sig i j'|) (fun _ _ => abs_nonneg _)
            (Finset.mem_univ j)
      _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', |C.sig i' j'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hden : 0 < 3 * S * n + 3 := by positivity
  refine ⟨γb / (3 * S * n + 3), div_pos hγ hden, ?_, fun x _ => ?_⟩
  · rw [div_lt_div_iff₀ hden two_pos]
    nlinarith [mul_nonneg hS0 (Nat.cast_nonneg (α := ℝ) n)]
  · set δ := γb / (3 * S * n + 3) with hδ
    have hδ0 : 0 ≤ δ := (div_pos hγ hden).le
    set G : ℝ := ∑ i, C.g i x ^ 2 with hG
    have hG0 : 0 ≤ G := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hterm : ∀ i j, |C.g i x * C.g j x * C.sig i j|
        ≤ S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by
      intro i j
      rw [abs_mul, abs_mul]
      have h1 : |C.g i x| * |C.g j x| ≤ (C.g i x ^ 2 + C.g j x ^ 2) / 2 := by
        nlinarith [sq_nonneg (|C.g i x| - |C.g j x|), sq_abs (C.g i x), sq_abs (C.g j x)]
      calc |C.g i x| * |C.g j x| * |C.sig i j| ≤ ((C.g i x ^ 2 + C.g j x ^ 2) / 2) * S :=
            mul_le_mul h1 (hsij i j) (abs_nonneg _) (by positivity)
        _ = S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) := by ring
    have hsum : ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| ≤ S * n * G := by
      calc ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
          ≤ ∑ i : Fin n, ∑ j : Fin n, S * ((C.g i x ^ 2 + C.g j x ^ 2) / 2) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
        _ = S * n * G := by
            simp only [← Finset.mul_sum, add_div, Finset.sum_add_distrib, Finset.sum_const,
              Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hG, ← Finset.sum_div]
            ring
    have hkey : δ * (3 * S * n + 3) = γb := by rw [hδ, div_mul_cancel₀ _ hden.ne']
    calc 3 * δ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| + δ * G
        ≤ 3 * δ * (S * n * G) + δ * G := by nlinarith
      _ ≤ δ * (3 * S * n + 3) * G := by nlinarith [mul_nonneg hδ0 hG0]
      _ = γb * G := by rw [hkey]

/-- Assumption 1.4 is monotone in `δ₁` (only large `‖x‖ ≥ 1` matters). -/
theorem a14_mono {n : ℕ} (C : Coeffs n) {δ₁ δ' : ℝ} (h14 : Assumption14 C δ₁)
    (hδ' : 0 < δ') (hle : δ' ≤ δ₁) : Assumption14 C δ' := by
  refine ⟨hδ', ?_⟩
  have hev : ∀ᶠ x in comap l1 atTop ⊓ 𝓟 (orthant n), 1 ≤ l1 x :=
    Filter.Eventually.filter_mono inf_le_left
      (Filter.tendsto_comap.eventually (eventually_ge_atTop 1))
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => ?_) (hev.mono fun x hx => ?_) h14.2
  · have hl : 0 ≤ l1 x := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hD : 0 ≤ 1 + ∑ i, (|C.f i x| + C.g i x ^ 2) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (sq_nonneg _))
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hl _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)) hD
  · have hD : 0 ≤ 1 + ∑ i, (|C.f i x| + C.g i x ^ 2) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun i _ =>
        add_nonneg (abs_nonneg _) (sq_nonneg _))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hx hle) (Finset.sum_nonneg fun i _ => sq_nonneg _)) hD

/-- `hmom` from the clause-1 moment bound of `Persist.lemma_3_2` (3.7). -/
theorem hmom_of {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (c : SDEState n) (hc : c ∈ openOrthant n)
    (γb δ₀ H₁ : ℝ) (hγ : 0 < γb) (hδ₀ : 0 < δ₀)
    (h1 : ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x t ω i) ^ δ₀) ∂P ≤
          ENNReal.ofReal (H₁ + (1 + ∑ i, c i * x i) ^ δ₀ * Real.exp (-δ₀ * γb * t))) :
    ∀ x ∈ openOrthant n, ∃ δ K : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x (N : ℝ≥0) ω i) ^ δ) ∂P ≤ ENNReal.ofReal K := by
  intro x hx
  refine ⟨δ₀, H₁ + (1 + ∑ i, c i * x i) ^ δ₀, hδ₀, fun N hN => ?_⟩
  have hN' : (0 : ℝ≥0) < (N : ℝ≥0) := by exact_mod_cast hN
  refine (h1 x (fun i => (hx i).le) (N : ℝ≥0) hN').trans (ENNReal.ofReal_le_ofReal ?_)
  have hA : 0 ≤ (1 + ∑ i, c i * x i) ^ δ₀ := Real.rpow_nonneg
    (add_nonneg zero_le_one (Finset.sum_nonneg fun i _ => (mul_pos (hc i) (hx i)).le)) _
  have hE : Real.exp (-δ₀ * γb * ((N : ℝ≥0) : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ δ₀ * γb * ((N : ℝ≥0) : ℝ) :=
      mul_nonneg (mul_nonneg hδ₀.le hγ.le) (NNReal.coe_nonneg _)
    linarith [neg_mul δ₀ γb]
  nlinarith [mul_le_mul_of_nonneg_left hE hA]

theorem stay_of {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hcl : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0))
    (x : SDEState n) (hx : x ∈ orthant n) : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n := by
  classical
  filter_upwards [hcl (Finset.univ.filter fun i => 0 < x i) x hx (fun i => by simp)] with ω hω t
  show ∀ i, 0 ≤ X x t ω i
  intro i
  by_cases hi : 0 < x i
  · exact ((hω t).1 i (by simp [hi])).le
  · rw [(hω t).2 i (by simp [hi])]

theorem stay_open_of {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hcl : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0))
    (x : SDEState n) (hx : x ∈ openOrthant n) : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ openOrthant n := by
  have hxo : x ∈ orthant n := fun i => (hx i).le
  filter_upwards [hcl Finset.univ x hxo (fun i => ⟨fun _ => hx i, fun _ => Finset.mem_univ i⟩)]
    with ω hω t
  exact fun i => (hω t).1 i (Finset.mem_univ i)

/-- Extinct's `δ₀` must also be `< 1`; shrinking `δ₀` keeps (3.2). -/
theorem delta_small {n : ℕ} (C : Coeffs n) {γb δ₀ : ℝ} (h : IsDelta0 C γb δ₀) :
    StochKolmogorov.Extinct.IsDelta0 ⟨C.f, C.g, C.Γ⟩ γb (min δ₀ (1 / 2)) := by
  refine ⟨lt_min h.1 (by norm_num), lt_min (lt_of_le_of_lt (min_le_left _ _) h.2.1)
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)), fun x hx => ?_⟩
  show 3 * min δ₀ (1 / 2) * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j|
      + min δ₀ (1 / 2) * ∑ i, C.g i x ^ 2 ≤ γb * ∑ i, C.g i x ^ 2
  have hS1 : 0 ≤ ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hS2 : 0 ≤ ∑ i, C.g i x ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hm : min δ₀ (1 / 2) ≤ δ₀ := min_le_left _ _
  have h3 := h.2.2 x hx
  have e1 := mul_le_mul_of_nonneg_right hm hS1
  have e2 := mul_le_mul_of_nonneg_right hm hS2
  linarith


theorem main_thm {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ μ ∈ M1 P C X, ∀ x ∈ openOrthant n,
      P {ω | limitSet X x ω ⊆ conv (subErgodic P X μ ∪ {μ})}
        = P {ω | limitSet X x ω = {μ}} := by
  intro μ hμ x hx
  have hC := hA.2.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  obtain ⟨δ₀, hδ₀⟩ := exists_isDelta0 C γb hγ
  have hcl : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0) :=
    (StochKolmogorov.Extinct.lemma_3_1 hn P ⟨C.f, C.g, C.Γ⟩ B X hX c γb hA _
      (delta_small C hδ₀)).2.1
  have hfc : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hC i).1.continuousOn
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  have hδ' : 0 < min δ₁ δ₀ := lt_min h14.1 hδ₀.1
  have h14' := a14_mono C h14 hδ' (min_le_left _ _)
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  have hstay := stay_of P X hcl x hxo
  obtain ⟨Kh, hKh, h54x⟩ :=
    (lemma_5_4 hn P C B X hX c γb hA δ₀ hδ₀ (min δ₁ δ₀) h14' (min_le_right _ _)).1
  have h56 := lemma_5_6 hn P C B X hX c γb hA δ₀ hδ₀ (min δ₁ δ₀) h14' (min_le_right _ _) x hxo
  have h57 := lemma_5_7 hn P C B X hX c γb hA δ₁ h14 x hxo
  obtain ⟨H₁, H₂, -, -, h1, -, -⟩ := StochKolmogorov.Persist.lemma_3_2 hn P ⟨C.f, C.g, C.Γ⟩
    B X hX c γb hA δ₀ hδ₀
  obtain ⟨δ, K, hδ, hmx⟩ := hmom_of P X c hc γb δ₀ H₁ hγ hδ₀.1 h1 x hx
  have hB := HB.log_le P X x c hc hsol.1 hδ hmx hstay
  have hL := HLglue.hL_of P C X c hc hfc hgc x hsol.2.1 hstay hδ'.le ⟨Kh, hKh, h54x x hxo⟩
    (log_lln_squares P C B X hX (fun i => ⟨hfc i, hgc i⟩) x hx (stay_open_of P X hcl x hx))
  have hlyap := UcGlue.lyap_nonpos P C X c (min δ₁ δ₀) hδ' hfc hgc x hsol.2.1 h56
    ⟨Kh, hKh, h54x x hxo⟩ (h57.mono fun ω h => h.2) hstay hL hB
  refine event_eq P C X x μ hμ (lemma_5_1 hn P C B X hX c γb hA μ hμ.1) ?_
  filter_upwards [h57, hlyap] with ω h1 h2
  exact ⟨nonempty_of_tight X x ω (hsol.2.1 ω) h1.1, h2⟩

end StochKolmogorov.Classify.L58

end L58Glue

open MeasureTheory ProbabilityTheory Filter StochKolmogorov.Classify EthierKurtz in
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) :
    ∀ μ ∈ M1 P C X, ∀ x ∈ openOrthant n,
      P {ω | limitSet X x ω ⊆ conv (subErgodic P X μ ∪ {μ})}
        = P {ω | limitSet X x ω = {μ}} := by
  exact StochKolmogorov.Classify.L58.main_thm hn P C B X hX c γb hA δ₁ h14
