-- Prove2me | solution 1 for StochKolmogorov.Classify.theorem_1_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-04T00:45:29.224338+00:00
-- url     : https://prove2.me/submissions/72bab805-9115-4670-bf86-c0904a614dd1

import Mathlib
import Definitions.Def_StochKolmogorov_Classify_Classification
import Definitions.Def_StochKolmogorov_Classify_Faces
import Definitions.Def_StochKolmogorov_Classify_Model
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Definitions.Def_TotalVariationDist
import Theorems.Thm_EthierKurtz_sde_markov_property_fd_conditional
import Theorems.Thm_StochKolmogorov_Classify_interior_open_set_reachable
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_4
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_6
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_7
import Theorems.Thm_StochKolmogorov_Classify_lemma_5_9
import Theorems.Thm_StochKolmogorov_Classify_log_lln_squares
import Theorems.Thm_StochKolmogorov_Extinct_lemma_3_1
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_face_box_tv_overlap
import Theorems.Thm_StochKolmogorov_Persist_lemma_3_2

set_option linter.all false
set_option Elab.async false


-- ===== module Assemble =====
section Mod_Assemble

/-! Top-level assembly of Theorem 1.3 (Hening-Nguyen, arXiv:1704.06984, Theorem 5.2 p. 28):
the conclusion follows from four facts:
* `M1` is finite (the paper sums over `M1`; finiteness of `M` = at most one ergodic measure per face),
* a.e. path lies in some `extinctEvent` (5.36),
* each `extinctEvent` is null-measurable,
* each `extinctEvent` has positive probability (last paragraph of the proof of Theorem 5.2). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Assemble

open StochKolmogorov.Classify EthierKurtz

/-- Two sink events for different measures are disjoint: `limitSet = {μ}` pins `μ`. -/
theorem extinctEvent_disjoint {n : ℕ} {Ω : Type*} (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n)
    {μ ν : Measure (SDEState n)} (h : μ ≠ ν) :
    Disjoint (extinctEvent C X x μ) (extinctEvent C X x ν) := by
  rw [Set.disjoint_left]
  intro ω h1 h2
  have e : ({μ} : Set (Measure (SDEState n))) = {ν} := h1.1.symm.trans h2.1
  exact h (Set.singleton_eq_singleton_iff.mp e)

theorem assemble {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfin : (M1 P C X).Finite)
    (hcover : ∀ x ∈ openOrthant n, ∀ᵐ ω ∂P, ∃ μ ∈ M1 P C X, ω ∈ extinctEvent C X x μ)
    (hnm : ∀ x ∈ openOrthant n, ∀ μ ∈ M1 P C X, NullMeasurableSet (extinctEvent C X x μ) P)
    (hpos : ∀ x ∈ openOrthant n, ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ)) :
    ∀ x ∈ openOrthant n,
      (∑' μ : M1 P C X, P (extinctEvent C X x (μ : Measure (SDEState n)))) = 1 ∧
        ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ) := by
  intro x hx
  refine ⟨?_, hpos x hx⟩
  haveI : Countable (M1 P C X) := hfin.countable.to_subtype
  have hdisj : Pairwise (Function.onFun (AEDisjoint P)
      (fun μ : M1 P C X => extinctEvent C X x (μ : Measure (SDEState n)))) := by
    intro μ ν hμν
    exact (extinctEvent_disjoint C X x (fun h => hμν (Subtype.ext h))).aedisjoint
  have hU := measure_iUnion₀ hdisj (fun μ : M1 P C X => hnm x hx μ.1 μ.2)
  rw [← hU]
  have hcompl : P (⋃ μ : M1 P C X, extinctEvent C X x (μ : Measure (SDEState n)))ᶜ = 0 := by
    have h0 := hcover x hx
    rw [ae_iff] at h0
    refine le_antisymm (le_trans (measure_mono ?_) h0.le) bot_le
    intro ω hω hex
    obtain ⟨μ, hμ, hω'⟩ := hex
    exact hω (Set.mem_iUnion.mpr ⟨⟨μ, hμ⟩, hω'⟩)
  have hae : (⋃ μ : M1 P C X, extinctEvent C X x (μ : Measure (SDEState n))) =ᵐ[P] Set.univ :=
    ae_eq_univ.mpr hcompl
  rw [measure_congr hae, measure_univ]

end StochKolmogorov.Classify.Assemble

end Mod_Assemble

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

-- ===== module K3 =====
section Mod_K3

/-! K3 of theorem_1_3 (8f909832): each sink event is null-measurable, GIVEN the a.e. cover (K2) and
injectivity of `supp` on the measures (K1b). Idea: `E_μ ⊆ A_μ := Z_μ ∩ L_μ` with `A_μ` measurable, where
`Z_μ` = "the Cesaro means of `min 1 |X_i|` along integers tend to 0 for `i ∉ supp μ`" and
`L_μ` = "they have positive limsup for `i ∈ supp μ`" (both read at RATIONAL times, so `A_μ` is the preimage of a measurable path set `Gam`). `A_μ ∩ E_ν = ∅` for `ν ≠ μ` (it forces
`supp μ = supp ν`), so `A_μ \ E_μ` lies in the null set where the cover fails. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K3

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- truncated coordinate size `min 1 |y_i|` -/
noncomputable def g (i : Fin n) (y : SDEState n) : ℝ := min 1 |y i|

theorem g_nonneg (i : Fin n) (y : SDEState n) : 0 ≤ g i y := le_min zero_le_one (abs_nonneg _)

theorem g_le_one (i : Fin n) (y : SDEState n) : g i y ≤ 1 := min_le_left _ _

theorem continuous_g (i : Fin n) : Continuous (g i : SDEState n → ℝ) :=
  continuous_const.min (PiLp.continuous_apply 2 _ i).abs

/-- `g i` as a bounded continuous function. -/
noncomputable def gB (i : Fin n) : SDEState n →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨g i, continuous_g i⟩ 1 (fun y z => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    rw [abs_le]
    constructor <;> linarith [g_nonneg i y, g_le_one i y, g_nonneg i z, g_le_one i z])

theorem gB_apply (i : Fin n) (y : SDEState n) : gB i y = g i y := rfl

/-- the running integral `∫₀ᵗ min 1 |X_i(s)| ds` -/
noncomputable def avg (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (i : Fin n)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∫ s in (0 : ℝ)..t, g i (X x s.toNNReal ω)

theorem abs_le_exp_log (y : ℝ) : |y| ≤ Real.exp (Real.log y) := by
  by_cases h : y = 0
  · simp [h]
  · rw [← Real.log_abs, Real.exp_log (abs_pos.mpr h)]

theorem intInt (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun t => X x t ω) (i : Fin n) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => g i (X x s.toNNReal ω)) volume a b :=
  ((continuous_g i).comp (hc.comp continuous_real_toNNReal)).intervalIntegrable a b


/-- the path read at rational times (negative rationals read time 0) -/
def rpath (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω) : ℚ → SDEState n :=
  fun q => X x (q : ℝ).toNNReal ω

/-- the measurable path set: `min 1 |f_i| → 0` along rationals for `i ∉ S`, positive limsup for `i ∈ S`. -/
def Gam (S : Finset (Fin n)) : Set (ℚ → SDEState n) :=
  {f | (∀ i, i ∉ S → ∀ m : ℕ, ∃ N : ℕ, ∀ q : ℚ, (N : ℚ) ≤ q → ((m : ℝ) + 1) * g i (f q) ≤ 1) ∧
    (∀ i, i ∈ S → ∃ m : ℕ, ∀ N : ℕ, ∃ q : ℚ, (N : ℚ) ≤ q ∧ 1 < ((m : ℝ) + 1) * g i (f q))}

theorem measurableSet_Gam (S : Finset (Fin n)) : MeasurableSet (Gam S) := by
  have hq : ∀ (i : Fin n) (q : ℚ), Measurable fun f : ℚ → SDEState n => ((0 : ℝ) + 1) * g i (f q) :=
    fun i q => ((continuous_g i).measurable.comp (measurable_pi_apply q)).const_mul _
  have hq' : ∀ (i : Fin n) (q : ℚ) (c : ℝ), Measurable fun f : ℚ → SDEState n => c * g i (f q) :=
    fun i q c => ((continuous_g i).measurable.comp (measurable_pi_apply q)).const_mul _
  have e : Gam S = (⋂ i, ⋂ (_ : i ∉ S), ⋂ m : ℕ, ⋃ N : ℕ, ⋂ q : ℚ, ⋂ (_ : (N : ℚ) ≤ q),
      {f : ℚ → SDEState n | ((m : ℝ) + 1) * g i (f q) ≤ 1}) ∩
      (⋂ i, ⋂ (_ : i ∈ S), ⋃ m : ℕ, ⋂ N : ℕ, ⋃ q : ℚ, ⋃ (_ : (N : ℚ) ≤ q),
      {f : ℚ → SDEState n | 1 < ((m : ℝ) + 1) * g i (f q)}) := by
    ext f; simp [Gam]
  rw [e]
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun m => MeasurableSet.iUnion fun N => MeasurableSet.iInter fun q =>
    MeasurableSet.iInter fun _ => measurableSet_le (hq' i q _) measurable_const)
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    MeasurableSet.iUnion fun m => MeasurableSet.iInter fun N => MeasurableSet.iUnion fun q =>
    MeasurableSet.iUnion fun _ => measurableSet_lt measurable_const (hq' i q _))

theorem measurable_rpath [MeasurableSpace Ω] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (hm : ∀ t, Measurable (X x t)) : Measurable (rpath X x) :=
  measurable_pi_lambda _ (fun q => hm _)

/-- `g_i` along the path tends to 0 for an extinct coordinate. -/
theorem g_tendsto_zero (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n)
    (μ : Measure (SDEState n)) {ω : Ω} (hω : ω ∈ extinctEvent C X x μ) {i : Fin n}
    (hi : i ∉ supp μ) : Tendsto (fun t : ℝ≥0 => g i (X x t ω)) atTop (𝓝 0) := by
  obtain ⟨hlim, hneg⟩ := hω.2 i hi
  have h1 : Tendsto (fun t : ℝ≥0 => Real.log (X x t ω i)) atTop atBot := by
    have h0 : Tendsto (fun t : ℝ≥0 => (t : ℝ) * (Real.log (X x t ω i) / t)) atTop atBot :=
      Filter.Tendsto.atTop_mul_neg hneg (NNReal.tendsto_coe_atTop.mpr tendsto_id) hlim
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have : (t : ℝ) ≠ 0 := by positivity
    field_simp
  have he : Tendsto (fun t : ℝ≥0 => Real.exp (Real.log (X x t ω i))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h1
  exact squeeze_zero (fun t => g_nonneg _ _)
    (fun t => (min_le_right _ _).trans (abs_le_exp_log _)) he

/-- density: a continuous bound at all rationals `≥ N` holds at all reals `≥ N`. -/
theorem le_of_rat {φ : ℝ → ℝ} (hφ : Continuous φ) {N : ℝ}
    (h : ∀ q : ℚ, N ≤ q → φ q ≤ 1) : ∀ s : ℝ, N ≤ s → φ s ≤ 1 := by
  intro s hs
  by_contra hlt
  push_neg at hlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hφ.continuousAt.eventually (lt_mem_nhds hlt))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + ε by linarith)
  have hd : dist (q : ℝ) s < ε := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  exact absurd (h q (hs.trans hq1.le)) (not_le.mpr (hball hd))

theorem extinct_sub_Gam (C : Coeffs n) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n)
    (hc : ∀ ω, Continuous fun t => X x t ω) (μ : Measure (SDEState n)) :
    extinctEvent C X x μ ⊆ rpath X x ⁻¹' Gam (supp μ) := by
  intro ω hω
  refine ⟨fun i hi m => ?_, fun i hi => ?_⟩
  · have h2 := g_tendsto_zero C X x μ hω hi
    have hpos : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := by positivity
    obtain ⟨T, hT⟩ := eventually_atTop.mp (h2.eventually (ge_mem_nhds hpos))
    refine ⟨⌈(T : ℝ)⌉₊, fun q hq => ?_⟩
    have hq' : (T : ℝ) ≤ q := (Nat.le_ceil _).trans (by exact_mod_cast hq)
    have hq0 : (0 : ℝ) ≤ q := T.2.trans hq'
    have hle : g i (X x (q : ℝ).toNNReal ω) ≤ ((m : ℝ) + 1)⁻¹ := by
      apply hT
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
      exact hq'
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    calc ((m : ℝ) + 1) * g i (rpath X x ω q) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left hle hm1.le
      _ = 1 := mul_inv_cancel₀ hm1.ne'
  · have hμ : μ ∈ limitSet X x ω := by rw [hω.1]; exact Set.mem_singleton μ
    obtain ⟨hprob, ts, hts1, htsT, hconv⟩ := hμ
    have hint : Integrable (g i) μ := (gB i).integrable μ
    have hc0 : 0 < ∫ y, g i y ∂μ := by
      rw [integral_pos_iff_support_of_nonneg (g_nonneg i) hint]
      have hne : μ {y : SDEState n | 0 < y i} ≠ 0 := by
        simpa [supp] using hi
      refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) (measure_mono ?_)
      intro y hy
      simp only [Function.mem_support, g, Set.mem_setOf_eq] at hy ⊢
      have : 0 < |y i| := abs_pos.mpr hy.ne'
      exact (lt_min one_pos this).ne'
    set c := ∫ y, g i y ∂μ with hcdef
    have hconv' := hconv (gB i)
    obtain ⟨m, hm⟩ := exists_nat_gt (8 / c)
    have hmc : 8 < ((m : ℝ) + 1) * c := by
      have := (div_lt_iff₀ hc0).mp (hm.trans (lt_add_one _))
      linarith
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hinv : ((m : ℝ) + 1)⁻¹ < c / 8 := by
      rw [inv_lt_iff_one_lt_mul₀ hm1]; nlinarith
    refine ⟨m, fun N => ?_⟩
    by_contra hno
    push_neg at hno
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hφ : Continuous fun s : ℝ => ((m : ℝ) + 1) * g i (X x s.toNNReal ω) :=
      continuous_const.mul ((continuous_g i).comp ((hc ω).comp continuous_real_toNNReal))
    have hall := le_of_rat hφ (N := (N : ℝ)) (fun q hq => hno q (by exact_mod_cast hq))
    have ev := (hconv'.eventually (lt_mem_nhds (half_lt_self hc0))).and
      (htsT.eventually_ge_atTop ((N : ℝ) + 1 + 3 * N / c))
    obtain ⟨k, hk1, hk2⟩ := ev.exists
    set t := ts k with ht
    have h3 : 0 ≤ 3 * (N : ℝ) / c := by positivity
    have tpos : 0 < t := by linarith
    have hNt : (N : ℝ) ≤ t := by linarith
    rw [show (∫ y, (gB i) y ∂μ) = c from rfl] at hk1
    rw [Shift.occ_integral X x ω (hc ω) tpos (gB i)] at hk1
    simp only [gB_apply] at hk1
    have hkav : c / 2 * t < avg X x i t ω := by
      unfold avg
      have := (lt_inv_mul_iff₀ tpos).mp hk1
      linarith
    have hsplit : avg X x i t ω = (∫ s in (0 : ℝ)..N, g i (X x s.toNNReal ω)) +
        ∫ s in (N : ℝ)..t, g i (X x s.toNNReal ω) :=
      (intervalIntegral.integral_add_adjacent_intervals (intInt X x ω (hc ω) i _ _)
        (intInt X x ω (hc ω) i _ _)).symm
    have hA : (∫ s in (0 : ℝ)..N, g i (X x s.toNNReal ω)) ≤ ∫ s in (0 : ℝ)..N, (1 : ℝ) :=
      intervalIntegral.integral_mono_on hN0 (intInt X x ω (hc ω) i _ _) intervalIntegrable_const
        (fun s _ => g_le_one _ _)
    have hB : (∫ s in (N : ℝ)..t, g i (X x s.toNNReal ω)) ≤ ∫ s in (N : ℝ)..t, ((m : ℝ) + 1)⁻¹ :=
      intervalIntegral.integral_mono_on hNt (intInt X x ω (hc ω) i _ _) intervalIntegrable_const
        (fun s hs => by
          have h1 := hall s hs.1
          calc g i (X x s.toNNReal ω) = ((m : ℝ) + 1)⁻¹ * (((m : ℝ) + 1) * g i (X x s.toNNReal ω)) := by
                field_simp
            _ ≤ ((m : ℝ) + 1)⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = ((m : ℝ) + 1)⁻¹ := mul_one _)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hA hB
    have hct : 3 * (N : ℝ) ≤ c * t := by
      have : 3 * (N : ℝ) / c ≤ t := by linarith
      rw [div_le_iff₀ hc0] at this; linarith
    have h5 : (t - N) * ((m : ℝ) + 1)⁻¹ ≤ t * (c / 8) := by
      have : (t - N) * ((m : ℝ) + 1)⁻¹ ≤ t * ((m : ℝ) + 1)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      exact this.trans (mul_le_mul_of_nonneg_left hinv.le tpos.le)
    have : c / 2 * t < (N - 0) * 1 + (t - N) * ((m : ℝ) + 1)⁻¹ := by linarith
    nlinarith

/-- K3, path form: under the cover and `supp`-injectivity, the sink event is a.e. the preimage of the
measurable path set `Gam (supp μ)` under the rational-time path. -/
theorem ae_eq_rpath [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n)
    (hc : ∀ ω, Continuous fun t => X x t ω)
    (S : Set (Measure (SDEState n)))
    (hinj : ∀ μ ∈ S, ∀ ν ∈ S, supp μ = supp ν → μ = ν)
    (hcover : ∀ᵐ ω ∂P, ∃ μ ∈ S, ω ∈ extinctEvent C X x μ) :
    ∀ μ ∈ S, rpath X x ⁻¹' Gam (supp μ) =ᵐ[P] extinctEvent C X x μ := by
  intro μ hμ
  have hEA := extinct_sub_Gam C X x hc μ
  have hdiff : rpath X x ⁻¹' Gam (supp μ) \ extinctEvent C X x μ ⊆
      {ω | ¬ ∃ ν ∈ S, ω ∈ extinctEvent C X x ν} := by
    rintro ω ⟨hωA, hωE⟩ ⟨ν, hν, hων⟩
    have hB := extinct_sub_Gam C X x hc ν hων
    have hs : supp μ = supp ν := by
      ext i
      constructor
      · intro hi
        by_contra hT
        obtain ⟨m, hm⟩ := hωA.2 i hi
        obtain ⟨N, hN⟩ := hB.1 i hT m
        obtain ⟨q, hq, hlt⟩ := hm N
        exact absurd (hN q hq) (not_le.mpr hlt)
      · intro hi
        by_contra hS
        obtain ⟨m, hm⟩ := hB.2 i hi
        obtain ⟨N, hN⟩ := hωA.1 i hS m
        obtain ⟨q, hq, hlt⟩ := hm N
        exact absurd (hN q hq) (not_le.mpr hlt)
    have := hinj μ hμ ν hν hs
    subst this
    exact hωE hων
  have hnull : P (rpath X x ⁻¹' Gam (supp μ) \ extinctEvent C X x μ) = 0 :=
    measure_mono_null hdiff (ae_iff.mp hcover)
  refine ae_eq_set.mpr ⟨hnull, ?_⟩
  rw [Set.diff_eq_empty.mpr hEA, measure_empty]

/-- K3 (modulo the cover K2 and `supp`-injectivity K1b). -/
theorem nullMeasurable_of_cover [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n)
    (hm : ∀ t, Measurable (X x t)) (hc : ∀ ω, Continuous fun t => X x t ω)
    (S : Set (Measure (SDEState n)))
    (hinj : ∀ μ ∈ S, ∀ ν ∈ S, supp μ = supp ν → μ = ν)
    (hcover : ∀ᵐ ω ∂P, ∃ μ ∈ S, ω ∈ extinctEvent C X x μ) :
    ∀ μ ∈ S, NullMeasurableSet (extinctEvent C X x μ) P := fun μ hμ =>
  ((measurableSet_Gam (supp μ)).preimage (measurable_rpath X x hm)).nullMeasurableSet.congr
    (ae_eq_rpath P C X x hc S hinj hcover μ hμ)

end StochKolmogorov.Classify.K3

end Mod_K3

-- ===== module PathMix =====
section Mod_PathMix

/-! PM2b of K4b (8f909832): a mixture identity `P(Y ∈ Γ) = ∫ P(Z y ∈ Γ) dκ(y)` (with measurable
`y ↦ P(Z y ∈ Γ)`) that holds on measurable cylinders of the path space `ι → E` holds on every
set of the product σ-algebra (Dynkin's π-λ theorem). Used with `ι = ℚ`, `Y` = the time-`t`-shifted
rational path of `X x`, `Z y` = the rational path of `X y`, `κ = trans P X t x`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.PathMix

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- the mixture identity for one set of a general space -/
def MixAt' {W : Type*} [MeasurableSpace W] (P : Measure Ω) (Y : Ω → W) (Z : E → Ω → W)
    (κ : Measure E) (Γ : Set W) : Prop :=
  Measurable (fun y => P (Z y ⁻¹' Γ)) ∧ P (Y ⁻¹' Γ) = ∫⁻ y, P (Z y ⁻¹' Γ) ∂κ

/-- generic Dynkin step: the mixture identity on a generating π-system extends to all measurable sets. -/
theorem mix_of_pi {W : Type*} [mW : MeasurableSpace W] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    [IsProbabilityMeasure κ] {𝒮 : Set (Set W)} (hgen : mW = generateFrom 𝒮) (hpi : IsPiSystem 𝒮)
    (hS : ∀ t ∈ 𝒮, MixAt' P Y Z κ t) :
    ∀ Γ : Set W, MeasurableSet Γ → MixAt' P Y Z κ Γ := by
  intro Γ hΓ
  refine MeasurableSpace.induction_on_inter (C := fun Γ _ => MixAt' P Y Z κ Γ)
    hgen hpi ?_ ?_ ?_ ?_ Γ hΓ
  · refine ⟨by simp, by simp⟩
  · intro t ht
    exact hS t ht
  · intro t htm hmix
    obtain ⟨hm, heq⟩ := hmix
    have hc : ∀ y, P (Z y ⁻¹' tᶜ) = 1 - P (Z y ⁻¹' t) := fun y => by
      rw [Set.preimage_compl, prob_compl_eq_one_sub (htm.preimage (hZ y))]
    refine ⟨?_, ?_⟩
    · simp_rw [hc]; exact hm.const_sub 1
    · rw [Set.preimage_compl, prob_compl_eq_one_sub (htm.preimage hY), heq]
      simp_rw [hc]
      have hle : (fun y => P (Z y ⁻¹' t)) ≤ᵐ[κ] fun _ => (1 : ℝ≥0∞) :=
        Eventually.of_forall fun y => prob_le_one
      have hfin : ∫⁻ y, P (Z y ⁻¹' t) ∂κ ≠ ∞ := by
        refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂κ) ?_ (lintegral_mono fun y => prob_le_one)
        simp
      rw [lintegral_sub hm hfin hle]
      simp
  · intro f hd hfm hmix
    have hZd : ∀ y, P (Z y ⁻¹' ⋃ i, f i) = ∑' i, P (Z y ⁻¹' f i) := fun y => by
      rw [Set.preimage_iUnion]
      exact measure_iUnion (fun i j hij => (hd hij).preimage _) (fun i => (hfm i).preimage (hZ y))
    refine ⟨?_, ?_⟩
    · simp_rw [hZd]; exact Measurable.tsum fun i => (hmix i).1
    · rw [Set.preimage_iUnion, measure_iUnion (fun i j hij => (hd hij).preimage _)
        (fun i => (hfm i).preimage hY)]
      simp_rw [hZd]
      rw [lintegral_tsum fun i => (hmix i).1.aemeasurable]
      exact tsum_congr fun i => (hmix i).2

/-- closed sets from bounded continuous test functions (thickened indicators). -/
theorem mix_closed {W : Type*} [PseudoEMetricSpace W] [MeasurableSpace W] [OpensMeasurableSpace W]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    [IsProbabilityMeasure κ]
    (hF : ∀ F : W →ᵇ ℝ≥0, (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (Z y ω) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (Y ω) : ℝ≥0∞) ∂P = ∫⁻ y, ∫⁻ ω, (F (Z y ω) : ℝ≥0∞) ∂P ∂κ)
    (C : Set W) (hC : IsClosed C) : MixAt' P Y Z κ C := by
  have δpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
  have δlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → W →ᵇ ℝ≥0 := fun k => thickenedIndicator (δpos k) C
  have hF' := fun k => hF (F k) ⟨_, lipschitzWith_thickenedIndicator (δpos k) C⟩
    (fun w => thickenedIndicator_le_one (δpos k) C w)
  have hFm : ∀ k, Measurable fun w => ((F k w : ℝ≥0) : ℝ≥0∞) :=
    fun k => measurable_coe_nnreal_ennreal.comp (F k).continuous.measurable
  have hlim : ∀ (V : Ω → W), Measurable V → Tendsto (fun k => ∫⁻ ω, (F k (V ω) : ℝ≥0∞) ∂P) atTop
      (𝓝 (P (V ⁻¹' C))) := by
    intro V hV
    have e : ∀ k, ∫⁻ ω, (F k (V ω) : ℝ≥0∞) ∂P = ∫⁻ w, (F k w : ℝ≥0∞) ∂(P.map V) :=
      fun k => (lintegral_map (hFm k) hV).symm
    simp_rw [e]
    rw [← Measure.map_apply hV hC.measurableSet]
    haveI : IsFiniteMeasure (P.map V) := Measure.isFiniteMeasure_map P V
    exact tendsto_lintegral_thickenedIndicator_of_isClosed (P.map V) hC δpos δlim
  have hmeas : Measurable fun y => P (Z y ⁻¹' C) :=
    measurable_of_tendsto_metrizable (fun k => (hF' k).1) (tendsto_pi_nhds.2 fun y => hlim _ (hZ y))
  refine ⟨hmeas, ?_⟩
  have h1 := hlim Y hY
  have h2 : Tendsto (fun k => ∫⁻ y, ∫⁻ ω, (F k (Z y ω) : ℝ≥0∞) ∂P ∂κ) atTop
      (𝓝 (∫⁻ y, P (Z y ⁻¹' C) ∂κ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) (fun k => (hF' k).1)
      (fun k => Eventually.of_forall fun y => ?_) (by simp) (Eventually.of_forall fun y => hlim _ (hZ y))
    calc ∫⁻ ω, (F k (Z y ω) : ℝ≥0∞) ∂P ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P :=
          lintegral_mono fun ω => by
            exact ENNReal.coe_le_one_iff.mpr (thickenedIndicator_le_one (δpos k) C (Z y ω))
      _ = 1 := by simp
  have h3 : Tendsto (fun k => ∫⁻ ω, (F k (Y ω) : ℝ≥0∞) ∂P) atTop
      (𝓝 (∫⁻ y, P (Z y ⁻¹' C) ∂κ)) := by
    simp_rw [(hF' _).2]; exact h2
  exact tendsto_nhds_unique h1 h3

/-- the mixture identity for one path set -/
def MixAt (P : Measure Ω) (Y : Ω → (ι → E)) (Z : E → Ω → (ι → E)) (κ : Measure E)
    (Γ : Set (ι → E)) : Prop :=
  Measurable (fun y => P (Z y ⁻¹' Γ)) ∧ P (Y ⁻¹' Γ) = ∫⁻ y, P (Z y ⁻¹' Γ) ∂κ

theorem mix_of_cylinders (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → (ι → E))
    (hY : Measurable Y) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    [IsProbabilityMeasure κ]
    (hcyl : ∀ (s : Finset ι) (S : Set (∀ i : s, E)), MeasurableSet S →
      MixAt P Y Z κ (cylinder s S)) :
    ∀ Γ : Set (ι → E), MeasurableSet Γ → MixAt P Y Z κ Γ := by
  intro Γ hΓ
  refine MeasurableSpace.induction_on_inter (C := fun Γ _ => MixAt P Y Z κ Γ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_ ?_ ?_ Γ hΓ
  · refine ⟨by simp, by simp⟩
  · intro t ht
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
    exact hcyl s S hS
  · intro t htm hmix
    obtain ⟨hm, heq⟩ := hmix
    have hc : ∀ y, P (Z y ⁻¹' tᶜ) = 1 - P (Z y ⁻¹' t) := fun y => by
      rw [Set.preimage_compl, prob_compl_eq_one_sub (htm.preimage (hZ y))]
    refine ⟨?_, ?_⟩
    · simp_rw [hc]; exact hm.const_sub 1
    · rw [Set.preimage_compl, prob_compl_eq_one_sub (htm.preimage hY), heq]
      simp_rw [hc]
      have hle : (fun y => P (Z y ⁻¹' t)) ≤ᵐ[κ] fun _ => (1 : ℝ≥0∞) :=
        Eventually.of_forall fun y => prob_le_one
      have hfin : ∫⁻ y, P (Z y ⁻¹' t) ∂κ ≠ ∞ := by
        refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂κ) ?_ (lintegral_mono fun y => prob_le_one)
        simp
      rw [lintegral_sub hm hfin hle]
      simp
  · intro f hd hfm hmix
    have hZd : ∀ y, P (Z y ⁻¹' ⋃ i, f i) = ∑' i, P (Z y ⁻¹' f i) := fun y => by
      rw [Set.preimage_iUnion]
      exact measure_iUnion (fun i j hij => (hd hij).preimage _) (fun i => (hfm i).preimage (hZ y))
    refine ⟨?_, ?_⟩
    · simp_rw [hZd]; exact Measurable.tsum fun i => (hmix i).1
    · rw [Set.preimage_iUnion, measure_iUnion (fun i j hij => (hd hij).preimage _)
        (fun i => (hfm i).preimage hY)]
      simp_rw [hZd]
      rw [lintegral_tsum fun i => (hmix i).1.aemeasurable]
      exact tsum_congr fun i => (hmix i).2


/-- PM2 (finite-dimensional test functions to the path σ-algebra). -/
theorem mix_all [PseudoMetricSpace E] [SecondCountableTopology E]
    [BorelSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → (ι → E))
    (hY : Measurable Y) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    [IsProbabilityMeasure κ]
    (hFD : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (s.restrict (Y ω)) : ℝ≥0∞) ∂P =
        ∫⁻ y, ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P ∂κ) :
    ∀ Γ : Set (ι → E), MeasurableSet Γ → MixAt P Y Z κ Γ := by
  refine mix_of_cylinders P Y hY Z hZ κ fun s S hS => ?_
  have hYs : Measurable fun ω => s.restrict (Y ω) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hY
  have hZs : ∀ y, Measurable fun ω => s.restrict (Z y ω) :=
    fun y => measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (hZ y)
  have hgen : (inferInstance : MeasurableSpace (∀ i : s, E)) = generateFrom {C | IsClosed C} :=
    BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
  exact mix_of_pi P _ hYs _ hZs κ hgen isPiSystem_isClosed
    (fun C hC => mix_closed P _ hYs _ hZs κ (hFD s) C hC) S hS

end StochKolmogorov.Classify.PathMix

end Mod_PathMix

-- ===== module K4 =====
section Mod_K4

/-! K4 of theorem_1_3 (8f909832): every sink has positive probability from every interior point, from
* `hinj` (K1b), `hcover` (K2), `h59` (sibling lemma_5_9), `hreach` (K4a irreducibility),
* `hFD` (PM1: finite-dimensional Markov identity for the rational path after time `t`).
Route: `E_x =ᵐ {shifted rational path ∈ Gam}` (K3 + path-shift invariance), the mixture identity on
the path σ-algebra (PathMix), and `P(E_y) ≥ 1/2` on an open box inside `Kbox μ 2 Δ`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K4

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- the rational-time path after time `t` -/
def shiftPath (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0) (ω : Ω) :
    ℚ → SDEState n :=
  fun q => X x (t + (q : ℝ).toNNReal) ω

open Classical in
/-- the rational-time path from `y` (a constant path off the orthant, where `X y` is unconstrained) -/
noncomputable def Zf (X : SDEState n → ℝ≥0 → Ω → SDEState n) (y : SDEState n) (ω : Ω) :
    ℚ → SDEState n :=
  if y ∈ orthant n then K3.rpath X y ω else fun _ => y

/-- PM1, the finite-dimensional Markov identity (open child). -/
def FDMarkov [MeasurableSpace Ω] (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ x ∈ openOrthant n, ∀ (t : ℝ≥0) (s : Finset ℚ) (F : (∀ i : s, SDEState n) →ᵇ ℝ≥0),
    (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
    Measurable (fun y => ∫⁻ ω, (F (s.restrict (Zf X y ω)) : ℝ≥0∞) ∂P) ∧
    ∫⁻ ω, (F (s.restrict (shiftPath X x t ω)) : ℝ≥0∞) ∂P =
      ∫⁻ y, ∫⁻ ω, (F (s.restrict (Zf X y ω)) : ℝ≥0∞) ∂P ∂(trans P X t x)

theorem pos_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (hinj : ∀ μ ∈ M1 P C X, ∀ ν ∈ M1 P C X, supp μ = supp ν → μ = ν)
    (hcover : ∀ y ∈ openOrthant n, ∀ᵐ ω ∂P, ∃ μ ∈ M1 P C X, ω ∈ extinctEvent C X y μ)
    (h59 : ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ y ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X y μ)).toReal)
    (hreach : ∀ x ∈ openOrthant n, ∀ U : Set (SDEState n), IsOpen U → U.Nonempty →
      U ⊆ openOrthant n → ∃ t : ℝ≥0, 0 < P {ω | X x t ω ∈ U})
    (hFD : FDMarkov P X) :
    ∀ x ∈ openOrthant n, ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ) := by
  intro x hx μ hμ
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  obtain ⟨Δ, hΔ, h5⟩ := h59 μ hμ 2 (by norm_num) (1 / 2) (by norm_num)
  set U : Set (SDEState n) := ⋂ i, {y : SDEState n | (i ∈ supp μ → 1 / 2 < y i ∧ y i < 2) ∧
    (i ∉ supp μ → 0 < y i ∧ y i < Δ)} with hUdef
  have hci : ∀ i : Fin n, Continuous fun y : SDEState n => y i := fun i => PiLp.continuous_apply 2 _ i
  have hUo : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases h : i ∈ supp μ
    · simp only [h, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isOpen_lt continuous_const (hci i)).inter (isOpen_lt (hci i) continuous_const)
    · simp only [h, IsEmpty.forall_iff, true_and, not_false_eq_true, forall_const]
      exact (isOpen_lt continuous_const (hci i)).inter (isOpen_lt (hci i) continuous_const)
  have hUint : U ⊆ openOrthant n := by
    intro y hy i
    have := Set.mem_iInter.mp hy i
    by_cases h : i ∈ supp μ
    · linarith [(this.1 h).1]
    · exact (this.2 h).1
  have hUK : U ⊆ Kbox μ 2 Δ := by
    intro y hy
    refine ⟨hUint hy, fun i hi => ?_, fun i hi => ((Set.mem_iInter.mp hy i).2 hi).2⟩
    have := (Set.mem_iInter.mp hy i).1 hi
    constructor
    · norm_num; linarith [this.1]
    · norm_num; linarith [this.2]
  have hUne : U.Nonempty := by
    refine ⟨WithLp.toLp 2 (fun i => if i ∈ supp μ then (1 : ℝ) else Δ / 2), Set.mem_iInter.mpr fun i => ?_⟩
    by_cases h : i ∈ supp μ
    · simp only [PiLp.toLp_apply, if_pos h, Set.mem_setOf_eq]
      exact ⟨fun _ => ⟨by norm_num, by norm_num⟩, fun h' => absurd h h'⟩
    · simp only [PiLp.toLp_apply, if_neg h, Set.mem_setOf_eq]
      exact ⟨fun h' => absurd h' h, fun _ => ⟨by linarith, by linarith⟩⟩
  obtain ⟨t, ht⟩ := hreach x hx U hUo hUne hUint
  set Γ := K3.Gam (supp μ) with hΓ
  haveI : IsProbabilityMeasure (trans P X t x) :=
    Measure.isProbabilityMeasure_map (hsol.1 t).aemeasurable
  have hYm : Measurable (shiftPath X x t) := measurable_pi_lambda _ fun q => hsol.1 _
  have hZm : ∀ y, Measurable (Zf X y) := by
    intro y
    unfold Zf
    split_ifs with h
    · exact K3.measurable_rpath X y (hX.2.2 y h).1
    · exact measurable_const
  have hmix := PathMix.mix_all P (shiftPath X x t) hYm (Zf X) hZm (trans P X t x) (hFD x hx t) Γ
    (K3.measurableSet_Gam _)
  -- the sink event from `x` is a.e. the shifted rational path in `Γ`
  let X' : SDEState n → ℝ≥0 → Ω → SDEState n := fun _ s ω => X x (t + s) ω
  have hc' : ∀ ω, Continuous fun s => X' x s ω := fun ω =>
    (hsol.2.1 ω).comp (continuous_const.add continuous_id)
  have hEq : ∀ ν ω, ω ∈ extinctEvent C X' x ν ↔ ω ∈ extinctEvent C X x ν := fun ν ω =>
    Shift.extinctEvent_shift C X X' x x ν ω ω t (fun s => rfl) (hsol.2.1 ω)
  have hcov' : ∀ᵐ ω ∂P, ∃ ν ∈ M1 P C X, ω ∈ extinctEvent C X' x ν :=
    (hcover x hx).mono fun ω ⟨ν, hν, h⟩ => ⟨ν, hν, (hEq ν ω).2 h⟩
  have hae := K3.ae_eq_rpath P C X' x hc' (M1 P C X) hinj hcov' μ hμ
  have hset : extinctEvent C X' x μ = extinctEvent C X x μ := Set.ext (hEq μ)
  have hrp : K3.rpath X' x = shiftPath X x t := rfl
  rw [hset, hrp] at hae
  -- on `U` the sink probability is at least 1/2
  have hy : ∀ y ∈ U, ENNReal.ofReal (1 / 2) ≤ P (Zf X y ⁻¹' Γ) := by
    intro y hyU
    have hyo : y ∈ orthant n := fun i => (hUint hyU i).le
    have hZ : Zf X y = K3.rpath X y := by funext ω; simp only [Zf, if_pos hyo]
    rw [hZ, measure_congr (K3.ae_eq_rpath P C X y (hX.2.2 y hyo).2.1 (M1 P C X) hinj
      (hcover y (hUint hyU)) μ hμ)]
    have := h5 y (hUK hyU)
    exact ENNReal.ofReal_le_of_le_toReal (by linarith)
  have hκU : trans P X t x U ≠ 0 := by
    unfold trans
    rw [Measure.map_apply (hsol.1 t) hUo.measurableSet]
    exact ht.ne'
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) * trans P X t x U :=
        ENNReal.mul_pos (by simp) hκU
    _ = ∫⁻ _ in U, ENNReal.ofReal (1 / 2) ∂(trans P X t x) := (setLIntegral_const U _).symm
    _ ≤ ∫⁻ y in U, P (Zf X y ⁻¹' Γ) ∂(trans P X t x) := setLIntegral_mono hmix.1 hy
    _ ≤ ∫⁻ y, P (Zf X y ⁻¹' Γ) ∂(trans P X t x) := setLIntegral_le_lintegral U _
    _ = P (shiftPath X x t ⁻¹' Γ) := hmix.2.symm
    _ = P (extinctEvent C X x μ) := measure_congr hae

end StochKolmogorov.Classify.K4

end Mod_K4

-- ===== module FDM =====
section Mod_FDM

/-! PM1 glue of K4b (8f909832): `K4.FDMarkov` (finite-dimensional Markov identity of the rational
path after time `t`, for Lipschitz test functions bounded by 1) from the child theorem
`EthierKurtz.sde_markov_property_fd_conditional` (case q = 0), applied to Lipschitz truncations of the Kolmogorov
coefficients (copied from the accepted `Persist.markov_property` reduction, namespace renamed). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDM

open StochKolmogorov.Classify EthierKurtz

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

variable {d : ℕ}
theorem coord_abs_le_state (x : SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i; rwa [Real.norm_eq_abs] at this

theorem lipOn_of_locLip_compact {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {s K : Set α} {f : α → β} (hf : LocallyLipschitzOn s f) (hK : IsCompact K) (hKs : K ⊆ s) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ y ∈ K, dist (f x) (f y) ≤ L * dist x y := by
  classical
  have hloc : ∀ x : K, ∃ r > (0 : ℝ), ∃ L : ℝ≥0, LipschitzOnWith L f (Metric.ball (x : α) r ∩ s) := by
    intro x
    obtain ⟨L, t, ht, hL⟩ := hf (hKs x.2)
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhdsWithin_iff.1 ht
    exact ⟨r, hr, L, hL.mono hrt⟩
  choose r hr L hL using hloc
  have hcov : K ⊆ ⋃ x : K, Metric.ball (x : α) (r x / 2) := fun y hy =>
    Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (hr _))⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover _ (fun _ => Metric.isOpen_ball) hcov
  -- bound on `f` over `K`
  have hbdd : Bornology.IsBounded (f '' K) :=
    (hK.image_of_continuousOn (hf.continuousOn.mono hKs)).isBounded
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.1 hbdd
  by_cases hTn : T.Nonempty
  · set δ : ℝ := T.inf' hTn (fun x => r x / 2) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]; exact fun x _ => half_pos (hr x)
    set Lm : ℝ≥0 := T.sup L
    refine ⟨Lm + max C 0 / δ, by positivity, fun x hx y hy => ?_⟩
    by_cases hxy : dist x y < δ
    · obtain ⟨z, hzT, hxz⟩ : ∃ z ∈ T, x ∈ Metric.ball (z : α) (r z / 2) := by
        have := hT hx; simp only [Set.mem_iUnion] at this
        obtain ⟨z, hz, h⟩ := this; exact ⟨z, hz, h⟩
      have hδz : δ ≤ r z / 2 := Finset.inf'_le _ hzT
      have hx' : x ∈ Metric.ball (z : α) (r z) ∩ s :=
        ⟨Metric.ball_subset_ball (by linarith [hr z]) hxz, hKs hx⟩
      have hy' : y ∈ Metric.ball (z : α) (r z) ∩ s := by
        refine ⟨?_, hKs hy⟩
        rw [Metric.mem_ball] at hxz ⊢
        calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
          _ < δ + r z / 2 := by rw [dist_comm]; exact add_lt_add hxy hxz
          _ ≤ r z := by linarith
      have h1 := (hL z).dist_le_mul x hx' y hy'
      have h2 : (L z : ℝ) ≤ Lm := by exact_mod_cast Finset.le_sup (f := L) hzT
      have h3 : 0 ≤ max C 0 / δ * dist x y := by positivity
      nlinarith [dist_nonneg (x := x) (y := y)]
    · replace hxy := not_lt.1 hxy
      have h1 : dist (f x) (f y) ≤ max C 0 :=
        (hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (le_max_left _ _)
      have h2 : max C 0 ≤ max C 0 / δ * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      have h3 : 0 ≤ (Lm : ℝ) * dist x y := by positivity
      nlinarith
  · have hK0 : K = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hTn
      subst hTn; simpa using hT
    exact ⟨0, le_rfl, fun x hx => by simp [hK0] at hx⟩


/-- Coordinatewise 1-Lipschitz maps are 1-Lipschitz in the Euclidean norm. -/
theorem norm_sub_le_of_coord {x y x' y' : SDEState d} (h : ∀ i, |x' i - y' i| ≤ |x i - y i|) :
    ‖x' - y'‖ ≤ ‖x - y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [PiLp.sub_apply, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem clamp1_lip (M a b : ℝ) : |max (-M) (min M a) - max (-M) (min M b)| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b); have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- Coordinate clamp to the box `[-M, M]^d`. -/
noncomputable def clampM (M : ℝ) (x : SDEState d) : SDEState d :=
  WithLp.toLp 2 (fun i => max (-M) (min M (x i)))

theorem clampM_apply (M : ℝ) (x : SDEState d) (i : Fin d) :
    clampM M x i = max (-M) (min M (x i)) := rfl

theorem clampM_lip (M : ℝ) (x y : SDEState d) : ‖clampM M x - clampM M y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by rw [clampM_apply, clampM_apply]; exact clamp1_lip _ _ _

theorem clampM_abs_le {M : ℝ} (hM : 0 ≤ M) (x : SDEState d) (i : Fin d) : |clampM M x i| ≤ M := by
  rw [clampM_apply, abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem clampM_eq {M : ℝ} {x : SDEState d} (hx : ‖x‖ ≤ M) : clampM M x = x := by
  ext i
  rw [clampM_apply]
  have := (coord_abs_le_state x i).trans hx
  rw [abs_le] at this
  rw [min_eq_right this.2, max_eq_right this.1]

theorem norm_le_card_mul {M : ℝ} {x : SDEState d} (hx : ∀ i, |x i| ≤ M) : ‖x‖ ≤ d * M := by
  calc ‖x‖ ≤ ∑ i, |x i| := euc_norm_le_sum' x
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hx i
    _ = d * M := by simp

/-- b9: a truncation family for coordinate functions that are Lipschitz on every box. -/
theorem trunc_family {ι : Type*} [Fintype ι] (φ : ι → SDEState d → ℝ)
    (hL : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ k x y, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |φ k x - φ k y| ≤ L * ‖x - y‖) :
    ∃ (s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι) (S L : ℕ → ℝ), (∀ R, Continuous (s₁ R)) ∧
      (∀ R, 0 ≤ L R) ∧ (∀ R x, ‖s₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = WithLp.toLp 2 (fun k => φ k x)) := by
  classical
  choose Lb hLb0 hLb using fun R : ℕ => hL ((R : ℝ) + 3) (by positivity)
  set s₁ : ℕ → SDEState d → EuclideanSpace ℝ ι :=
    fun R x => WithLp.toLp 2 (fun k => φ k (clampM ((R : ℝ) + 3) x)) with hs₁
  have hM : ∀ R : ℕ, (0 : ℝ) ≤ (R : ℝ) + 3 := fun R => by positivity
  have hlip : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ (Fintype.card ι * Lb R) * ‖x - y‖ := by
    intro R x y
    calc ‖s₁ R x - s₁ R y‖ ≤ ∑ k, |(s₁ R x - s₁ R y) k| := euc_norm_le_sum' _
      _ ≤ ∑ _k : ι, Lb R * ‖x - y‖ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁, PiLp.sub_apply]
          exact (hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) y)).trans
            (mul_le_mul_of_nonneg_left (clampM_lip _ _ _) (hLb0 R))
      _ = (Fintype.card ι * Lb R) * ‖x - y‖ := by simp [mul_assoc]
  refine ⟨s₁, fun R => ∑ k : ι, (|φ k (clampM ((R : ℝ) + 3) 0)| + Lb R * (2 * (d * ((R : ℝ) + 3)))),
    fun R => Fintype.card ι * Lb R, fun R => ?_, fun R => by have := hLb0 R; positivity,
    fun R x => ?_, hlip, fun R x hx => ?_⟩
  · exact LipschitzWith.continuous (K := ⟨Fintype.card ι * Lb R, by have := hLb0 R; positivity⟩)
      (LipschitzWith.of_dist_le_mul fun x y => by
        rw [dist_eq_norm, dist_eq_norm]; exact hlip R x y)
  · calc ‖s₁ R x‖ ≤ ∑ k, |s₁ R x k| := euc_norm_le_sum' _
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro k _
          simp only [hs₁]
          set M : ℝ := (R : ℝ) + 3
          have hc := hLb R k _ _ (clampM_abs_le (hM R) x) (clampM_abs_le (hM R) 0)
          have hn : ‖clampM M x - clampM M 0‖ ≤ 2 * (d * M) := by
            calc ‖clampM M x - clampM M 0‖ ≤ ‖clampM M x‖ + ‖clampM M 0‖ := norm_sub_le _ _
              _ ≤ d * M + d * M := add_le_add (norm_le_card_mul (clampM_abs_le (hM R) x))
                  (norm_le_card_mul (clampM_abs_le (hM R) 0))
              _ = 2 * (d * M) := by ring
          have := mul_le_mul_of_nonneg_left hn (hLb0 R)
          have h3 := abs_sub_abs_le_abs_sub (φ k (clampM M x)) (φ k (clampM M 0))
          linarith
  · simp only [hs₁, clampM_eq hx]

variable {n : ℕ}

theorem posPart_apply' (x : SDEState n) (i : Fin n) : posPart x i = max (x i) 0 := rfl

theorem posPart_lip (x y : SDEState n) : ‖posPart x - posPart y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by
    rw [posPart_apply', posPart_apply']; exact abs_max_sub_max_le_abs _ _ _

theorem posPart_mem_orthant (x : SDEState n) : posPart x ∈ orthant n := fun i => by
  rw [posPart_apply']; exact le_max_right _ _

theorem continuous_posPart : Continuous (posPart (n := n)) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact posPart_lip x y)

/-- A locally Lipschitz function on the orthant, read at `x⁺`, is Lipschitz and bounded on boxes. -/
theorem locLip_posPart_box {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L G : ℝ, 0 ≤ L ∧ 0 ≤ G ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |h (posPart x) - h (posPart y)| ≤ L * ‖x - y‖ ∧ |h (posPart x)| ≤ G := by
  set K : Set (SDEState n) := {y | ∀ i, 0 ≤ y i ∧ y i ≤ M} with hKdef
  have hKc : IsClosed K := by
    have : K = ⋂ i, ({y : SDEState n | 0 ≤ y i} ∩ {y | y i ≤ M}) := by
      ext y; simp [hKdef, forall_and]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  have hKb : Bornology.IsBounded K := (Metric.isBounded_closedBall (x := (0 : SDEState n))
      (r := n * M)).subset fun y hy => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact norm_le_card_mul fun i => by rw [abs_of_nonneg (hy i).1]; exact (hy i).2
  have hKo : K ⊆ orthant n := fun y hy i => (hy i).1
  obtain ⟨L, hL0, hL⟩ := lipOn_of_locLip_compact hh (Metric.isCompact_of_isClosed_isBounded hKc hKb) hKo
  have hpK : ∀ x : SDEState n, (∀ i, |x i| ≤ M) → posPart x ∈ K := fun x hx i => by
    rw [posPart_apply']
    exact ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hx i)) hM⟩
  have h0 : ∀ i, |(0 : SDEState n) i| ≤ M := fun i => by simpa using hM
  refine ⟨L, L * (n * M) + |h (posPart 0)|, hL0, by positivity, fun x y hx hy => ⟨?_, ?_⟩⟩
  · have := hL _ (hpK x hx) _ (hpK y hy)
    rw [Real.dist_eq, dist_eq_norm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (posPart_lip x y) hL0)
  · have h1 := hL _ (hpK x hx) _ (hpK 0 h0)
    rw [Real.dist_eq, dist_eq_norm] at h1
    have h2 : ‖posPart x - posPart (0 : SDEState n)‖ ≤ n * M := by
      calc ‖posPart x - posPart (0 : SDEState n)‖ ≤ ‖x - 0‖ := posPart_lip x 0
        _ = ‖x‖ := by rw [sub_zero]
        _ ≤ n * M := norm_le_card_mul hx
    have h3 := abs_sub_abs_le_abs_sub (h (posPart x)) (h (posPart 0))
    have h4 := mul_le_mul_of_nonneg_left h2 hL0
    linarith

/-- Products `x_i · h(x⁺) · c` are Lipschitz on boxes. -/
theorem prod_box_lip {h : SDEState n → ℝ} (hh : LocallyLipschitzOn (orthant n) h) (c : ℝ) (i : Fin n)
    {M : ℝ} (hM : 0 ≤ M) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : SDEState n, (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x i * h (posPart x) * c - y i * h (posPart y) * c| ≤ L * ‖x - y‖ := by
  obtain ⟨L, G, hL0, hG0, hLG⟩ := locLip_posPart_box hh hM
  refine ⟨|c| * (M * L + G), by positivity, fun x y hx hy => ?_⟩
  obtain ⟨h1, -⟩ := hLG x y hx hy
  obtain ⟨-, h2⟩ := hLG y x hy hx
  have hxy : |x i - y i| ≤ ‖x - y‖ := by
    have := coord_abs_le_state (x - y) i; rwa [PiLp.sub_apply] at this
  have e : x i * h (posPart x) * c - y i * h (posPart y) * c =
      c * (x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)) := by ring
  rw [e, abs_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  calc |x i * (h (posPart x) - h (posPart y)) + h (posPart y) * (x i - y i)|
      ≤ |x i| * |h (posPart x) - h (posPart y)| + |h (posPart y)| * |x i - y i| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ M * (L * ‖x - y‖) + G * ‖x - y‖ := by
        gcongr
        · exact hx i
    _ = (M * L + G) * ‖x - y‖ := by ring

/-- b11: the Kolmogorov coefficients are continuous and have truncation families as needed by
`markov_core`. -/
theorem kolm_trunc (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (fun x : SDEState n => diffusion C (0, x)) ∧
    Continuous (fun x : SDEState n => drift C (0, x)) ∧
    ∃ (s₁ : ℕ → SDEState n → SDEDiffusion n) (b₁ : ℕ → SDEState n → SDEState n) (S L : ℕ → ℝ),
      (∀ R, Continuous (s₁ R)) ∧ (∀ R, Continuous (b₁ R)) ∧ (∀ R, 0 ≤ L R) ∧
      (∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R) ∧
      (∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖) ∧
      (∀ (R : ℕ) (x : SDEState n), ‖x‖ ≤ (R : ℝ) + 3 →
        s₁ R x = diffusion C (0, x) ∧ b₁ R x = drift C (0, x)) := by
  have hgc : ∀ i, Continuous fun x : SDEState n => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hfc : ∀ i, Continuous fun x : SDEState n => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  refine ⟨(PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      (((PiLp.continuous_apply 2 _ k.1).mul (hgc k.1)).mul continuous_const)),
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
      ((PiLp.continuous_apply 2 _ k).mul (hfc k))), ?_⟩
  -- the two coordinate families
  have hLs : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n × Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k.1 * C.g k.1 (posPart x) * C.Γ k.2 k.1 - y k.1 * C.g k.1 (posPart y) * C.Γ k.2 k.1|
        ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n × Fin n => prod_box_lip (hC k.1).2 (C.Γ k.2 k.1) k.1 hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  have hLb : ∀ M : ℝ, 0 ≤ M → ∃ L, 0 ≤ L ∧ ∀ (k : Fin n) (x y : SDEState n),
      (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) →
      |x k * C.f k (posPart x) * 1 - y k * C.f k (posPart y) * 1| ≤ L * ‖x - y‖ := by
    intro M hM
    choose L hL0 hL using fun k : Fin n => prod_box_lip (hC k).1 1 k hM
    refine ⟨∑ k, L k, Finset.sum_nonneg fun k _ => hL0 k, fun k x y hx hy => ?_⟩
    exact (hL k x y hx hy).trans (mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun k _ => hL0 k) (Finset.mem_univ k)) (norm_nonneg _))
  obtain ⟨s₁, S1, L1, hs1c, hL1, hS1, hl1, he1⟩ := trunc_family _ hLs
  obtain ⟨b₁, S2, L2, hb1c, hL2, hS2, hl2, he2⟩ := trunc_family _ hLb
  refine ⟨s₁, b₁, fun R => max (S1 R) (S2 R), fun R => max (L1 R) (L2 R), hs1c, hb1c,
    fun R => (hL1 R).trans (le_max_left _ _), fun R x => ⟨(hS1 R x).trans (le_max_left _ _),
      (hS2 R x).trans (le_max_right _ _)⟩, fun R x y => ⟨(hl1 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)), (hl2 R x y).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))⟩, fun R x hx => ⟨?_, ?_⟩⟩
  · rw [he1 R x hx]; rfl
  · rw [he2 R x hx]; simp only [mul_one]; rfl

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

variable {n : ℕ}

theorem fdMarkov_of {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n) :
    K4.FDMarkov P X := by
  classical
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := kolm_trunc C hC
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hXs y hy
  intro x hx t s G hGL hG1
  obtain ⟨KG, hGL⟩ := hGL
  have hxo : x ∈ orthant n := fun i => (hx i).le
  let e : Fin s.card ≃ s := s.equivFin.symm
  let τ : Fin s.card → ℝ≥0 := fun i => (((e i : ℚ) : ℝ)).toNNReal
  let F : (Fin s.card → SDEState n) → ℝ := fun v => ((G (fun j => v (e.symm j)) : ℝ≥0) : ℝ)
  have hFc : Continuous F :=
    NNReal.continuous_coe.comp (G.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hF0 : ∀ v, 0 ≤ F v := fun v => (G _).2
  have hFK : ∀ v, |F v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hF0 v)]; exact_mod_cast hG1 _
  have hFL : ∀ v v', |F v - F v'| ≤ (KG : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hGL.dist_le_mul (fun j => v (e.symm j)) (fun j => v' (e.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KG.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e.symm j))
  obtain ⟨g, hgm, hgK, hgD, hgM'⟩ := EthierKurtz.sde_markov_property_fd_conditional hB hσc hbc s₁ b₁
    S L hs₁ hb₁ hL hSg hLg hag hX' τ hFc.measurable hFK KG.2 hFL
  have hgM := fun x hx s' hD => by
    have h1 := hgM' x hx s' hD 0 (fun j => j.elim0) (fun j => j.elim0) (fun _ => (1 : ℝ))
      measurable_const 1 0 (fun v => by simp) le_rfl (fun v v' => by simp)
    simpa only [one_mul] using h1
  have hGF : ∀ f : ℚ → SDEState n, ((G (s.restrict f) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (F (fun i => f (e i))) := by
    intro f
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [Equiv.apply_symm_apply, Finset.restrict]
  have hlin : ∀ Φ : Ω → (Fin s.card → SDEState n), Measurable Φ →
      ∫⁻ ω, ENNReal.ofReal (F (Φ ω)) ∂P = ENNReal.ofReal (∫ ω, F (Φ ω) ∂P) := by
    intro Φ hΦ
    refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun ω => hF0 _)).symm
    exact (integrable_const (1 : ℝ)).mono' (hFc.measurable.comp hΦ).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFK _)
  let h : SDEState n → ℝ≥0∞ := (orthant n).piecewise (fun y => ENNReal.ofReal (g y))
    (fun y => ((G (s.restrict (fun _ : ℚ => y)) : ℝ≥0) : ℝ≥0∞))
  have hhm : Measurable h := by
    refine Measurable.piecewise orthant_isClosed.measurableSet (ENNReal.measurable_ofReal.comp hgm) ?_
    exact measurable_coe_nnreal_ennreal.comp
      (G.continuous.comp (continuous_pi fun j => continuous_id)).measurable
  have hheq : ∀ y, ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P = h y := by
    intro y
    by_cases hy : y ∈ orthant n
    · simp only [h, Set.piecewise_eq_of_mem _ _ _ hy, K4.Zf, if_pos hy]
      simp_rw [hGF]
      rw [hgD y hy]
      exact hlin (fun ω i => X y (τ i) ω) (measurable_pi_lambda _ fun i => (hXs y hy).1 _)
    · simp only [h, Set.piecewise_eq_of_notMem _ _ _ hy, K4.Zf, if_neg hy]
      simp
  have hgI : Integrable (fun ω => g (X x t ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hgm.comp ((hXs x hxo).1 t)).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hgK _)
  have hg0 : 0 ≤ᵐ[P] fun ω => g (X x t ω) := by
    filter_upwards [hinv x hxo t] with ω hω
    show (0 : ℝ) ≤ g (X x t ω)
    rw [hgD _ hω]
    exact integral_nonneg fun ω' => hF0 (fun i => X (X x t ω) (τ i) ω')
  refine ⟨?_, ?_⟩
  · have : (fun y => ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P) = h := funext hheq
    rw [this]; exact hhm
  calc ∫⁻ ω, ((G (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0) : ℝ≥0∞) ∂P
        = ∫⁻ ω, ENNReal.ofReal (F (fun i => K4.shiftPath X x t ω (e i))) ∂P :=
          lintegral_congr fun ω => hGF _
    _ = ENNReal.ofReal (∫ ω, F (fun i => X x (t + τ i) ω) ∂P) :=
          hlin (fun ω i => X x (t + τ i) ω) (measurable_pi_lambda _ fun i => (hXs x hxo).1 _)
    _ = ENNReal.ofReal (∫ ω, g (X x t ω) ∂P) := by rw [hgM x hxo t (hinv x hxo t)]
    _ = ∫⁻ ω, ENNReal.ofReal (g (X x t ω)) ∂P := ofReal_integral_eq_lintegral_ofReal hgI hg0
    _ = ∫⁻ ω, h (X x t ω) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hinv x hxo t] with ω hω
          simp only [h, Set.piecewise_eq_of_mem _ _ _ hω]
    _ = ∫⁻ y, h y ∂(trans P X t x) := by
          rw [trans, lintegral_map hhm ((hXs x hxo).1 t)]
    _ = ∫⁻ y, ∫⁻ ω, ((G (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P ∂(trans P X t x) :=
          lintegral_congr fun y => (hheq y).symm

end StochKolmogorov.Classify.FDM

end Mod_FDM

-- ===== module FDMC =====
section Mod_FDMC

/-! K2-mc step 1 (8f909832): conditional finite-dimensional Markov identity, tested against a
Lipschitz functional `G` of finitely many past rational times in `(0, t]`, from child C
(`EthierKurtz.sde_markov_property_fd_conditional`) with `q = s'.card`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDMC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- past rational times `q ∈ (0, t]` -/
def Past (t : ℝ≥0) : Type := {q : ℚ // 0 < q ∧ (q : ℝ) ≤ t}

/-- the past rational path up to time `t` -/
def past (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (t : ℝ≥0) (ω : Ω) :
    Past t → SDEState n :=
  fun q => X x ((q.1 : ℚ) : ℝ).toNNReal ω

theorem measurable_past [MeasurableSpace Ω] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (t : ℝ≥0) (hm : ∀ s, Measurable (X x s)) : Measurable (past X x t) :=
  measurable_pi_lambda _ fun _ => hm _

theorem fdMarkovCond_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n) :
    ∀ x ∈ openOrthant n, ∀ (t : ℝ≥0) (s' : Finset (Past t)) (G : (∀ i : s', SDEState n) →ᵇ ℝ≥0),
      (∃ K, LipschitzWith K G) → (∀ w, G w ≤ 1) →
      ∀ (s : Finset ℚ) (F : (∀ i : s, SDEState n) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) * (F (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0∞) ∂P =
        ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (K4.Zf X (X x t ω) ω')) : ℝ≥0∞) ∂P ∂P := by
  classical
  obtain ⟨hP, hB, hXs⟩ := hX
  haveI := hP
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := FDM.kolm_trunc C hC
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hXs y hy
  intro x hx t s' G hGL hG1 s F hFL hF1
  obtain ⟨KG, hGL⟩ := hGL
  obtain ⟨KF, hFL⟩ := hFL
  have hxo : x ∈ orthant n := fun i => (hx i).le
  -- the future functional
  let e : Fin s.card ≃ s := s.equivFin.symm
  let τ : Fin s.card → ℝ≥0 := fun i => (((e i : ℚ) : ℝ)).toNNReal
  let Fr : (Fin s.card → SDEState n) → ℝ := fun v => ((F (fun j => v (e.symm j)) : ℝ≥0) : ℝ)
  have hFc : Continuous Fr :=
    NNReal.continuous_coe.comp (F.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hF0 : ∀ v, 0 ≤ Fr v := fun v => (F _).2
  have hFK : ∀ v, |Fr v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hF0 v)]; exact_mod_cast hF1 _
  have hFLr : ∀ v v', |Fr v - Fr v'| ≤ (KF : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hFL.dist_le_mul (fun j => v (e.symm j)) (fun j => v' (e.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KF.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e.symm j))
  -- the past functional
  let e' : Fin s'.card ≃ s' := s'.equivFin.symm
  let u : Fin s'.card → ℝ≥0 := fun j => ((((e' j).1).1 : ℚ) : ℝ).toNNReal
  have hu : ∀ j, 0 < u j ∧ u j ≤ t := fun j =>
    ⟨Real.toNNReal_pos.2 (by exact_mod_cast ((e' j).1).2.1),
      Real.toNNReal_le_iff_le_coe.2 ((e' j).1).2.2⟩
  let Gr : (Fin s'.card → SDEState n) → ℝ := fun v => ((G (fun j => v (e'.symm j)) : ℝ≥0) : ℝ)
  have hGc : Continuous Gr :=
    NNReal.continuous_coe.comp (G.continuous.comp (continuous_pi fun j => continuous_apply _))
  have hG0 : ∀ v, 0 ≤ Gr v := fun v => (G _).2
  have hGK : ∀ v, |Gr v| ≤ 1 := fun v => by
    rw [abs_of_nonneg (hG0 v)]; exact_mod_cast hG1 _
  have hGLr : ∀ v v', |Gr v - Gr v'| ≤ (KG : ℝ) * ∑ i, ‖v i - v' i‖ := by
    intro v v'
    have h1 := hGL.dist_le_mul (fun j => v (e'.symm j)) (fun j => v' (e'.symm j))
    rw [NNReal.dist_eq] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ KG.2)
    refine (dist_pi_le_iff (Finset.sum_nonneg fun i _ => norm_nonneg _)).2 fun j => ?_
    rw [dist_eq_norm]
    exact Finset.single_le_sum (f := fun i => ‖v i - v' i‖) (fun i _ => norm_nonneg _)
      (Finset.mem_univ (e'.symm j))
  obtain ⟨g, hgm, hgK, hgD, hgM⟩ := EthierKurtz.sde_markov_property_fd_conditional hB hσc hbc s₁ b₁
    S L hs₁ hb₁ hL hSg hLg hag hX' τ hFc.measurable hFK KF.2 hFLr
  have key := hgM x hxo t (hinv x hxo t) s'.card u hu Gr hGc.measurable 1 KG hGK KG.2 hGLr
  have hFeq : ∀ f : ℚ → SDEState n, ((F (s.restrict f) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Fr (fun i => f (e i))) := by
    intro f
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [Equiv.apply_symm_apply, Finset.restrict]
  have hGeq : ∀ ω, ((G (s'.restrict (past X x t ω)) : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Gr (fun j => X x (u j) ω)) := by
    intro ω
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 2
    congr 1
    funext j
    simp only [u, past, Equiv.apply_symm_apply, Finset.restrict]
  have hlin : ∀ Φ : Ω → (Fin s.card → SDEState n), Measurable Φ →
      ∫⁻ ω, ENNReal.ofReal (Fr (Φ ω)) ∂P = ENNReal.ofReal (∫ ω, Fr (Φ ω) ∂P) := by
    intro Φ hΦ
    refine (ofReal_integral_eq_lintegral_ofReal ?_ (Eventually.of_forall fun ω => hF0 _)).symm
    exact (integrable_const (1 : ℝ)).mono' (hFc.measurable.comp hΦ).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hFK _)
  let h : SDEState n → ℝ≥0∞ := (orthant n).piecewise (fun y => ENNReal.ofReal (g y))
    (fun y => ((F (s.restrict (fun _ : ℚ => y)) : ℝ≥0) : ℝ≥0∞))
  have hheq : ∀ y, ∫⁻ ω, ((F (s.restrict (K4.Zf X y ω)) : ℝ≥0) : ℝ≥0∞) ∂P = h y := by
    intro y
    by_cases hy : y ∈ orthant n
    · simp only [h, Set.piecewise_eq_of_mem _ _ _ hy, K4.Zf, if_pos hy]
      simp_rw [hFeq]
      rw [hgD y hy]
      exact hlin (fun ω i => X y (τ i) ω) (measurable_pi_lambda _ fun i => (hXs y hy).1 _)
    · simp only [h, Set.piecewise_eq_of_notMem _ _ _ hy, K4.Zf, if_neg hy]
      simp
  have hGm : Measurable fun ω => Gr (fun j => X x (u j) ω) :=
    hGc.measurable.comp (f := fun ω j => X x (u j) ω) (measurable_pi_lambda _ fun j => (hXs x hxo).1 _)
  have hFm : Measurable fun ω => Fr (fun i => X x (t + τ i) ω) :=
    hFc.measurable.comp (f := fun ω i => X x (t + τ i) ω)
      (measurable_pi_lambda _ fun i => (hXs x hxo).1 _)
  have hgXm : Measurable fun ω => g (X x t ω) := hgm.comp ((hXs x hxo).1 t)
  have hI1 : Integrable (fun ω => Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hGm.mul hFm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hGK (fun j => X x (u j) ω)) (abs_nonneg _) (hFK (fun i => X x (t + τ i) ω)))
  have hI2 : Integrable (fun ω => Gr (fun j => X x (u j) ω) * g (X x t ω)) P :=
    (integrable_const (1 : ℝ)).mono' (hGm.mul hgXm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hGK (fun j => X x (u j) ω)) (abs_nonneg _) (hgK (X x t ω)))
  have hg0 : ∀ᵐ ω ∂P, 0 ≤ g (X x t ω) := by
    filter_upwards [hinv x hxo t] with ω hω
    rw [hgD _ hω]
    exact integral_nonneg fun ω' => hF0 (fun i => X (X x t ω) (τ i) ω')
  calc ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) * (F (s.restrict (K4.shiftPath X x t ω)) : ℝ≥0∞) ∂P
        = ∫⁻ ω, ENNReal.ofReal (Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω)) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [hGeq, hFeq, ENNReal.ofReal_mul (hG0 (fun j => X x (u j) ω))]
          rfl
    _ = ENNReal.ofReal (∫ ω, Gr (fun j => X x (u j) ω) * Fr (fun i => X x (t + τ i) ω) ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hI1
            (Eventually.of_forall fun ω => mul_nonneg (hG0 (fun j => X x (u j) ω))
              (hF0 (fun i => X x (t + τ i) ω)))).symm
    _ = ENNReal.ofReal (∫ ω, Gr (fun j => X x (u j) ω) * g (X x t ω) ∂P) := by rw [key]
    _ = ∫⁻ ω, ENNReal.ofReal (Gr (fun j => X x (u j) ω) * g (X x t ω)) ∂P :=
          ofReal_integral_eq_lintegral_ofReal hI2
            (hg0.mono fun ω hω => mul_nonneg (hG0 (fun j => X x (u j) ω)) hω)
    _ = ∫⁻ ω, (G (s'.restrict (past X x t ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (K4.Zf X (X x t ω) ω')) : ℝ≥0∞) ∂P ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hinv x hxo t] with ω hω
          rw [hheq, hGeq, ENNReal.ofReal_mul (hG0 (fun j => X x (u j) ω))]
          simp only [h, Set.piecewise_eq_of_mem _ _ _ hω]

end StochKolmogorov.Classify.FDMC

end Mod_FDMC

-- ===== module PathMix2 =====
section Mod_PathMix2

/-! K2-mc (8f909832): two-measure version of PathMix. `Q` (finite; e.g. `P` weighted by a past
functional) governs `Y`, the probability `P` governs `Z y`, and `κ` (finite, same mass as `Q`)
mixes: `Q(Y ∈ Γ) = ∫ P(Z y ∈ Γ) dκ(y)`. Used for the conditional (past-weighted) path Markov
identity: `Q = P.withDensity (G ∘ past)`, `κ = Q.map (X x s)`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.PathMix2

variable {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

def MixQ {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) (Y : Ω → W) (Z : E → Ω → W)
    (κ : Measure E) (Γ : Set W) : Prop :=
  Measurable (fun y => P (Z y ⁻¹' Γ)) ∧ Q (Y ⁻¹' Γ) = ∫⁻ y, P (Z y ⁻¹' Γ) ∂κ

theorem mixQ_compl {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) [IsFiniteMeasure Q]
    [IsProbabilityMeasure P] (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W)
    (hZ : ∀ y, Measurable (Z y)) (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (t : Set W) (htm : MeasurableSet t) (hmix : MixQ Q P Y Z κ t) : MixQ Q P Y Z κ tᶜ := by
  obtain ⟨hm, heq⟩ := hmix
  have hc : ∀ y, P (Z y ⁻¹' tᶜ) = 1 - P (Z y ⁻¹' t) := fun y => by
    rw [Set.preimage_compl, prob_compl_eq_one_sub (htm.preimage (hZ y))]
  refine ⟨?_, ?_⟩
  · simp_rw [hc]; exact hm.const_sub 1
  · rw [Set.preimage_compl, measure_compl (htm.preimage hY) (measure_ne_top _ _), heq, hmass]
    simp_rw [hc]
    have hle : (fun y => P (Z y ⁻¹' t)) ≤ᵐ[κ] fun _ => (1 : ℝ≥0∞) :=
      Eventually.of_forall fun y => prob_le_one
    have hfin : ∫⁻ y, P (Z y ⁻¹' t) ∂κ ≠ ∞ := by
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂κ) ?_ (lintegral_mono fun y => prob_le_one)
      simp
    rw [lintegral_sub hm hfin hle]
    simp

theorem mixQ_iUnion {W : Type*} [MeasurableSpace W] (Q P : Measure Ω) (Y : Ω → W)
    (hY : Measurable Y) (Z : E → Ω → W) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    (f : ℕ → Set W) (hd : Pairwise (Function.onFun Disjoint f)) (hfm : ∀ i, MeasurableSet (f i))
    (hmix : ∀ i, MixQ Q P Y Z κ (f i)) : MixQ Q P Y Z κ (⋃ i, f i) := by
  have hZd : ∀ y, P (Z y ⁻¹' ⋃ i, f i) = ∑' i, P (Z y ⁻¹' f i) := fun y => by
    rw [Set.preimage_iUnion]
    exact measure_iUnion (fun i j hij => (hd hij).preimage _) (fun i => (hfm i).preimage (hZ y))
  refine ⟨?_, ?_⟩
  · simp_rw [hZd]; exact Measurable.tsum fun i => (hmix i).1
  · rw [Set.preimage_iUnion, measure_iUnion (fun i j hij => (hd hij).preimage _)
      (fun i => (hfm i).preimage hY)]
    simp_rw [hZd]
    rw [lintegral_tsum fun i => (hmix i).1.aemeasurable]
    exact tsum_congr fun i => (hmix i).2

theorem mixQ_of_pi {W : Type*} [mW : MeasurableSpace W] (Q P : Measure Ω) [IsFiniteMeasure Q]
    [IsProbabilityMeasure P] (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W)
    (hZ : ∀ y, Measurable (Z y)) (κ : Measure E) [IsFiniteMeasure κ]
    (hmass : Q Set.univ = κ Set.univ) {𝒮 : Set (Set W)} (hgen : mW = generateFrom 𝒮)
    (hpi : IsPiSystem 𝒮) (hS : ∀ t ∈ 𝒮, MixQ Q P Y Z κ t) :
    ∀ Γ : Set W, MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  intro Γ hΓ
  refine MeasurableSpace.induction_on_inter (C := fun Γ _ => MixQ Q P Y Z κ Γ)
    hgen hpi ?_ ?_ ?_ ?_ Γ hΓ
  · refine ⟨by simp, by simp⟩
  · intro t ht
    exact hS t ht
  · intro t htm hmix
    exact mixQ_compl Q P Y hY Z hZ κ hmass t htm hmix
  · intro f hd hfm hmix
    exact mixQ_iUnion Q P Y hY Z hZ κ f hd hfm hmix

theorem mixQ_closed {W : Type*} [PseudoEMetricSpace W] [MeasurableSpace W] [OpensMeasurableSpace W]
    (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → W) (hY : Measurable Y) (Z : E → Ω → W) (hZ : ∀ y, Measurable (Z y)) (κ : Measure E)
    [IsFiniteMeasure κ]
    (hF : ∀ F : W →ᵇ ℝ≥0, (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (Z y ω) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (Y ω) : ℝ≥0∞) ∂Q = ∫⁻ y, ∫⁻ ω, (F (Z y ω) : ℝ≥0∞) ∂P ∂κ)
    (C : Set W) (hC : IsClosed C) : MixQ Q P Y Z κ C := by
  have δpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
  have δlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → W →ᵇ ℝ≥0 := fun k => thickenedIndicator (δpos k) C
  have hF' := fun k => hF (F k) ⟨_, lipschitzWith_thickenedIndicator (δpos k) C⟩
    (fun w => thickenedIndicator_le_one (δpos k) C w)
  have hFm : ∀ k, Measurable fun w => ((F k w : ℝ≥0) : ℝ≥0∞) :=
    fun k => measurable_coe_nnreal_ennreal.comp (F k).continuous.measurable
  have hlim : ∀ (μ : Measure Ω) [IsFiniteMeasure μ] (V : Ω → W), Measurable V →
      Tendsto (fun k => ∫⁻ ω, (F k (V ω) : ℝ≥0∞) ∂μ) atTop (𝓝 (μ (V ⁻¹' C))) := by
    intro μ _ V hV
    have e : ∀ k, ∫⁻ ω, (F k (V ω) : ℝ≥0∞) ∂μ = ∫⁻ w, (F k w : ℝ≥0∞) ∂(μ.map V) :=
      fun k => (lintegral_map (hFm k) hV).symm
    simp_rw [e]
    rw [← Measure.map_apply hV hC.measurableSet]
    haveI : IsFiniteMeasure (μ.map V) := Measure.isFiniteMeasure_map μ V
    exact tendsto_lintegral_thickenedIndicator_of_isClosed (μ.map V) hC δpos δlim
  have hmeas : Measurable fun y => P (Z y ⁻¹' C) :=
    measurable_of_tendsto_metrizable (fun k => (hF' k).1)
      (tendsto_pi_nhds.2 fun y => hlim P _ (hZ y))
  refine ⟨hmeas, ?_⟩
  have h1 := hlim Q Y hY
  have h2 : Tendsto (fun k => ∫⁻ y, ∫⁻ ω, (F k (Z y ω) : ℝ≥0∞) ∂P ∂κ) atTop
      (𝓝 (∫⁻ y, P (Z y ⁻¹' C) ∂κ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => 1) (fun k => (hF' k).1)
      (fun k => Eventually.of_forall fun y => ?_) (by simp)
      (Eventually.of_forall fun y => hlim P _ (hZ y))
    calc ∫⁻ ω, (F k (Z y ω) : ℝ≥0∞) ∂P ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P :=
          lintegral_mono fun ω => by
            exact ENNReal.coe_le_one_iff.mpr (thickenedIndicator_le_one (δpos k) C (Z y ω))
      _ = 1 := by simp
  have h3 : Tendsto (fun k => ∫⁻ ω, (F k (Y ω) : ℝ≥0∞) ∂Q) atTop
      (𝓝 (∫⁻ y, P (Z y ⁻¹' C) ∂κ)) := by
    simp_rw [(hF' _).2]; exact h2
  exact tendsto_nhds_unique h1 h3

theorem mixQ_cylinders (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → (ι → E)) (hY : Measurable Y) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (hcyl : ∀ (s : Finset ι) (S : Set (∀ i : s, E)), MeasurableSet S →
      MixQ Q P Y Z κ (cylinder s S)) :
    ∀ Γ : Set (ι → E), MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  refine mixQ_of_pi Q P Y hY Z hZ κ hmass generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders fun t ht => ?_
  obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).1 ht
  exact hcyl s S hS

/-- two-measure PM2: finite-dimensional Lipschitz test functions to the path σ-algebra. -/
theorem mixQ_all [PseudoMetricSpace E] [SecondCountableTopology E]
    [BorelSpace E] (Q P : Measure Ω) [IsFiniteMeasure Q] [IsProbabilityMeasure P]
    (Y : Ω → (ι → E)) (hY : Measurable Y) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (κ : Measure E) [IsFiniteMeasure κ] (hmass : Q Set.univ = κ Set.univ)
    (hFD : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (s.restrict (Y ω)) : ℝ≥0∞) ∂Q =
        ∫⁻ y, ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P ∂κ) :
    ∀ Γ : Set (ι → E), MeasurableSet Γ → MixQ Q P Y Z κ Γ := by
  refine mixQ_cylinders Q P Y hY Z hZ κ hmass fun s S hS => ?_
  have hYs : Measurable fun ω => s.restrict (Y ω) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp hY
  have hZs : ∀ y, Measurable fun ω => s.restrict (Z y ω) :=
    fun y => measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp (hZ y)
  have hgen : (inferInstance : MeasurableSpace (∀ i : s, E)) = generateFrom {C | IsClosed C} :=
    BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed
  exact mixQ_of_pi Q P _ hYs _ hZs κ hmass hgen isPiSystem_isClosed
    (fun C hC => mixQ_closed Q P _ hYs _ hZs κ (hFD s) C hC) S hS

end StochKolmogorov.Classify.PathMix2

end Mod_PathMix2

-- ===== module CondMix =====
section Mod_CondMix

/-! K2-mc steps 2-3 (8f909832), generic: from the conditional finite-dimensional Markov identity
(Lipschitz tests `G` of the past path `V`, `F` of the future path `Y`) to the conditional path
identity `P(Y ∈ Γ, V ∈ A) = ∫_{V ∈ A} P(Z (Xt ω) ∈ Γ) dP(ω)` for all measurable `A`, `Γ`. -/

set_option autoImplicit false

open MeasureTheory Filter MeasurableSpace
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace StochKolmogorov.Classify.CondMix

/-- Two finite Borel measures on a pseudo-emetric space agree if they agree on Lipschitz
bounded continuous functions with values in `[0, 1]`. -/
theorem ext_lip {W : Type*} [PseudoEMetricSpace W] [MeasurableSpace W] [BorelSpace W]
    (μ ν : Measure W) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ F : W →ᵇ ℝ≥0, (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ w, (F w : ℝ≥0∞) ∂μ = ∫⁻ w, (F w : ℝ≥0∞) ∂ν) : μ = ν := by
  have δpos : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
  have δlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcl : ∀ C : Set W, IsClosed C → μ C = ν C := by
    intro C hC
    have h1 := tendsto_lintegral_thickenedIndicator_of_isClosed μ hC δpos δlim
    have h2 := tendsto_lintegral_thickenedIndicator_of_isClosed ν hC δpos δlim
    have e : ∀ k : ℕ, ∫⁻ w, (thickenedIndicator (δpos k) C w : ℝ≥0∞) ∂μ =
        ∫⁻ w, (thickenedIndicator (δpos k) C w : ℝ≥0∞) ∂ν := fun k =>
      h _ ⟨_, lipschitzWith_thickenedIndicator (δpos k) C⟩
        (fun w => thickenedIndicator_le_one (δpos k) C w)
    simp_rw [e] at h1
    exact tendsto_nhds_unique h1 h2
  refine ext_of_generate_finite _ ?_ isPiSystem_isClosed (fun C hC => hcl C hC)
    (hcl _ isClosed_univ)
  rw [BorelSpace.measurable_eq (α := W), borel_eq_generateFrom_isClosed]

/-- Two finite measures on a path space `ι → E` agree if they agree on Lipschitz `[0,1]`-valued
tests of finitely many coordinates. -/
theorem pi_ext_lip {ι E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ ν : Measure (ι → E)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ w, (F (s.restrict w) : ℝ≥0∞) ∂μ = ∫⁻ w, (F (s.restrict w) : ℝ≥0∞) ∂ν) : μ = ν := by
  have hmap : ∀ s : Finset ι, μ.map s.restrict = ν.map s.restrict := by
    intro s
    refine ext_lip _ _ fun F hF hF1 => ?_
    have hFm : Measurable fun w : (∀ i : s, E) => ((F w : ℝ≥0) : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp F.continuous.measurable
    rw [lintegral_map hFm (Finset.measurable_restrict s),
      lintegral_map hFm (Finset.measurable_restrict s)]
    exact h s F hF hF1
  have hcyl : ∀ t ∈ measurableCylinders (fun _ : ι => E), μ t = ν t := by
    intro t ht
    rw [mem_measurableCylinders] at ht
    obtain ⟨s, S, hS, rfl⟩ := ht
    have e : cylinder (α := fun _ : ι => E) s S = s.restrict ⁻¹' S := rfl
    rw [e, ← Measure.map_apply (Finset.measurable_restrict s) hS,
      ← Measure.map_apply (Finset.measurable_restrict s) hS, hmap s]
  refine ext_of_generate_finite _ generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders hcyl ?_
  have := hcyl _ (cylinder_mem_measurableCylinders (∅ : Finset ι) Set.univ MeasurableSet.univ)
  simpa using this

variable {Ω E ι ι' : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The conditional path identity. -/
theorem condMix [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → (ι' → E)) (hV : Measurable V) (Y : Ω → (ι → E)) (hY : Measurable Y)
    (Xt : Ω → E) (hXt : Measurable Xt) (Z : E → Ω → (ι → E)) (hZ : ∀ y, Measurable (Z y))
    (hFD : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P))
    (hC : ∀ (s' : Finset ι') (G : (∀ i : s', E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K G) → (∀ w, G w ≤ 1) →
      ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) → (∀ w, F w ≤ 1) →
      ∫⁻ ω, (G (s'.restrict (V ω)) : ℝ≥0∞) * (F (s.restrict (Y ω)) : ℝ≥0∞) ∂P =
        ∫⁻ ω, (G (s'.restrict (V ω)) : ℝ≥0∞) *
          ∫⁻ ω', (F (s.restrict (Z (Xt ω) ω')) : ℝ≥0∞) ∂P ∂P)
    (A : Set (ι' → E)) (hA : MeasurableSet A) (Γ : Set (ι → E)) (hΓ : MeasurableSet Γ) :
    Measurable (fun y => P (Z y ⁻¹' Γ)) ∧
      P (Y ⁻¹' Γ ∩ V ⁻¹' A) = ∫⁻ ω in V ⁻¹' A, P (Z (Xt ω) ⁻¹' Γ) ∂P := by
  set Q : Measure Ω := P.restrict (V ⁻¹' A) with hQ
  set κ : Measure E := Q.map Xt with hκ
  haveI hQfin : IsFiniteMeasure Q := by rw [hQ]; infer_instance
  haveI : IsFiniteMeasure κ := Measure.isFiniteMeasure_map Q Xt
  have hmass : Q Set.univ = κ Set.univ := by
    rw [hκ, Measure.map_apply hXt MeasurableSet.univ, Set.preimage_univ]
  -- the finite-dimensional identity under `Q`
  have hFDQ : ∀ (s : Finset ι) (F : (∀ i : s, E) →ᵇ ℝ≥0), (∃ K, LipschitzWith K F) →
      (∀ w, F w ≤ 1) →
      Measurable (fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P) ∧
      ∫⁻ ω, (F (s.restrict (Y ω)) : ℝ≥0∞) ∂Q =
        ∫⁻ y, ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P ∂κ := by
    intro s F hF hF1
    have hHm := hFD s F hF hF1
    refine ⟨hHm, ?_⟩
    set H : E → ℝ≥0∞ := fun y => ∫⁻ ω, (F (s.restrict (Z y ω)) : ℝ≥0∞) ∂P with hH
    have hFYm : Measurable fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞) :=
      measurable_coe_nnreal_ennreal.comp
        (F.continuous.measurable.comp ((Finset.measurable_restrict s).comp hY))
    have hHXm : Measurable fun ω => H (Xt ω) := hHm.comp hXt
    have hH1 : ∀ y, H y ≤ 1 := fun y => by
      calc H y ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂P :=
            lintegral_mono fun ω => ENNReal.coe_le_one_iff.mpr (hF1 _)
        _ = 1 := by simp
    -- two measures on the past path space
    set μ1 : Measure (ι' → E) :=
      (P.withDensity fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞)).map V with hμ1
    set μ2 : Measure (ι' → E) := (P.withDensity fun ω => H (Xt ω)).map V with hμ2
    have hfin1 : IsFiniteMeasure (P.withDensity fun ω => ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞)) := by
      refine isFiniteMeasure_withDensity ?_
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂P) (by simp) ?_
      exact lintegral_mono fun ω => ENNReal.coe_le_one_iff.mpr (hF1 _)
    have hfin2 : IsFiniteMeasure (P.withDensity fun ω => H (Xt ω)) := by
      refine isFiniteMeasure_withDensity ?_
      refine ne_top_of_le_ne_top (b := ∫⁻ _, (1 : ℝ≥0∞) ∂P) (by simp) ?_
      exact lintegral_mono fun ω => hH1 _
    haveI : IsFiniteMeasure μ1 := Measure.isFiniteMeasure_map _ V
    haveI : IsFiniteMeasure μ2 := Measure.isFiniteMeasure_map _ V
    have hμ : μ1 = μ2 := by
      refine pi_ext_lip μ1 μ2 fun s' G hG hG1 => ?_
      have hGm : Measurable fun w : (ι' → E) => ((G (s'.restrict w) : ℝ≥0) : ℝ≥0∞) :=
        measurable_coe_nnreal_ennreal.comp
          (G.continuous.measurable.comp (Finset.measurable_restrict s'))
      have hGVm : Measurable fun ω => ((G (s'.restrict (V ω)) : ℝ≥0) : ℝ≥0∞) := hGm.comp hV
      rw [hμ1, hμ2, lintegral_map hGm hV, lintegral_map hGm hV,
        lintegral_withDensity_eq_lintegral_mul _ hFYm hGVm,
        lintegral_withDensity_eq_lintegral_mul _ hHXm hGVm]
      have := hC s' G hG hG1 s F hF hF1
      simp only [Pi.mul_apply]
      rw [lintegral_congr fun ω => mul_comm _ _, this]
      exact lintegral_congr fun ω => mul_comm _ _
    have hA1 : μ1 A = ∫⁻ ω in V ⁻¹' A, ((F (s.restrict (Y ω)) : ℝ≥0) : ℝ≥0∞) ∂P := by
      rw [hμ1, Measure.map_apply hV hA, withDensity_apply _ (hV hA)]
    have hA2 : μ2 A = ∫⁻ ω in V ⁻¹' A, H (Xt ω) ∂P := by
      rw [hμ2, Measure.map_apply hV hA, withDensity_apply _ (hV hA)]
    rw [hκ, lintegral_map hHm hXt, hQ, ← hA1, ← hA2, hμ]
  have hmix := PathMix2.mixQ_all Q P Y hY Z hZ κ hmass hFDQ Γ hΓ
  refine ⟨hmix.1, ?_⟩
  have h2 := hmix.2
  rw [hQ, Measure.restrict_apply (hY hΓ)] at h2
  rw [h2, hκ, lintegral_map hmix.1 hXt]

end StochKolmogorov.Classify.CondMix

end Mod_CondMix

-- ===== module FDMC2 =====
section Mod_FDMC2

/-! K2-mc (8f909832): the conditional path Markov identity for the Kolmogorov solution family:
`P(shiftPath_t ∈ Γ, past_t ∈ A) = ∫_{past_t ∈ A} P(Zf (X x t ω) ∈ Γ) dP(ω)`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.FDMC

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem measurable_Zf [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (y : SDEState n) : Measurable (K4.Zf X y) := by
  unfold K4.Zf
  split_ifs with h
  · exact K3.measurable_rpath X y (hX.2.2 y h).1
  · exact measurable_const

theorem condPath_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (x : SDEState n) (hx : x ∈ openOrthant n) (t : ℝ≥0)
    (A : Set (Past t → SDEState n)) (hA : MeasurableSet A)
    (Γ : Set (ℚ → SDEState n)) (hΓ : MeasurableSet Γ) :
    Measurable (fun y => P (K4.Zf X y ⁻¹' Γ)) ∧
      P (K4.shiftPath X x t ⁻¹' Γ ∩ past X x t ⁻¹' A) =
        ∫⁻ ω in past X x t ⁻¹' A, P (K4.Zf X (X x t ω) ⁻¹' Γ) ∂P := by
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  have hFD := FDM.fdMarkov_of P C B X hX hC hinv
  exact CondMix.condMix P (past X x t) (measurable_past X x t hsol.1)
    (K4.shiftPath X x t) (measurable_pi_lambda _ fun q => hsol.1 _) (X x t) (hsol.1 t)
    (K4.Zf X) (measurable_Zf P C B X hX)
    (fun s F hF hF1 => (hFD x hx t s F hF hF1).1)
    (fdMarkovCond_of P C B X hX hC hinv x hx t) A hA Γ hΓ

end StochKolmogorov.Classify.FDMC

end Mod_FDMC2

-- ===== module Levy =====
section Mod_Levy

/-! K2-levy (8f909832), generic: Lévy's upward theorem for an event `E`, with the conditional
probabilities `P(E | ℱ k)` identified by set integrals. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace StochKolmogorov.Classify.Levy

theorem levy_ind {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ mΩ) (E : Set Ω) (hE : MeasurableSet[⨆ k, ℱ k] E)
    (f : ℕ → Ω → ℝ) (hfm : ∀ k, StronglyMeasurable[ℱ k] (f k)) (hfb : ∀ k ω, |f k ω| ≤ 1)
    (hf : ∀ k (A : Set Ω), MeasurableSet[ℱ k] A → ∫ ω in A, f k ω ∂P = P.real (E ∩ A)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => f k ω) atTop (𝓝 (E.indicator 1 ω)) := by
  have hle : (⨆ k, ℱ k) ≤ mΩ := iSup_le fun k => ℱ.le k
  have hEm : MeasurableSet E := hle _ hE
  set g : Ω → ℝ := E.indicator 1 with hg
  have hgint : Integrable g P := (integrable_const (1 : ℝ)).indicator hEm
  have hgsm : StronglyMeasurable[⨆ k, ℱ k] g := stronglyMeasurable_const.indicator hE
  have hlev := hgint.tendsto_ae_condExp (ℱ := ℱ) hgsm
  have heq : ∀ k, f k =ᵐ[P] P[g | ℱ k] := by
    intro k
    have hfk : Measurable (f k) := ((hfm k).mono (ℱ.le k)).measurable
    have hfI : Integrable (f k) P :=
      (integrable_const (1 : ℝ)).mono' hfk.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hfb k ω)
    refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le k) hgint
      (fun s _ _ => hfI.integrableOn) (fun s hs _ => ?_) (hfm k).aestronglyMeasurable
    rw [hf k s hs, hg, integral_indicator_one hEm, Measure.real, Measure.real,
      Measure.restrict_apply hEm]
  filter_upwards [hlev, ae_all_iff.2 heq] with ω h1 h2
  exact h1.congr fun k => (h2 k).symm

/-- Grid convergence for (almost) every offset `u ∈ [0,1]` implies a.s. convergence of the
continuous-time Cesàro averages (Fubini over the offset + dominated convergence + Cesàro). -/
theorem cesaro_of_grid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ → Ω → ℝ) (hYm : Measurable (fun p : Ω × ℝ => Y p.2 p.1)) (hYb : ∀ s ω, |Y s ω| ≤ 1)
    (c : Ω → ℝ) (hc : Measurable c)
    (hgrid : ∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ᵐ ω ∂P,
      Tendsto (fun k : ℕ => Y (k + u) ω) atTop (𝓝 (c ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N⁻¹ : ℝ) * ∫ s in (0 : ℝ)..N, Y s ω) atTop (𝓝 (c ω)) := by
  set ν : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1) with hν
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 (by simp [Real.volume_Icc])
  let f : ℕ → Ω × ℝ → ℝ := fun k p => Y (k + p.2) p.1 - c p.1
  have hfm : ∀ k, Measurable (f k) := fun k =>
    (hYm.comp (measurable_fst.prodMk (measurable_const.add measurable_snd))).sub
      (hc.comp measurable_fst)
  set B : Set (Ω × ℝ) := {p | ¬ Tendsto (fun k => f k p) atTop (𝓝 0)} with hBdef
  have hB : MeasurableSet B := (measurableSet_tendsto (𝓝 0) hfm).compl
  have hprod : (P.prod ν) B = 0 := by
    rw [Measure.prod_apply_symm hB]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have h1 := hgrid u hu
    show P {x | ¬ Tendsto (fun k => f k (x, u)) atTop (𝓝 0)} = 0
    exact ae_iff.1 (h1.mono fun ω h => tendsto_sub_nhds_zero_iff.2 h)
  rw [Measure.prod_apply hB] at hprod
  have hω := (lintegral_eq_zero_iff (measurable_measure_prodMk_left hB)).1 hprod
  filter_upwards [hω] with ω hω0
  have hω0' : ν (Prod.mk ω ⁻¹' B) = 0 := hω0
  have hsec : ∀ k : ℕ, Measurable fun u : ℝ => Y (k + u) ω := fun k =>
    hYm.comp (measurable_const.prodMk (measurable_const.add measurable_id))
  have hae : ∀ᵐ u ∂ν, Tendsto (fun k : ℕ => Y (k + u) ω) atTop (𝓝 (c ω)) := by
    rw [ae_iff]
    refine measure_mono_null (fun u hu => ?_) hω0'
    intro h
    exact hu (tendsto_sub_nhds_zero_iff.1 h)
  have hD : Tendsto (fun k : ℕ => ∫ u, Y (k + u) ω ∂ν) atTop (𝓝 (∫ _u, c ω ∂ν)) :=
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun k => (hsec k).aestronglyMeasurable) (integrable_const 1)
      (fun k => Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hYb _ _) hae
  have hc1 : ∫ _u, c ω ∂ν = c ω := by
    simp [hν, Real.volume_Icc]
  rw [hc1] at hD
  have hpiece : ∀ k : ℕ, ∫ u, Y (k + u) ω ∂ν = ∫ s in (k : ℝ)..((k + 1 : ℕ) : ℝ), Y s ω := by
    intro k
    rw [hν, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_add_left (fun s => Y s ω) (k : ℝ)]
    push_cast
    simp
  have hII : ∀ a b : ℝ, IntervalIntegrable (fun s => Y s ω) volume a b := by
    intro a b
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' ?_ ?_
    · exact (hYm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · exact Eventually.of_forall fun s => by
        show ‖Y s ω‖ ≤ 1
        rw [Real.norm_eq_abs]; exact hYb _ _
  have hsum : ∀ N : ℕ, ∑ k ∈ Finset.range N, ∫ u, Y (k + u) ω ∂ν = ∫ s in (0 : ℝ)..N, Y s ω := by
    intro N
    simp_rw [hpiece]
    have := intervalIntegral.sum_integral_adjacent_intervals (f := fun s => Y s ω)
      (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := N) (fun k _ => hII _ _)
    simpa using this
  have hC := hD.cesaro
  simp_rw [hsum] at hC
  exact hC

end StochKolmogorov.Classify.Levy

end Mod_Levy

-- ===== module LevyPath =====
section Mod_LevyPath

/-! K2-levy (8f909832): for a measurable shift-invariant path set `Γ`, the Cesàro averages of
`h(X_{s+1})`, `h y = P(Zf y ∈ Γ)`, converge a.s. to the indicator of `{shiftPath_1 ∈ Γ}`
(Lévy upward theorem on the grids `k + u + 1` + the conditional path identity + Fubini). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.LevyPath

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem toNNReal_one_add (q : ℚ) :
    (((1 + max q 0 : ℚ) : ℝ)).toNNReal = 1 + ((q : ℝ)).toNNReal := by
  apply NNReal.eq
  rw [Real.coe_toNNReal', NNReal.coe_add, NNReal.coe_one, Real.coe_toNNReal']
  push_cast
  have : (0 : ℝ) ≤ 1 + max (q : ℝ) 0 := by have := le_max_right (q : ℝ) 0; linarith
  exact max_eq_left this

/-- `X x t` is measurable w.r.t. the past σ-algebra up to `t ≥ 1` (continuity from the left). -/
theorem measurable_X_past [mΩ : MeasurableSpace Ω] (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (hc : ∀ ω, Continuous fun t => X x t ω) (t : ℝ≥0) (ht : 1 ≤ t) :
    Measurable[MeasurableSpace.comap (FDMC.past X x t) inferInstance] (X x t) := by
  have hlt : ∀ j : ℕ, (t : ℝ) - 1 / ((j : ℝ) + 1) < t := fun j => by
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  choose q hq1 hq2 using fun j : ℕ => exists_rat_btwn (hlt j)
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hqpos : ∀ j, (0 : ℚ) < q j := fun j => by
    have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have : (0 : ℝ) < q j := by linarith [hq1 j]
    exact_mod_cast this
  let r : ℕ → FDMC.Past t := fun j => ⟨q j, hqpos j, (hq2 j).le⟩
  have hmeas : ∀ j, Measurable[MeasurableSpace.comap (FDMC.past X x t) inferInstance]
      (fun ω => FDMC.past X x t ω (r j)) := fun j =>
    (measurable_pi_apply (r j)).comp (comap_measurable (FDMC.past X x t))
  have hq : Tendsto (fun j => ((q j : ℚ) : ℝ)) atTop (𝓝 (t : ℝ)) := by
    have hd : Tendsto (fun j : ℕ => (t : ℝ) - 1 / ((j : ℝ) + 1)) atTop (𝓝 ((t : ℝ) - 0)) :=
      (tendsto_const_nhds (x := (t : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at hd
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hd tendsto_const_nhds
      (fun j => (hq1 j).le) (fun j => (hq2 j).le)
  have hq' : Tendsto (fun j => (((q j : ℚ) : ℝ)).toNNReal) atTop (𝓝 t) := by
    have := (continuous_real_toNNReal.tendsto _).comp hq
    rw [Real.toNNReal_coe] at this
    exact this
  exact @measurable_of_tendsto_metrizable Ω (SDEState n)
    (MeasurableSpace.comap (FDMC.past X x t) inferInstance) _ _ _ _ _ _ hmeas
    (tendsto_pi_nhds.2 fun ω => ((hc ω).tendsto t).comp hq')

theorem pi_meas_aux {α δ β : Type*} [m : MeasurableSpace α] [MeasurableSpace β] (f : α → δ → β)
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f := measurable_pi_lambda f hf

theorem levy_path [mΩ : MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (Γ : Set (ℚ → SDEState n)) (hΓ : MeasurableSet Γ)
    (hΓinv : ∀ (t : ℝ≥0) (ω : Ω), K4.shiftPath X x t ω ∈ Γ ↔ K4.shiftPath X x 1 ω ∈ Γ) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (N⁻¹ : ℝ) *
      ∫ s in (0 : ℝ)..N, (P (K4.Zf X (X x (s + 1).toNNReal ω) ⁻¹' Γ)).toReal) atTop
      (𝓝 ((K4.shiftPath X x 1 ⁻¹' Γ).indicator 1 ω)) := by
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  have hm := hsol.1
  have hc := hsol.2.1
  obtain ⟨hhm, -⟩ := FDMC.condPath_of P C B X hX hC hinv x hx 0 Set.univ MeasurableSet.univ Γ hΓ
  set h : SDEState n → ℝ := fun y => (P (K4.Zf X y ⁻¹' Γ)).toReal with hhdef
  have hh : Measurable h := hhm.ennreal_toReal
  have hh0 : ∀ y, 0 ≤ h y := fun y => ENNReal.toReal_nonneg
  have hh1 : ∀ y, h y ≤ 1 := fun y => by
    have := prob_le_one (μ := P) (s := K4.Zf X y ⁻¹' Γ)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  set E : Set Ω := K4.shiftPath X x 1 ⁻¹' Γ with hEdef
  have hShm : ∀ t, Measurable (K4.shiftPath X x t) := fun t =>
    measurable_pi_lambda _ fun q => hm _
  have hEm : MeasurableSet E := hShm 1 hΓ
  have hXj : Measurable (Function.uncurry fun (s : ℝ≥0) (ω : Ω) => X x s ω) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => hc ω) hm
  have hYm : Measurable (fun p : Ω × ℝ => h (X x (p.2 + 1).toNNReal p.1)) :=
    hh.comp (hXj.comp ((measurable_real_toNNReal.comp (measurable_snd.add_const 1)).prodMk
      measurable_fst))
  refine Levy.cesaro_of_grid P (fun s ω => h (X x (s + 1).toNNReal ω)) hYm
    (fun s ω => by rw [abs_of_nonneg (hh0 _)]; exact hh1 _) (E.indicator 1)
    (measurable_const.indicator hEm) fun u hu => ?_
  -- the grid `t k = k + u + 1`
  let t : ℕ → ℝ≥0 := fun k => ((k : ℝ) + u + 1).toNNReal
  have ht1 : ∀ k, 1 ≤ t k := fun k => by
    show (1 : ℝ≥0) ≤ ((k : ℝ) + u + 1).toNNReal
    rw [Real.one_le_toNNReal]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith [hu.1]
  have htmono : Monotone t := fun k k' hkk' => by
    apply Real.toNNReal_le_toNNReal
    have : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
    linarith
  let ℱ : Filtration ℕ mΩ :=
    { seq := fun k => MeasurableSpace.comap (FDMC.past X x (t k)) inferInstance
      mono' := by
        intro k k' hkk'
        have htt : t k ≤ t k' := htmono hkk'
        let rr : (FDMC.Past (t k') → SDEState n) → (FDMC.Past (t k) → SDEState n) :=
          fun g q => g ⟨q.1, q.2.1, q.2.2.trans (by exact_mod_cast htt)⟩
        have hrr : Measurable rr := measurable_pi_lambda _ fun q => measurable_pi_apply _
        have e : FDMC.past X x (t k) = rr ∘ FDMC.past X x (t k') := rfl
        show MeasurableSpace.comap (FDMC.past X x (t k)) inferInstance ≤
          MeasurableSpace.comap (FDMC.past X x (t k')) inferInstance
        rw [e, ← MeasurableSpace.comap_comp]
        exact MeasurableSpace.comap_mono hrr.comap_le
      le' := fun k => (FDMC.measurable_past X x (t k) hm).comap_le }
  have hE : MeasurableSet[⨆ k, ℱ k] E := by
    have hS : Measurable[⨆ k, MeasurableSpace.comap (FDMC.past X x (t k)) inferInstance]
        (K4.shiftPath X x 1) := by
      refine @pi_meas_aux Ω ℚ (SDEState n)
        (⨆ k, MeasurableSpace.comap (FDMC.past X x (t k)) inferInstance) _ _ fun q => ?_
      obtain ⟨k, hk⟩ := exists_nat_ge (1 + max (q : ℝ) 0)
      have hpos : (0 : ℚ) < 1 + max q 0 := by
        have := le_max_right q 0; linarith
      have hle : (((1 + max q 0 : ℚ) : ℝ)) ≤ (t k : ℝ) := by
        show (((1 + max q 0 : ℚ) : ℝ)) ≤ (((k : ℝ) + u + 1).toNNReal : ℝ)
        rw [Real.coe_toNNReal _ (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith [hu.1])]
        push_cast
        have := le_max_right (q : ℝ) 0
        have : (0 : ℝ) ≤ u := hu.1
        have hk' : 1 + max (q : ℝ) 0 ≤ k := hk
        linarith
      let r : FDMC.Past (t k) := ⟨1 + max q 0, hpos, hle⟩
      have e : (fun ω => K4.shiftPath X x 1 ω q) = fun ω => FDMC.past X x (t k) ω r := by
        funext ω
        simp only [K4.shiftPath, FDMC.past, r]
        rw [toNNReal_one_add]
      rw [e]
      exact ((measurable_pi_apply r).comp (comap_measurable (FDMC.past X x (t k)))).mono
        (le_iSup (fun k => MeasurableSpace.comap (FDMC.past X x (t k)) inferInstance) k) le_rfl
    exact hS hΓ
  have hfm : ∀ k, StronglyMeasurable[ℱ k] (fun ω => h (X x (t k) ω)) := fun k =>
    (hh.comp (measurable_X_past X x hc (t k) (ht1 k))).stronglyMeasurable
  have hf : ∀ k (A : Set Ω), MeasurableSet[ℱ k] A →
      ∫ ω in A, h (X x (t k) ω) ∂P = P.real (E ∩ A) := by
    intro k A hA
    obtain ⟨A', hA', hAeq⟩ := hA
    rw [← hAeq]
    obtain ⟨-, hid⟩ := FDMC.condPath_of P C B X hX hC hinv x hx (t k) A' hA' Γ hΓ
    have hset : K4.shiftPath X x (t k) ⁻¹' Γ = E := Set.ext fun ω => hΓinv (t k) ω
    rw [hset] at hid
    rw [Measure.real, hid]
    rw [integral_toReal]
    · exact (hhm.comp (hm (t k))).aemeasurable
    · exact Eventually.of_forall fun ω => measure_lt_top _ _
  have hlev := Levy.levy_ind P ℱ E hE (fun k ω => h (X x (t k) ω)) hfm
    (fun k ω => by rw [abs_of_nonneg (hh0 _)]; exact hh1 _) hf
  filter_upwards [hlev] with ω hω
  refine hω.congr fun k => ?_
  rfl

end StochKolmogorov.Classify.LevyPath

end Mod_LevyPath

-- ===== module K2fin =====
section Mod_K2fin

/-! K2 (8f909832) final step: a shift-invariant measurable path event `Γ` whose hitting
probability `P(Zf y ∈ Γ)` is at least `1/2` on a set `K` that the path visits with positive
lower time-density (5.40) happens almost surely. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K2fin

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem intervalIntegrable_of_bdd {f : ℝ → ℝ} (hf : Measurable f) (hb : ∀ s, |f s| ≤ 1)
    (a b : ℝ) : IntervalIntegrable f volume a b :=
  (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' hf.aestronglyMeasurable
    (Eventually.of_forall fun s => by
      show ‖f s‖ ≤ 1
      rw [Real.norm_eq_abs]; exact hb s)

theorem cover_of_levy [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (Γ : Set (ℚ → SDEState n)) (hΓ : MeasurableSet Γ)
    (hΓinv : ∀ (t : ℝ≥0) (ω : Ω), K4.shiftPath X x t ω ∈ Γ ↔ K4.shiftPath X x 1 ω ∈ Γ)
    (K : Set (SDEState n)) (hK : MeasurableSet K)
    (hhK : ∀ y ∈ K, (1 : ℝ) / 2 ≤ (P (K4.Zf X y ⁻¹' Γ)).toReal)
    (hrec : ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c ≤ (N⁻¹ : ℝ) * ∫ s in (0 : ℝ)..N, K.indicator 1 (X x (s + 1).toNNReal ω)) :
    ∀ᵐ ω ∂P, K4.shiftPath X x 1 ω ∈ Γ := by
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  obtain ⟨hhm, -⟩ := FDMC.condPath_of P C B X hX hC hinv x hx 0 Set.univ MeasurableSet.univ Γ hΓ
  filter_upwards [LevyPath.levy_path P C B X hX hC hinv x hx Γ hΓ hΓinv, hrec] with ω h1 hω2
  obtain ⟨c, hc, hev⟩ := hω2
  by_contra hω
  have hind : (K4.shiftPath X x 1 ⁻¹' Γ).indicator (1 : Ω → ℝ) ω = 0 :=
    Set.indicator_of_notMem (s := K4.shiftPath X x 1 ⁻¹' Γ) hω _
  rw [hind] at h1
  have hXc : Measurable fun s : ℝ => X x (s + 1).toNNReal ω :=
    ((hsol.2.1 ω).comp (continuous_real_toNNReal.comp (continuous_id.add continuous_const))).measurable
  set a : ℝ → ℝ := fun s => (P (K4.Zf X (X x (s + 1).toNNReal ω) ⁻¹' Γ)).toReal with ha
  set b : ℝ → ℝ := fun s => K.indicator (1 : SDEState n → ℝ) (X x (s + 1).toNNReal ω) with hb
  have ham : Measurable a := hhm.ennreal_toReal.comp hXc
  have hbm : Measurable b := (measurable_const.indicator hK).comp hXc
  have ha0 : ∀ s, 0 ≤ a s := fun s => ENNReal.toReal_nonneg
  have ha1 : ∀ s, |a s| ≤ 1 := fun s => by
    rw [abs_of_nonneg (ha0 s)]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
  have hb1 : ∀ s, |b s| ≤ 1 := fun s => by
    simp only [hb, Set.indicator]
    split_ifs <;> simp
  have hab : ∀ s, b s / 2 ≤ a s := by
    intro s
    by_cases hs : X x (s + 1).toNNReal ω ∈ K
    · have := hhK _ hs
      simp only [hb, Set.indicator_of_mem hs, Pi.one_apply]
      linarith
    · simp only [hb, Set.indicator_of_notMem hs]
      linarith [ha0 s]
  have hint : ∀ N : ℕ, (∫ s in (0 : ℝ)..N, b s) / 2 ≤ ∫ s in (0 : ℝ)..N, a s := by
    intro N
    rw [← intervalIntegral.integral_div]
    exact intervalIntegral.integral_mono_on (Nat.cast_nonneg N)
      ((intervalIntegrable_of_bdd hbm hb1 0 N).div_const 2)
      (intervalIntegrable_of_bdd ham ha1 0 N) fun s _ => hab s
  have hlt := h1.eventually (gt_mem_nhds (half_pos hc))
  obtain ⟨N, hN1, hN2⟩ := (hev.and hlt).exists
  have hNinv : (0 : ℝ) ≤ (N⁻¹ : ℝ) := inv_nonneg.2 (Nat.cast_nonneg N)
  have := mul_le_mul_of_nonneg_left (hint N) hNinv
  have e : (N⁻¹ : ℝ) * ((∫ s in (0 : ℝ)..N, b s) / 2) = ((N⁻¹ : ℝ) * ∫ s in (0 : ℝ)..N, b s) / 2 := by
    ring
  rw [e] at this
  have hN1' : c ≤ (N⁻¹ : ℝ) * ∫ s in (0 : ℝ)..N, b s := hN1
  have hN2' : (N⁻¹ : ℝ) * ∫ s in (0 : ℝ)..N, a s < c / 2 := hN2
  linarith

end StochKolmogorov.Classify.K2fin

end Mod_K2fin

-- ===== module Dfam =====
section Mod_Dfam

/-! K2-Γ (8f909832): a countable convergence-determining family `hD s k` of bounded continuous
functions on a separable metric space: tents `min 1 ((k+1) · infDist x (U s)ᶜ)` on finite unions
`U s` of balls from a countable basis. If `∫ hD s k dμᵢ → ∫ hD s k dμ` for every `s, k`, then
`μᵢ → μ` weakly (portmanteau, liminf over open sets). -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StochKolmogorov.Classify.Dfam

variable {E : Type*} [MetricSpace E] [TopologicalSpace.SeparableSpace E] [Nonempty E]

/-- countable family of balls: centre from a dense sequence, radius `1/(m+1)`. -/
noncomputable def ball' (j : ℕ) : Set E :=
  Metric.ball (TopologicalSpace.denseSeq E (Nat.unpair j).1) (1 / (((Nat.unpair j).2 : ℝ) + 1))

theorem exists_ball' {G : Set E} (hG : IsOpen G) {x : E} (hx : x ∈ G) :
    ∃ j, x ∈ ball' (E := E) j ∧ ball' (E := E) j ⊆ G := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hG x hx
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hr)
  have hm0 : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  obtain ⟨i, hi⟩ := (Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq E)) x _ hm0
  refine ⟨Nat.pair i m, ?_, ?_⟩
  · simp only [ball', Nat.unpair_pair, Metric.mem_ball]
    exact hi
  · intro z hz
    simp only [ball', Nat.unpair_pair, Metric.mem_ball] at hz
    apply hb
    rw [Metric.mem_ball]
    have := dist_triangle z (TopologicalSpace.denseSeq E i) x
    rw [dist_comm (TopologicalSpace.denseSeq E i) x] at this
    linarith

/-- finite unions of basic balls. -/
noncomputable def U (s : Finset ℕ) : Set E := ⋃ j ∈ s, ball' j

theorem isOpen_U (s : Finset ℕ) : IsOpen (U (E := E) s) :=
  isOpen_biUnion fun _ _ => Metric.isOpen_ball

/-- the tent function. -/
noncomputable def tent (s : Finset ℕ) (k : ℕ) (x : E) : ℝ :=
  min 1 (((k : ℝ) + 1) * Metric.infDist x (U s)ᶜ)

theorem continuous_tent (s : Finset ℕ) (k : ℕ) : Continuous (tent (E := E) s k) :=
  continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))

theorem tent_nonneg (s : Finset ℕ) (k : ℕ) (x : E) : 0 ≤ tent s k x :=
  le_min zero_le_one (mul_nonneg (by positivity) Metric.infDist_nonneg)

theorem tent_le_one (s : Finset ℕ) (k : ℕ) (x : E) : tent s k x ≤ 1 := min_le_left _ _

theorem norm_tent_le (s : Finset ℕ) (k : ℕ) (x : E) : ‖tent s k x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (tent_nonneg s k x)]; exact tent_le_one s k x

/-- the tent as a bounded continuous function. -/
noncomputable def hD (s : Finset ℕ) (k : ℕ) : E →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (tent s k) (continuous_tent s k) 1
    (norm_tent_le s k)

theorem hD_apply (s : Finset ℕ) (k : ℕ) (x : E) : hD s k x = tent s k x := rfl

theorem tent_eq_zero {s : Finset ℕ} (k : ℕ) {x : E} (hx : x ∉ U s) : tent s k x = 0 := by
  have : Metric.infDist x (U s)ᶜ = 0 := Metric.infDist_zero_of_mem hx
  simp [tent, this]

variable [MeasurableSpace E] [BorelSpace E]

/-- the approximating index sets for an open set `G`. -/
noncomputable def sG (G : Set E) (m : ℕ) : Finset ℕ := by
  classical exact (Finset.range m).filter fun j => ball' (E := E) j ⊆ G

theorem U_sG_subset (G : Set E) (m : ℕ) : U (sG G m) ⊆ G := by
  intro x hx
  simp only [U, Set.mem_iUnion] at hx
  obtain ⟨j, hj, hx⟩ := hx
  classical
  simp only [sG, Finset.mem_filter] at hj
  exact hj.2 hx

theorem tent_le_indicator (G : Set E) (m k : ℕ) (x : E) :
    tent (sG G m) k x ≤ G.indicator 1 x := by
  by_cases hx : x ∈ U (sG G m)
  · rw [Set.indicator_of_mem (U_sG_subset G m hx)]; exact tent_le_one _ _ _
  · rw [tent_eq_zero k hx]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem tent_tendsto_indicator {G : Set E} (hG : IsOpen G) (hGu : G ≠ Set.univ) (x : E) :
    Tendsto (fun m => tent (sG G m) m x) atTop (𝓝 (G.indicator 1 x)) := by
  by_cases hx : x ∈ G
  · rw [Set.indicator_of_mem hx]
    obtain ⟨j, hxj, hjG⟩ := exists_ball' hG hx
    obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem G).1 hGu
    -- for `m > j`, `x ∈ U (sG G m)` with a uniform distance to the complement
    have hsub : ∀ m, j < m → ball' (E := E) j ⊆ U (sG G m) := by
      intro m hm y hy
      simp only [U, Set.mem_iUnion]
      classical
      exact ⟨j, by simp [sG, Finset.mem_filter, Finset.mem_range, hm, hjG], hy⟩
    have hne : (ball' (E := E) j)ᶜ.Nonempty := ⟨z, fun h => hz (hjG h)⟩
    have hd : 0 < Metric.infDist x (ball' (E := E) j)ᶜ :=
      (IsClosed.notMem_iff_infDist_pos (Metric.isOpen_ball.isClosed_compl) hne).1
        (fun h => h hxj)
    set d := Metric.infDist x (ball' (E := E) j)ᶜ
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / d)
    refine tendsto_atTop_of_eventually_const (i₀ := max (j + 1) M) fun m hm => ?_
    have hmj : j < m := lt_of_lt_of_le (Nat.lt_succ_self j) (le_trans (le_max_left _ _) hm)
    have hmM : (M : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_right _ _) hm
    have hcne : (U (E := E) (sG G m))ᶜ.Nonempty := ⟨z, fun h => hz (U_sG_subset G m h)⟩
    have hdd : d ≤ Metric.infDist x (U (sG G m))ᶜ :=
      Metric.infDist_le_infDist_of_subset (Set.compl_subset_compl.2 (hsub m hmj)) hcne
    have h1 : 1 ≤ ((m : ℝ) + 1) * Metric.infDist x (U (sG G m))ᶜ := by
      have h2 : 1 < ((m : ℝ) + 1) * d := by
        rw [div_lt_iff₀ hd] at hM
        nlinarith
      nlinarith
    simp only [tent]
    exact min_eq_left h1
  · rw [Set.indicator_of_notMem hx]
    exact tendsto_const_nhds.congr fun m =>
      (tent_eq_zero m fun h => hx (U_sG_subset G m h)).symm

theorem integral_tent_tendsto (μ : Measure E) [IsFiniteMeasure μ] {G : Set E} (hG : IsOpen G)
    (hGu : G ≠ Set.univ) :
    Tendsto (fun m => ∫ x, tent (sG G m) m x ∂μ) atTop (𝓝 (μ.real G)) := by
  have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
    (fun m => (continuous_tent (sG G m) m).aestronglyMeasurable) (integrable_const 1)
    (fun m => Eventually.of_forall fun x => norm_tent_le _ _ x)
    (Eventually.of_forall fun x => tent_tendsto_indicator hG hGu x)
  rwa [integral_indicator_one hG.measurableSet] at h

/-- portmanteau through the countable family. -/
theorem tendsto_of_hD {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated] [L.NeBot]
    (μ : ProbabilityMeasure E) (μs : ι → ProbabilityMeasure E)
    (h : ∀ s k, Tendsto (fun i => ∫ x, hD s k x ∂(μs i : Measure E)) L
      (𝓝 (∫ x, hD s k x ∂(μ : Measure E)))) :
    Tendsto μs L (𝓝 μ) := by
  refine MeasureTheory.tendsto_of_forall_isOpen_le_liminf' fun G hG => ?_
  by_cases hGu : G = Set.univ
  · subst hGu
    simp only [measure_univ, Filter.liminf_const, le_refl]
  · -- for each `m`, `ofReal ∫ tent_m dμ ≤ liminf μᵢ(G)`
    have hm : ∀ m, ENNReal.ofReal (∫ x, tent (sG G m) m x ∂(μ : Measure E)) ≤
        L.liminf fun i => (μs i : Measure E) G := by
      intro m
      have ht : Tendsto (fun i => ENNReal.ofReal (∫ x, tent (sG G m) m x ∂(μs i : Measure E))) L
          (𝓝 (ENNReal.ofReal (∫ x, tent (sG G m) m x ∂(μ : Measure E)))) :=
        ENNReal.tendsto_ofReal (h (sG G m) m)
      rw [← ht.liminf_eq]
      refine liminf_le_liminf (Eventually.of_forall fun i => ?_)
      rw [← ofReal_measureReal (measure_ne_top _ G)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← integral_indicator_one hG.measurableSet]
      exact integral_mono ((hD (sG G m) m).integrable (μs i : Measure E)) (integrable_const (1 : ℝ) |>.indicator
        hG.measurableSet) fun x => tent_le_indicator G m m x
    have hlim := ENNReal.tendsto_ofReal (integral_tent_tendsto (μ : Measure E) hG hGu)
    rw [ofReal_measureReal (measure_ne_top _ G)] at hlim
    exact le_of_tendsto' hlim hm

end StochKolmogorov.Classify.Dfam

end Mod_Dfam

-- ===== module LimOcc =====
section Mod_LimOcc

/-! K2-Γ (8f909832): occupation measures of a continuous path.
* `limitSet_eq_of_avg`: if the `Dfam.hD` averages of `occ X x T ω` converge to those of a probability
  measure `μ`, then `limitSet X x ω = {μ}` (portmanteau through the countable family).
* `avg_of_limitSet`: if `limitSet X x ω = {μ}` and `{occ X x t ω, t ≥ 1}` is tight (Lemma 5.7), then
  `∫ h d(occ X x T ω) → ∫ h dμ` for every bounded continuous `h` (Prokhorov). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.LimOcc

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem isProb_occ (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) {T : ℝ} (hT : 0 < T) :
    IsProbabilityMeasure (occ X x T ω) := by
  have hm : Measurable fun s : ℝ => X x s.toNNReal ω :=
    (hc.comp continuous_real_toNNReal).measurable
  constructor
  unfold occ
  rw [Measure.smul_apply, Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, smul_eq_mul,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hT).ne' ENNReal.ofReal_ne_top]

theorem tendsto_occ_of_avg (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (μ : Measure (SDEState n)) [IsProbabilityMeasure μ]
    (havg : ∀ s k, Tendsto (fun T : ℝ => ∫ y, Dfam.hD s k y ∂(occ X x T ω)) atTop
      (𝓝 (∫ y, Dfam.hD s k y ∂μ)))
    (ts : ℕ → ℝ) (h1 : ∀ k, 1 ≤ ts k) (hts : Tendsto ts atTop atTop) (h : SDEState n →ᵇ ℝ) :
    Tendsto (fun k => ∫ y, h y ∂(occ X x (ts k) ω)) atTop (𝓝 (∫ y, h y ∂μ)) := by
  let μs : ℕ → ProbabilityMeasure (SDEState n) := fun k =>
    ⟨occ X x (ts k) ω, isProb_occ X x ω hc (lt_of_lt_of_le one_pos (h1 k))⟩
  let μP : ProbabilityMeasure (SDEState n) := ⟨μ, inferInstance⟩
  have := Dfam.tendsto_of_hD μP μs (fun s k => (havg s k).comp hts)
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 this) h

theorem limitSet_eq_of_avg (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (μ : Measure (SDEState n)) [IsProbabilityMeasure μ]
    (havg : ∀ s k, Tendsto (fun T : ℝ => ∫ y, Dfam.hD s k y ∂(occ X x T ω)) atTop
      (𝓝 (∫ y, Dfam.hD s k y ∂μ))) :
    limitSet X x ω = {μ} := by
  ext π
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hπ, ts, h1, hts, hlim⟩
    exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun h =>
      tendsto_nhds_unique (hlim h) (tendsto_occ_of_avg X x ω hc μ havg ts h1 hts h)
  · intro hπ
    rw [hπ]
    have h1 : ∀ k : ℕ, (1 : ℝ) ≤ (k : ℝ) + 1 := fun k => le_add_of_nonneg_left (Nat.cast_nonneg k)
    have hts : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact ⟨inferInstance, fun k => (k : ℝ) + 1, h1, hts,
      fun h => tendsto_occ_of_avg X x ω hc μ havg _ h1 hts h⟩

theorem avg_of_limitSet (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (μ : Measure (SDEState n))
    (hL : limitSet X x ω = {μ})
    (hT : IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X x t ω}) (h : SDEState n →ᵇ ℝ) :
    Tendsto (fun T : ℝ => ∫ y, h y ∂(occ X x T ω)) atTop (𝓝 (∫ y, h y ∂μ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  let S : Set (ProbabilityMeasure (SDEState n)) :=
    {ν | ∃ t : ℝ, 1 ≤ t ∧ (ν : Measure (SDEState n)) = occ X x t ω}
  have hS : IsTightMeasureSet {((ν : ProbabilityMeasure (SDEState n)) : Measure (SDEState n)) |
      ν ∈ S} := by
    refine hT.subset ?_
    rintro _ ⟨ν, ⟨t, ht, he⟩, rfl⟩
    exact ⟨t, ht, he⟩
  have hK := isCompact_closure_of_isTightMeasureSet hS
  let νs : ℕ → ProbabilityMeasure (SDEState n) := fun k =>
    ⟨occ X x (max (ns k) 1) ω, isProb_occ X x ω hc (lt_of_lt_of_le one_pos (le_max_right _ _))⟩
  have hmem : ∀ k, νs k ∈ closure S := fun k =>
    subset_closure ⟨max (ns k) 1, le_max_right _ _, rfl⟩
  obtain ⟨π, -, φ, hφ, hπ⟩ := hK.tendsto_subseq hmem
  have hns' : Tendsto (fun k => ns (φ k)) atTop atTop := hns.comp hφ.tendsto_atTop
  have hts : Tendsto (fun k => max (ns (φ k)) 1) atTop atTop :=
    tendsto_atTop_mono (fun k => le_max_left _ _) hns'
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hπ
  have hπL : (π : Measure (SDEState n)) ∈ limitSet X x ω :=
    ⟨inferInstance, fun k => max (ns (φ k)) 1, fun k => le_max_right _ _, hts, fun g => hint g⟩
  rw [hL, Set.mem_singleton_iff] at hπL
  refine ⟨φ, ?_⟩
  have h2 := hint h
  rw [hπL] at h2
  refine h2.congr' ?_
  filter_upwards [hns'.eventually_ge_atTop 1] with k hk
  show ∫ y, h y ∂(occ X x (max (ns (φ k)) 1) ω) = ∫ y, h y ∂(occ X x (ns (φ k)) ω)
  rw [max_eq_left hk]

end StochKolmogorov.Classify.LimOcc

end Mod_LimOcc

-- ===== module Riem =====
section Mod_Riem

/-! K2-Γ (8f909832), real-analysis helpers for the rational path set:
* `riemann_tendsto`: left Riemann sums of a continuous function on `[0, N]` converge.
* `avg_real_of_nat`: Cesàro averages of a bounded continuous function along `ℕ` imply along `ℝ`.
* `rate_iff`: the closed rational exponential-rate condition `RratR` is equivalent, for a continuous
  function and a negative rate, to `log ψ(t) / t → L`. -/

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped NNReal

namespace StochKolmogorov.Classify.Riem

theorem riemann_tendsto {φ : ℝ → ℝ} (hφ : Continuous φ) (N : ℕ) :
    Tendsto (fun m : ℕ => ∑ j ∈ Finset.range (N * (m + 1)),
      (1 / ((m : ℝ) + 1)) * φ (j * (1 / ((m : ℝ) + 1)))) atTop
      (𝓝 (∫ s in (0 : ℝ)..N, φ s)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hN1 : (0 : ℝ) < N + 1 := by positivity
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := (N : ℝ))).uniformContinuousOn_of_continuous
    hφ.continuousOn
  obtain ⟨δ, hδ, hd⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / (N + 1)) (div_pos hε hN1)
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hδ
  refine ⟨M, fun m hm => ?_⟩
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  set d : ℝ := 1 / ((m : ℝ) + 1) with hd_def
  have hdpos : 0 < d := by positivity
  have hdδ : d < δ := by
    refine lt_of_le_of_lt ?_ hM
    rw [hd_def]
    apply one_div_le_one_div_of_le (by positivity)
    have : (M : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  set K := N * (m + 1) with hK
  have hKd : (K : ℝ) * d = N := by
    rw [hK, hd_def]; push_cast; field_simp
  have hsplit : ∑ j ∈ Finset.range K, ∫ s in ((j : ℝ) * d)..((j : ℝ) * d + d), φ s =
      ∫ s in (0 : ℝ)..N, φ s := by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := φ)
      (a := fun j : ℕ => (j : ℝ) * d) (n := K) (fun k _ => hφ.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, Nat.cast_add, Nat.cast_one, add_one_mul] at this
    rw [hKd] at this
    exact this
  have hj : ∀ j ∈ Finset.range K,
      |d * φ (j * d) - ∫ s in ((j : ℝ) * d)..((j : ℝ) * d + d), φ s| ≤ ε / (N + 1) * d := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjK : (j : ℝ) + 1 ≤ K := by exact_mod_cast hj
    have hab : (j : ℝ) * d ≤ (j : ℝ) * d + d := by linarith
    have hconst : d * φ (j * d) = ∫ _s in ((j : ℝ) * d)..((j : ℝ) * d + d), φ (j * d) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hφ.intervalIntegrable _ _)]
    have hjN : (j : ℝ) * d + d ≤ N := by
      rw [← hKd]
      have := mul_le_mul_of_nonneg_right hjK hdpos.le
      linarith
    have h0 : 0 ≤ (j : ℝ) * d := by positivity
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (j : ℝ) * d)
      (b := (j : ℝ) * d + d) (C := ε / (N + 1)) (f := fun s => φ (j * d) - φ s) (by
        intro s hs
        rw [Set.uIoc_of_le hab] at hs
        have hs1 : (j : ℝ) * d ∈ Set.Icc (0 : ℝ) N := ⟨h0, by linarith⟩
        have hs2 : s ∈ Set.Icc (0 : ℝ) N := ⟨by linarith [hs.1], by linarith [hs.2]⟩
        have hdist : dist ((j : ℝ) * d) s < δ := by
          rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2]
        have := hd _ hs1 _ hs2 hdist
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs]; exact this.le)
    rw [Real.norm_eq_abs] at this
    calc _ ≤ _ := this
      _ = ε / (N + 1) * d := by
        rw [show (j : ℝ) * d + d - (j : ℝ) * d = d by ring, abs_of_pos hdpos]
  have hsum : |∑ j ∈ Finset.range K, d * φ (j * d) -
      ∑ j ∈ Finset.range K, ∫ s in ((j : ℝ) * d)..((j : ℝ) * d + d), φ s| ≤
      K * (ε / (N + 1) * d) := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hj).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [Real.dist_eq, ← hsplit]
  calc _ ≤ (K : ℝ) * (ε / (N + 1) * d) := hsum
    _ = N * ε / (N + 1) := by
      rw [show (K : ℝ) * (ε / (N + 1) * d) = (K * d) * ε / (N + 1) by ring, hKd]
    _ < ε := by
      rw [div_lt_iff₀ hN1]; nlinarith

theorem avg_real_of_nat {φ : ℝ → ℝ} (hφ : Continuous φ) {B : ℝ} (hB : ∀ s, |φ s| ≤ B) {c : ℝ}
    (h : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∫ s in (0 : ℝ)..N, φ s) atTop (𝓝 c)) :
    Tendsto (fun T : ℝ => T⁻¹ * ∫ s in (0 : ℝ)..T, φ s) atTop (𝓝 c) := by
  have hfl := h.comp (tendsto_nat_floor_atTop (α := ℝ))
  have he : Tendsto (fun T : ℝ => 2 * B / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  refine hfl.congr_dist (squeeze_zero' (Eventually.of_forall fun T => dist_nonneg) ?_ he)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  simp only [Function.comp]
  have hF1 : (1 : ℝ) ≤ (⌊T⌋₊ : ℝ) := by
    have : 1 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    exact_mod_cast this
  have hFT : (⌊T⌋₊ : ℝ) ≤ T := Nat.floor_le (by linarith)
  have hTF : T < (⌊T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one T
  set F : ℝ := (⌊T⌋₊ : ℝ) with hF_def
  have hint : ∀ a b : ℝ, IntervalIntegrable φ volume a b := fun a b => hφ.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 F) (hint F T)]
  set a := ∫ s in (0 : ℝ)..F, φ s with ha_def
  set r := ∫ s in F..T, φ s with hr_def
  have hFpos : (0 : ℝ) < F := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  have ha : |a| ≤ B * F := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := F) (C := B)
      (f := φ) (fun s _ => by rw [Real.norm_eq_abs]; exact hB s)
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hFpos] at this
    exact this
  have hr : |r| ≤ B * (T - F) := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := F) (b := T) (C := B)
      (f := φ) (fun s _ => by rw [Real.norm_eq_abs]; exact hB s)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hFT)] at this
    exact this
  rw [Real.dist_eq]
  have e : F⁻¹ * a - T⁻¹ * (a + r) = (a * (T - F) - r * F) / (T * F) := by
    field_simp; ring
  have hTF' : 0 ≤ T - F := sub_nonneg.2 hFT
  have i1 : |a| * (T - F) ≤ B * F * 1 :=
    calc |a| * (T - F) ≤ (B * F) * (T - F) := mul_le_mul_of_nonneg_right ha hTF'
      _ ≤ B * F * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have i2 : |r| * F ≤ B * F * 1 :=
    calc |r| * F ≤ B * (T - F) * F := mul_le_mul_of_nonneg_right hr hFpos.le
      _ = B * F * (T - F) := by ring
      _ ≤ B * F * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h1 : |a * (T - F) - r * F| ≤ 2 * B * F := by
    have := abs_sub (a * (T - F)) (r * F)
    rw [abs_mul, abs_mul, abs_of_nonneg hTF', abs_of_pos hFpos] at this
    linarith
  rw [e, abs_div, abs_of_pos (mul_pos hTpos hFpos), div_le_div_iff₀ (mul_pos hTpos hFpos) hTpos]
  have := mul_le_mul_of_nonneg_right h1 hTpos.le
  linarith

/-- density: a continuous function `≤ 0` at all rationals `≥ N` is `≤ 0` at all reals `≥ N`. -/
theorem le_of_rat0 {φ : ℝ → ℝ} (hφ : Continuous φ) {N : ℝ}
    (h : ∀ q : ℚ, N ≤ q → φ q ≤ 0) : ∀ s : ℝ, N ≤ s → φ s ≤ 0 := by
  intro s hs
  by_contra hlt
  push_neg at hlt
  obtain ⟨ε, hε, hball⟩ :=
    Metric.eventually_nhds_iff.mp (hφ.continuousAt.eventually (lt_mem_nhds hlt))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show s < s + ε by linarith)
  have hd : dist (q : ℝ) s < ε := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  exact absurd (h q (hs.trans hq1.le)) (not_le.mpr (hball hd))

/-- the closed rational rate condition. -/
def RratR (L : ℝ) (ψ : ℝ → ℝ) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ q : ℚ, (N : ℚ) ≤ q →
    Real.exp ((L - ε) * q) ≤ |ψ q| ∧ |ψ q| ≤ Real.exp ((L + ε) * q)

theorem rate_iff {ψ : ℝ → ℝ} (hψ : Continuous ψ) {L : ℝ} (hL : L < 0) :
    RratR L ψ ↔ Tendsto (fun t : ℝ≥0 => Real.log (ψ t) / t) atTop (𝓝 L) := by
  constructor
  · intro hR
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨ε', hε'0, hε'1⟩ := exists_rat_btwn hε
    obtain ⟨N, hN⟩ := hR ε' (by exact_mod_cast hε'0)
    have hlo := le_of_rat0 (φ := fun s => Real.exp ((L - ε') * s) - |ψ s|) (by fun_prop)
      (N := N) (fun q hq => by
        have := (hN q (by exact_mod_cast hq)).1
        linarith)
    have hhi := le_of_rat0 (φ := fun s => |ψ s| - Real.exp ((L + ε') * s)) (by fun_prop)
      (N := N) (fun q hq => by
        have := (hN q (by exact_mod_cast hq)).2
        linarith)
    refine ⟨max (N : ℝ≥0) 1, fun t ht => ?_⟩
    have ht1 : (1 : ℝ) ≤ t := by
      have := le_trans (le_max_right _ _) ht; exact_mod_cast this
    have htN : (N : ℝ) ≤ t := by
      have := le_trans (le_max_left _ _) ht; exact_mod_cast this
    have h1 := hlo t htN
    have h2 := hhi t htN
    have hpos : 0 < |ψ t| := lt_of_lt_of_le (Real.exp_pos ((L - ε') * t)) (by linarith)
    have hlog1 : (L - ε') * t ≤ Real.log (ψ t) := by
      rw [← Real.log_abs, ← Real.log_exp ((L - ε') * t)]
      exact Real.log_le_log (Real.exp_pos _) (by linarith)
    have hlog2 : Real.log (ψ t) ≤ (L + ε') * t := by
      rw [← Real.log_abs, ← Real.log_exp ((L + ε') * t)]
      exact Real.log_le_log hpos (by linarith)
    have htpos : (0 : ℝ) < t := by linarith
    have hεt := mul_lt_mul_of_pos_right hε'1 htpos
    rw [Real.dist_eq, abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ htpos]; linarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ htpos]; linarith
  · intro hT ε hε
    have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
    have hδ : 0 < min (ε : ℝ) (-L / 2) := lt_min hε' (by linarith)
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hT _ hδ
    refine ⟨⌈max (N0 : ℝ) 1⌉₊, fun q hq => ?_⟩
    have hq' : max (N0 : ℝ) 1 ≤ q := le_trans (Nat.le_ceil _) (by exact_mod_cast hq)
    have hqpos : (0 : ℝ) < q := by linarith [le_max_right (N0 : ℝ) 1]
    have htq : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hqpos.le
    have hd := hN0 (q : ℝ).toNNReal (by
      show N0 ≤ _
      rw [← NNReal.coe_le_coe, htq]; linarith [le_max_left (N0 : ℝ) 1])
    rw [htq, Real.dist_eq, abs_lt] at hd
    set u := Real.log (ψ q) / q with hu
    have hlog : Real.log (ψ q) = u * q := (div_mul_cancel₀ _ hqpos.ne').symm
    have hm1 := min_le_left (ε : ℝ) (-L / 2)
    have hm2 := min_le_right (ε : ℝ) (-L / 2)
    have hlo : (L - ε) * q ≤ u * q := mul_le_mul_of_nonneg_right (by linarith [hd.1]) hqpos.le
    have hhi : u * q ≤ (L + ε) * q := mul_le_mul_of_nonneg_right (by linarith [hd.2]) hqpos.le
    have hneg : u * q < 0 := mul_neg_of_neg_of_pos (by linarith [hd.2]) hqpos
    have hne : ψ q ≠ 0 := by
      intro h0
      rw [h0, Real.log_zero] at hlog
      linarith
    have habs : |ψ q| = Real.exp (u * q) := by
      rw [← hlog, ← Real.log_abs, Real.exp_log (abs_pos.2 hne)]
    rw [habs]
    exact ⟨Real.exp_le_exp.2 hlo, Real.exp_le_exp.2 hhi⟩

end StochKolmogorov.Classify.Riem

end Mod_Riem

-- ===== module Gam2 =====
section Mod_Gam2

/-! K2-Γ (8f909832): the measurable rational path set `Gam C μ` for a sink `μ`:
closed exponential-rate bounds `|f q i| ∈ [e^{(λᵢ-ε)q}, e^{(λᵢ+ε)q}]` for `i ∉ supp μ` and Riemann-sum
averages of the countable tent family `Dfam.hD`. For a continuous path:
* `mem_Gam_iff`: `rpath X x ω ∈ Gam C μ ↔ RC C μ X x ω` (real-time rates + occupation averages);
* `shift_mem_iff`: membership is invariant under every time shift;
* `extinct_of_RC` / `RC_of_extinct` (the latter under the tightness of Lemma 5.7). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Gam2

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- closed rate condition on a rational path. -/
def Rrat (i : Fin n) (L : ℝ) (f : ℚ → SDEState n) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ q : ℚ, (N : ℚ) ≤ q →
    Real.exp ((L - ε) * q) ≤ |f q i| ∧ |f q i| ≤ Real.exp ((L + ε) * q)

/-- normalized left Riemann sum of `h ∘ f` over `[0, N]` with mesh `1/m`. -/
noncomputable def rsum (h : SDEState n → ℝ) (f : ℚ → SDEState n) (N m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (N * m), (1 / ((N : ℝ) * m)) * h (f ((j : ℚ) / m))

/-- the average condition: Riemann averages over `[0, N+1]` are eventually `ε`-close to `c`. -/
def Arat (h : SDEState n → ℝ) (c : ℝ) (f : ℚ → SDEState n) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    |rsum h f (N + 1) (m + 1) - c| ≤ ε

/-- the path set of the sink `μ`. -/
def Gam (C : Coeffs n) (μ : Measure (SDEState n)) : Set (ℚ → SDEState n) :=
  {f | (∀ i, i ∉ supp μ → Rrat i (lyap C i μ) f ∧ lyap C i μ < 0) ∧
    ∀ (s : Finset ℕ) (k : ℕ), Arat (Dfam.hD s k) (∫ y, Dfam.hD s k y ∂μ) f}

theorem measurable_coord (q : ℚ) (i : Fin n) : Measurable fun f : ℚ → SDEState n => f q i := by
  have h1 : Continuous fun y : SDEState n => y i := PiLp.continuous_apply 2 _ i
  exact h1.measurable.comp (measurable_pi_apply q)

theorem measurable_rsum {h : SDEState n → ℝ} (hh : Continuous h) (N m : ℕ) :
    Measurable fun f : ℚ → SDEState n => rsum h f N m := by
  unfold rsum
  exact Finset.measurable_sum _ fun j _ =>
    (hh.measurable.comp (measurable_pi_apply ((j : ℚ) / m))).const_mul _

theorem measurableSet_Gam (C : Coeffs n) (μ : Measure (SDEState n)) :
    MeasurableSet (Gam C μ) := by
  have e : Gam C μ = (⋂ i, ⋂ (_ : i ∉ supp μ), ((⋂ ε : ℚ, ⋂ (_ : 0 < ε), ⋃ N : ℕ, ⋂ q : ℚ,
      ⋂ (_ : (N : ℚ) ≤ q),
      ({f : ℚ → SDEState n | Real.exp ((lyap C i μ - ε) * q) ≤ |f q i|} ∩
        {f | |f q i| ≤ Real.exp ((lyap C i μ + ε) * q)})) ∩ {_f | lyap C i μ < 0})) ∩
      ⋂ (s : Finset ℕ), ⋂ (k : ℕ), ⋂ ε : ℚ, ⋂ (_ : 0 < ε), ⋃ N0 : ℕ, ⋂ N : ℕ, ⋂ (_ : N0 ≤ N),
      ⋃ M : ℕ, ⋂ m : ℕ, ⋂ (_ : M ≤ m),
      {f | |rsum (Dfam.hD s k) f (N + 1) (m + 1) - ∫ y, Dfam.hD s k y ∂μ| ≤ ε} := by
    ext f
    simp only [Gam, Rrat, Arat, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_iUnion]
  rw [e]
  have habs : ∀ (q : ℚ) (i : Fin n), Measurable fun f : ℚ → SDEState n => |f q i| :=
    fun q i => (measurable_coord q i).abs
  refine MeasurableSet.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    MeasurableSet.inter (MeasurableSet.iInter fun ε => MeasurableSet.iInter fun _ =>
      MeasurableSet.iUnion fun N => MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ =>
        MeasurableSet.inter (measurableSet_le measurable_const (habs q i))
          (measurableSet_le (habs q i) measurable_const))
      (MeasurableSet.const _))
    (MeasurableSet.iInter fun s => MeasurableSet.iInter fun k => MeasurableSet.iInter fun ε =>
      MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun N0 => MeasurableSet.iInter fun N =>
      MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun M => MeasurableSet.iInter fun m =>
      MeasurableSet.iInter fun _ => measurableSet_le
        (((measurable_rsum (Dfam.hD s k).continuous _ _).sub_const _).abs) measurable_const)

theorem rrat_iff (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (i : Fin n) {L : ℝ} (hL : L < 0) :
    Rrat i L (K3.rpath X x ω) ↔
      Tendsto (fun t : ℝ≥0 => Real.log (X x t ω i) / t) atTop (𝓝 L) := by
  have hψ : Continuous fun s : ℝ => X x s.toNNReal ω i :=
    (PiLp.continuous_apply 2 _ i).comp (hc.comp continuous_real_toNNReal)
  have := Riem.rate_iff hψ hL
  simp only [Real.toNNReal_coe] at this
  exact this

theorem arat_iff (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (h : SDEState n →ᵇ ℝ) (c : ℝ) :
    Arat h c (K3.rpath X x ω) ↔
      Tendsto (fun T : ℝ => ∫ y, h y ∂(occ X x T ω)) atTop (𝓝 c) := by
  set φ : ℝ → ℝ := fun s => h (X x s.toNNReal ω) with hφ_def
  have hφ : Continuous φ := h.continuous.comp (hc.comp continuous_real_toNNReal)
  have hB : ∀ s, |φ s| ≤ ‖h‖ := fun s => by
    rw [← Real.norm_eq_abs]; exact h.norm_coe_le_norm _
  set g : ℕ → ℝ := fun N => (N : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(N : ℝ), φ s with hg
  have hrs : ∀ N : ℕ, Tendsto (fun m : ℕ => rsum h (K3.rpath X x ω) (N + 1) (m + 1)) atTop
      (𝓝 (g (N + 1))) := by
    intro N
    have := (Riem.riemann_tendsto hφ (N + 1)).const_mul (((N + 1 : ℕ) : ℝ)⁻¹)
    refine this.congr fun m => ?_
    unfold rsum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc]
    congr 1
    · push_cast; field_simp
    · show h (X x ((j : ℝ) * (1 / ((m : ℝ) + 1))).toNNReal ω) =
        h (X x ((((j : ℚ) / ((m + 1 : ℕ) : ℚ) : ℚ) : ℝ)).toNNReal ω)
      rw [show ((((j : ℚ) / ((m + 1 : ℕ) : ℚ) : ℚ) : ℝ)) = (j : ℝ) * (1 / ((m : ℝ) + 1)) by
        push_cast; ring]
  have hA : Arat h c (K3.rpath X x ω) ↔ Tendsto (fun N : ℕ => g (N + 1)) atTop (𝓝 c) := by
    constructor
    · intro hA
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨ε', hε'0, hε'1⟩ := exists_rat_btwn hε
      obtain ⟨N0, hN0⟩ := hA ε' (by exact_mod_cast hε'0)
      refine ⟨N0, fun N hN => ?_⟩
      obtain ⟨M, hM⟩ := hN0 N hN
      have hlim := ((hrs N).sub_const c).abs
      have hle : |g (N + 1) - c| ≤ ε' :=
        le_of_tendsto hlim (eventually_atTop.2 ⟨M, fun m hm => hM m hm⟩)
      rw [Real.dist_eq]; linarith
    · intro hT ε hε
      have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
      obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hT (ε / 2) (by linarith)
      refine ⟨N0, fun N hN => ?_⟩
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 (hrs N) (ε / 2) (by linarith)
      refine ⟨M, fun m hm => ?_⟩
      have h1 := hN0 N hN
      have h2 := hM m hm
      rw [Real.dist_eq] at h1 h2
      have := abs_sub_le (rsum h (K3.rpath X x ω) (N + 1) (m + 1)) (g (N + 1)) c
      linarith
  rw [hA, Filter.tendsto_add_atTop_iff_nat 1]
  have hocc : (fun T : ℝ => ∫ y, h y ∂(occ X x T ω)) =ᶠ[atTop]
      fun T : ℝ => T⁻¹ * ∫ s in (0 : ℝ)..T, φ s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact Shift.occ_integral X x ω hc hT h
  rw [tendsto_congr' hocc]
  constructor
  · exact Riem.avg_real_of_nat hφ hB
  · intro hT
    exact hT.comp tendsto_natCast_atTop_atTop

/-- the real-time conditions. -/
def RC (C : Coeffs n) (μ : Measure (SDEState n)) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (x : SDEState n) (ω : Ω) : Prop :=
  (∀ i, i ∉ supp μ →
    Tendsto (fun t : ℝ≥0 => Real.log (X x t ω i) / t) atTop (𝓝 (lyap C i μ)) ∧ lyap C i μ < 0) ∧
  ∀ (s : Finset ℕ) (k : ℕ), Tendsto (fun T : ℝ => ∫ y, Dfam.hD s k y ∂(occ X x T ω)) atTop
    (𝓝 (∫ y, Dfam.hD s k y ∂μ))

theorem mem_Gam_iff (C : Coeffs n) (μ : Measure (SDEState n))
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) :
    K3.rpath X x ω ∈ Gam C μ ↔ RC C μ X x ω := by
  refine and_congr (forall_congr' fun i => imp_congr_right fun _ => ?_)
    (forall_congr' fun s => forall_congr' fun k => arat_iff X x ω hc _ _)
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(rrat_iff X x ω hc i h2).1 h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(rrat_iff X x ω hc i h2).2 h1, h2⟩

theorem RC_shift (C : Coeffs n) (μ : Measure (SDEState n))
    (X X' : SDEState n → ℝ≥0 → Ω → SDEState n) (x x' : SDEState n) (ω ω' : Ω) (t : ℝ≥0)
    (hs : ∀ s, X' x' s ω' = X x (t + s) ω) (hc : Continuous fun s => X x s ω) :
    RC C μ X' x' ω' ↔ RC C μ X x ω := by
  refine and_congr (forall_congr' fun i => imp_congr_right fun _ => and_congr ?_ Iff.rfl)
    (forall_congr' fun s => forall_congr' fun k => ?_)
  · simp only [hs]
    exact Shift.rate_shift (fun u => Real.log (X x u ω i)) t _
  · have he : Tendsto (fun T : ℝ => 2 * t * ‖Dfam.hD (E := SDEState n) s k‖ / T) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hclose : ∀ᶠ T in atTop, dist (∫ y, Dfam.hD s k y ∂(occ X x T ω))
        (∫ y, Dfam.hD s k y ∂(occ X' x' T ω')) ≤ 2 * t * ‖Dfam.hD (E := SDEState n) s k‖ / T := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      rw [Real.dist_eq]; exact Shift.occ_shift_close X X' x x' ω ω' t hs hc hT _
    have hd := squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) hclose he
    have hd' : Tendsto (fun T => dist (∫ y, Dfam.hD s k y ∂(occ X' x' T ω'))
        (∫ y, Dfam.hD s k y ∂(occ X x T ω))) atTop (𝓝 0) := by
      simpa only [dist_comm] using hd
    exact ⟨fun h' => h'.congr_dist hd', fun h => h.congr_dist hd⟩

theorem shift_mem_iff (C : Coeffs n) (μ : Measure (SDEState n))
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (t : ℝ≥0) :
    K4.shiftPath X x t ω ∈ Gam C μ ↔ K3.rpath X x ω ∈ Gam C μ := by
  have hct : Continuous fun s => X x (t + s) ω := hc.comp (continuous_const.add continuous_id)
  have e : K4.shiftPath X x t ω = K3.rpath (fun y s ω => X y (t + s) ω) x ω := rfl
  rw [e, mem_Gam_iff C μ _ x ω hct, mem_Gam_iff C μ X x ω hc]
  exact RC_shift C μ X _ x x ω ω t (fun s => rfl) hc

theorem extinct_of_RC (C : Coeffs n) (μ : Measure (SDEState n)) [IsProbabilityMeasure μ]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω) (h : RC C μ X x ω) : ω ∈ extinctEvent C X x μ :=
  ⟨LimOcc.limitSet_eq_of_avg X x ω hc μ h.2, h.1⟩

theorem RC_of_extinct (C : Coeffs n) (μ : Measure (SDEState n))
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω)
    (hT : IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X x t ω})
    (h : ω ∈ extinctEvent C X x μ) : RC C μ X x ω :=
  ⟨h.2, fun s k => LimOcc.avg_of_limitSet X x ω hc μ h.1 hT _⟩

end StochKolmogorov.Classify.Gam2

end Mod_Gam2

-- ===== module K2cov =====
section Mod_K2cov

/-! K2 (8f909832) modulo (5.40): with `Γ = ⋃_{μ ∈ M¹} Gam C μ` (measurable, shift invariant), Lemma 5.7
tightness at the points of `K` and `P(E_μ^y) ≥ 1/2` on `K` (Lemma 5.9), the recurrence (5.40) to `K`
gives `P(⋃_{μ ∈ M¹} E_μ^x) = 1`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K2cov

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem cover_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (hM1 : (M1 P C X).Finite) (hprob : ∀ μ ∈ M1 P C X, IsProbabilityMeasure μ)
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X y t ω})
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (K : Set (SDEState n)) (hK : MeasurableSet K)
    (hKμ : ∀ y ∈ K, y ∈ orthant n ∧ ∃ μ ∈ M1 P C X,
      (1 : ℝ) / 2 ≤ (P (extinctEvent C X y μ)).toReal)
    (hrec : ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c ≤ (N⁻¹ : ℝ) * ∫ s in (0 : ℝ)..N, K.indicator 1 (X x (s + 1).toNNReal ω)) :
    ∀ᵐ ω ∂P, ∃ μ ∈ M1 P C X, ω ∈ extinctEvent C X x μ := by
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hcont : ∀ y ∈ orthant n, ∀ ω, Continuous fun s => X y s ω :=
    fun y hy ω => (hX.2.2 y hy).2.1 ω
  set Γ : Set (ℚ → SDEState n) := ⋃ μ ∈ M1 P C X, Gam2.Gam C μ with hΓ_def
  have hΓ : MeasurableSet Γ :=
    MeasurableSet.biUnion hM1.countable fun μ _ => Gam2.measurableSet_Gam C μ
  have hΓinv : ∀ (t : ℝ≥0) (ω : Ω), K4.shiftPath X x t ω ∈ Γ ↔ K4.shiftPath X x 1 ω ∈ Γ := by
    intro t ω
    simp only [hΓ_def, Set.mem_iUnion]
    refine exists_congr fun μ => exists_congr fun _ => ?_
    rw [Gam2.shift_mem_iff C μ X x ω (hcont x hxo ω) t,
      Gam2.shift_mem_iff C μ X x ω (hcont x hxo ω) 1]
  have hhK : ∀ y ∈ K, (1 : ℝ) / 2 ≤ (P (K4.Zf X y ⁻¹' Γ)).toReal := by
    intro y hy
    obtain ⟨hyo, μ, hμ, hle⟩ := hKμ y hy
    have hsub : extinctEvent C X y μ ≤ᵐ[P] K4.Zf X y ⁻¹' Γ := by
      filter_upwards [h57 y hyo] with ω hT hE
      have hZ : K4.Zf X y ω = K3.rpath X y ω := by simp [K4.Zf, hyo]
      show K4.Zf X y ω ∈ Γ
      rw [hZ, hΓ_def, Set.mem_iUnion₂]
      exact ⟨μ, hμ, (Gam2.mem_Gam_iff C μ X y ω (hcont y hyo ω)).2
        (Gam2.RC_of_extinct C μ X y ω (hcont y hyo ω) hT hE)⟩
    exact hle.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub))
  have hmain := K2fin.cover_of_levy P C B X hX hC hinv x hx Γ hΓ hΓinv K hK hhK hrec
  filter_upwards [hmain] with ω hω
  rw [hΓ_def, Set.mem_iUnion₂] at hω
  obtain ⟨μ, hμ, hm⟩ := hω
  haveI := hprob μ hμ
  rw [Gam2.shift_mem_iff C μ X x ω (hcont x hxo ω) 1,
    Gam2.mem_Gam_iff C μ X x ω (hcont x hxo ω)] at hm
  exact ⟨μ, hμ, Gam2.extinct_of_RC C μ X x ω (hcont x hxo ω) hm⟩

end StochKolmogorov.Classify.K2cov

end Mod_K2cov

-- ===== module Rec540 =====
section Mod_Rec540

/-! (5.39) ⇒ (5.40) for one path (8f909832, K2): if the occupation measures are tight and every limit
point `π` gives `∫ ψ dπ > 0` for a function `0 ≤ ψ ≤ 1` with `ψ ≤ 1_K` along the path, then the
path spends a positive lower fraction of time in `K` (grid form used by `K2fin.cover_of_levy`).
`K2_of_U`: K2 from K1, Lemma 5.7 (tightness), Lemma 5.9 (via `hKμ`), interior invariance and (5.39). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Rec540

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- a limit point along any sequence of times `≥ 1` tending to infinity (Prokhorov). -/
theorem exists_limit (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω)
    (hT : IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X x t ω})
    (ts : ℕ → ℝ) (h1 : ∀ k, 1 ≤ ts k) (hts : Tendsto ts atTop atTop) :
    ∃ π ∈ limitSet X x ω, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ h : SDEState n →ᵇ ℝ,
      Tendsto (fun k => ∫ y, h y ∂(occ X x (ts (φ k)) ω)) atTop (𝓝 (∫ y, h y ∂π)) := by
  let S : Set (ProbabilityMeasure (SDEState n)) :=
    {ν | ∃ t : ℝ, 1 ≤ t ∧ (ν : Measure (SDEState n)) = occ X x t ω}
  have hS : IsTightMeasureSet {((ν : ProbabilityMeasure (SDEState n)) : Measure (SDEState n)) |
      ν ∈ S} := by
    refine hT.subset ?_
    rintro _ ⟨ν, ⟨t, ht, he⟩, rfl⟩
    exact ⟨t, ht, he⟩
  have hK := isCompact_closure_of_isTightMeasureSet hS
  let νs : ℕ → ProbabilityMeasure (SDEState n) := fun k =>
    ⟨occ X x (ts k) ω, LimOcc.isProb_occ X x ω hc (lt_of_lt_of_le one_pos (h1 k))⟩
  have hmem : ∀ k, νs k ∈ closure S := fun k => subset_closure ⟨ts k, h1 k, rfl⟩
  obtain ⟨π, -, φ, hφ, hπ⟩ := hK.tendsto_subseq hmem
  have hint := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hπ
  refine ⟨π, ⟨inferInstance, fun k => ts (φ k), fun k => h1 _, hts.comp hφ.tendsto_atTop,
    fun g => hint g⟩, φ, hφ, fun g => hint g⟩

theorem eventually_pos (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω)
    (hT : IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X x t ω})
    (ψ : SDEState n →ᵇ ℝ) (hψ0 : ∀ y, 0 ≤ ψ y)
    (hpos : ∀ π ∈ limitSet X x ω, 0 < ∫ y, ψ y ∂π) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop, c ≤ ∫ y, ψ y ∂(occ X x T ω) := by
  by_contra hne
  push_neg at hne
  -- for every `k` there are arbitrarily large `T` with a small average
  have hfr : ∀ k : ℕ, ∃ T : ℝ, (k : ℝ) + 1 ≤ T ∧ ∫ y, ψ y ∂(occ X x T ω) < 1 / ((k : ℝ) + 1) := by
    intro k
    have h := hne (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨T, hT1, hT2⟩ := (h.and_eventually (eventually_ge_atTop ((k : ℝ) + 1))).exists
    exact ⟨T, hT2, hT1⟩
  choose ts hts1 hts2 using hfr
  have h1 : ∀ k, 1 ≤ ts k := fun k => le_trans (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    (hts1 k)
  have htt : Tendsto ts atTop atTop :=
    tendsto_atTop_mono hts1 (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  obtain ⟨π, hπ, φ, hφ, hlim⟩ := exists_limit X x ω hc hT ts h1 htt
  have hle : ∫ y, ψ y ∂π ≤ 0 := by
    have hz : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    refine le_of_tendsto_of_tendsto (hlim ψ) hz (Eventually.of_forall fun k => ?_)
    exact (hts2 (φ k)).le
  exact absurd (hpos π hπ) (not_lt.2 hle)

theorem rec_of_pos (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (ω : Ω)
    (hc : Continuous fun s => X x s ω)
    (hT : IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X x t ω})
    (ψ : SDEState n →ᵇ ℝ) (hψ0 : ∀ y, 0 ≤ ψ y) (hψ1 : ∀ y, ψ y ≤ 1)
    (K : Set (SDEState n)) (hK : MeasurableSet K)
    (hψK : ∀ s : ℝ≥0, ψ (X x s ω) ≤ K.indicator 1 (X x s ω))
    (hpos : ∀ π ∈ limitSet X x ω, 0 < ∫ y, ψ y ∂π) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c ≤ (N⁻¹ : ℝ) * ∫ s in (0 : ℝ)..N, K.indicator 1 (X x (s + 1).toNNReal ω) := by
  obtain ⟨c0, hc0, hev⟩ := eventually_pos X x ω hc hT ψ hψ0 hpos
  refine ⟨c0 / 2, half_pos hc0, ?_⟩
  have hev' := (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop).eventually hev
  obtain ⟨N1, hN1⟩ := exists_nat_gt (2 / c0)
  filter_upwards [hev', eventually_ge_atTop (max N1 1)] with N hN hNge
  have hN1' : (N1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hNge
  have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hNge
  set g : ℝ → ℝ := fun u => K.indicator (1 : SDEState n → ℝ) (X x u.toNNReal ω) with hg
  set p : ℝ → ℝ := fun u => ψ (X x u.toNNReal ω) with hp
  have hpc : Continuous p := ψ.continuous.comp (hc.comp continuous_real_toNNReal)
  have hgm : Measurable g :=
    (measurable_const.indicator hK).comp (hc.comp continuous_real_toNNReal).measurable
  have hg1 : ∀ u, |g u| ≤ 1 := fun u => by
    simp only [hg, Set.indicator]
    split_ifs <;> simp
  have hpg : ∀ u, p u ≤ g u := fun u => hψK _
  have e1 : ∫ s in (0 : ℝ)..N, K.indicator 1 (X x (s + 1).toNNReal ω) =
      ∫ u in (1 : ℝ)..((N : ℝ) + 1), g u := by
    have := intervalIntegral.integral_comp_add_right g (1 : ℝ) (a := 0) (b := (N : ℝ))
    rw [zero_add] at this
    exact this
  rw [e1]
  have hocc := Shift.occ_integral X x ω hc (show (0 : ℝ) < (N : ℝ) + 1 by positivity) ψ
  have hN : c0 ≤ ((N : ℝ) + 1)⁻¹ * ∫ u in (0 : ℝ)..((N : ℝ) + 1), p u := by
    rw [← hocc]; exact hN
  have hsplit : ∫ u in (0 : ℝ)..((N : ℝ) + 1), p u =
      (∫ u in (0 : ℝ)..1, p u) + ∫ u in (1 : ℝ)..((N : ℝ) + 1), p u :=
    (intervalIntegral.integral_add_adjacent_intervals (hpc.intervalIntegrable _ _)
      (hpc.intervalIntegrable _ _)).symm
  have h01 : ∫ u in (0 : ℝ)..1, p u ≤ 1 := by
    have := intervalIntegral.integral_mono_on (zero_le_one' ℝ) (hpc.intervalIntegrable 0 1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1) fun u _ => hψ1 (X x u.toNNReal ω)
    simpa using this
  have hpg' : ∫ u in (1 : ℝ)..((N : ℝ) + 1), p u ≤ ∫ u in (1 : ℝ)..((N : ℝ) + 1), g u :=
    intervalIntegral.integral_mono_on (by linarith) (hpc.intervalIntegrable _ _)
      (K2fin.intervalIntegrable_of_bdd hgm hg1 _ _) fun u _ => hpg u
  have hNp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hmul : c0 * ((N : ℝ) + 1) ≤ ∫ u in (0 : ℝ)..((N : ℝ) + 1), p u := by
    have := mul_le_mul_of_nonneg_left hN hNp.le
    rw [← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul] at this
    linarith
  set I := ∫ u in (1 : ℝ)..((N : ℝ) + 1), g u
  have hI : c0 * N + c0 - 1 ≤ I := by linarith
  have hc2 : 2 < c0 * N := by
    have := (div_lt_iff₀ hc0).1 (lt_of_lt_of_le hN1 hN1')
    linarith
  rw [le_inv_mul_iff₀ (by linarith)]
  nlinarith

/-- K2 from K1 (`hM1`), Lemma 5.7 tightness (`h57`), Lemma 5.9 (`hKμ`), interior invariance (`hint`) and
(5.39) (`hU`) for a cut-off `0 ≤ ψ ≤ 1` with `ψ ≤ 1_K` on the open orthant. -/
theorem K2_of_U [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (hM1 : (M1 P C X).Finite) (hprob : ∀ μ ∈ M1 P C X, IsProbabilityMeasure μ)
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X y t ω})
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (K : Set (SDEState n)) (hK : MeasurableSet K)
    (hKμ : ∀ y ∈ K, y ∈ orthant n ∧ ∃ μ ∈ M1 P C X,
      (1 : ℝ) / 2 ≤ (P (extinctEvent C X y μ)).toReal)
    (ψ : SDEState n →ᵇ ℝ) (hψ0 : ∀ y, 0 ≤ ψ y) (hψ1 : ∀ y, ψ y ≤ 1)
    (hψK : ∀ y ∈ openOrthant n, ψ y ≤ K.indicator 1 y)
    (hint : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, X x s ω ∈ openOrthant n)
    (hU : ∀ᵐ ω ∂P, ∀ π ∈ limitSet X x ω, 0 < ∫ y, ψ y ∂π) :
    ∀ᵐ ω ∂P, ∃ μ ∈ M1 P C X, ω ∈ extinctEvent C X x μ := by
  have hxo : x ∈ orthant n := fun i => (hx i).le
  refine K2cov.cover_of P C B X hX hC hinv hM1 hprob h57 x hx K hK hKμ ?_
  filter_upwards [h57 x hxo, hint, hU] with ω hT hin hpos
  exact rec_of_pos X x ω ((hX.2.2 x hxo).2.1 ω) hT ψ hψ0 hψ1 K hK (fun s => hψK _ (hin s)) hpos

end StochKolmogorov.Classify.Rec540

end Mod_Rec540

-- ===== module Psi =====
section Mod_Psi

/-! The cut-off `ψ` of (5.39) (8f909832, K2): `ψ = min 1 (∑_{μ ∈ S} φ_μ)` with `φ_μ` a product of
coordinate tents, `φ_μ = 1` on the face box `K⁰_μ` (`k0⁻¹ ≤ yᵢ ≤ k0` on `supp μ`, `yᵢ = 0` off it) and
`φ_μ(y) > 0 ⇒ y ∈ Kbox μ k Δ` for interior `y`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Psi

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

/-- tent: `1` on `[k0⁻¹, k0]`, `0` outside `(k⁻¹, k)`. -/
noncomputable def ta (k0 k : ℝ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - k⁻¹) / (k0⁻¹ - k⁻¹)) ((k - t) / (k - k0))))

/-- tent: `1` at `t ≤ 0`, `0` at `t ≥ Δ`. -/
noncomputable def tb (Δ : ℝ) (t : ℝ) : ℝ := max 0 (min 1 (1 - t / Δ))

theorem continuous_ta (k0 k : ℝ) : Continuous (ta k0 k) := by unfold ta; fun_prop
theorem continuous_tb (Δ : ℝ) : Continuous (tb Δ) := by unfold tb; fun_prop

theorem ta_nonneg (k0 k t : ℝ) : 0 ≤ ta k0 k t := le_max_left _ _
theorem tb_nonneg (Δ t : ℝ) : 0 ≤ tb Δ t := le_max_left _ _
theorem ta_le_one (k0 k t : ℝ) : ta k0 k t ≤ 1 := max_le zero_le_one (min_le_left _ _)
theorem tb_le_one (Δ t : ℝ) : tb Δ t ≤ 1 := max_le zero_le_one (min_le_left _ _)

theorem ta_pos {k0 k t : ℝ} (hk0 : 1 ≤ k0) (hk : k0 < k) (h : 0 < ta k0 k t) :
    k⁻¹ < t ∧ t < k := by
  have hk0p : 0 < k0 := by linarith
  have hd1 : 0 < k0⁻¹ - k⁻¹ := sub_pos.2 (inv_strictAnti₀ hk0p hk)
  have hd2 : 0 < k - k0 := sub_pos.2 hk
  unfold ta at h
  have h1 : 0 < min 1 (min ((t - k⁻¹) / (k0⁻¹ - k⁻¹)) ((k - t) / (k - k0))) := by
    by_contra hc
    push_neg at hc
    rw [max_eq_left hc] at h
    exact lt_irrefl _ h
  have h2 := (lt_min_iff.1 (lt_min_iff.1 h1).2)
  exact ⟨by have := (div_pos_iff_of_pos_right hd1).1 h2.1; linarith,
    by have := (div_pos_iff_of_pos_right hd2).1 h2.2; linarith⟩

theorem ta_eq_one {k0 k t : ℝ} (hk0 : 1 ≤ k0) (hk : k0 < k) (h1 : k0⁻¹ ≤ t) (h2 : t ≤ k0) :
    ta k0 k t = 1 := by
  have hk0p : 0 < k0 := by linarith
  have hd1 : 0 < k0⁻¹ - k⁻¹ := sub_pos.2 (inv_strictAnti₀ hk0p hk)
  have hd2 : 0 < k - k0 := sub_pos.2 hk
  have e1 : 1 ≤ (t - k⁻¹) / (k0⁻¹ - k⁻¹) := by rw [le_div_iff₀ hd1]; linarith
  have e2 : 1 ≤ (k - t) / (k - k0) := by rw [le_div_iff₀ hd2]; linarith
  unfold ta
  rw [min_eq_left (le_min e1 e2), max_eq_right zero_le_one]

theorem tb_pos {Δ t : ℝ} (hΔ : 0 < Δ) (h : 0 < tb Δ t) : t < Δ := by
  unfold tb at h
  have h1 : 0 < min 1 (1 - t / Δ) := by
    by_contra hc
    push_neg at hc
    rw [max_eq_left hc] at h
    exact lt_irrefl _ h
  have h2 := (lt_min_iff.1 h1).2
  have : t / Δ < 1 := by linarith
  rwa [div_lt_one hΔ] at this

theorem tb_zero (Δ : ℝ) : tb Δ 0 = 1 := by
  unfold tb; simp

open Classical in
/-- the product tent of the sink `μ`. -/
noncomputable def phi (μ : Measure (SDEState n)) (k0 k Δ : ℝ) (y : SDEState n) : ℝ :=
  ∏ i, (if i ∈ supp μ then ta k0 k (y i) else tb Δ (y i))

theorem phi_factor_nonneg (μ : Measure (SDEState n)) (k0 k Δ : ℝ) (y : SDEState n) (i : Fin n) :
    0 ≤ (if i ∈ supp μ then ta k0 k (y i) else tb Δ (y i)) := by
  split_ifs
  · exact ta_nonneg _ _ _
  · exact tb_nonneg _ _

theorem phi_nonneg (μ : Measure (SDEState n)) (k0 k Δ : ℝ) (y : SDEState n) :
    0 ≤ phi μ k0 k Δ y := by
  classical
  unfold phi
  exact Finset.prod_nonneg fun i _ => phi_factor_nonneg μ k0 k Δ y i

theorem phi_le_one (μ : Measure (SDEState n)) (k0 k Δ : ℝ) (y : SDEState n) :
    phi μ k0 k Δ y ≤ 1 := by
  classical
  unfold phi
  refine Finset.prod_le_one (fun i _ => phi_factor_nonneg μ k0 k Δ y i) fun i _ => ?_
  split_ifs
  · exact ta_le_one _ _ _
  · exact tb_le_one _ _

theorem continuous_phi (μ : Measure (SDEState n)) (k0 k Δ : ℝ) :
    Continuous (phi μ k0 k Δ) := by
  classical
  unfold phi
  refine continuous_finset_prod _ fun i _ => ?_
  split_ifs
  · exact (continuous_ta k0 k).comp (PiLp.continuous_apply 2 _ i)
  · exact (continuous_tb Δ).comp (PiLp.continuous_apply 2 _ i)

theorem mem_Kbox_of_phi_pos {μ : Measure (SDEState n)} {k0 : ℝ} {k : ℕ} {Δ : ℝ}
    (hk0 : 1 ≤ k0) (hk : k0 < k) (hΔ : 0 < Δ) {y : SDEState n} (hy : y ∈ openOrthant n)
    (h : 0 < phi μ k0 k Δ y) : y ∈ Kbox μ k Δ := by
  classical
  have hfac : ∀ i, 0 < (if i ∈ supp μ then ta k0 k (y i) else tb Δ (y i)) := by
    intro i
    refine lt_of_le_of_ne (phi_factor_nonneg μ k0 k Δ y i) fun h0 => ?_
    have : phi μ k0 k Δ y = 0 := by
      unfold phi
      exact Finset.prod_eq_zero (Finset.mem_univ i) h0.symm
    linarith
  refine ⟨hy, fun i hi => ?_, fun i hi => ?_⟩
  · have := hfac i
    rw [if_pos hi] at this
    obtain ⟨h1, h2⟩ := ta_pos hk0 hk this
    exact ⟨h1.le, h2.le⟩
  · have := hfac i
    rw [if_neg hi] at this
    exact tb_pos hΔ this

theorem phi_eq_one {μ : Measure (SDEState n)} {k0 k Δ : ℝ} (hk0 : 1 ≤ k0) (hk : k0 < k)
    {y : SDEState n} (h1 : ∀ i ∈ supp μ, k0⁻¹ ≤ y i ∧ y i ≤ k0) (h2 : ∀ i, i ∉ supp μ → y i = 0) :
    phi μ k0 k Δ y = 1 := by
  classical
  unfold phi
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs with hi
  · exact ta_eq_one hk0 hk (h1 i hi).1 (h1 i hi).2
  · rw [h2 i hi, tb_zero]

/-- the cut-off. -/
noncomputable def psiF (S : Finset (Measure (SDEState n))) (k0 k : ℝ)
    (Δ : Measure (SDEState n) → ℝ) (y : SDEState n) : ℝ :=
  min 1 (∑ μ ∈ S, phi μ k0 k (Δ μ) y)

theorem continuous_psiF (S : Finset (Measure (SDEState n))) (k0 k : ℝ)
    (Δ : Measure (SDEState n) → ℝ) : Continuous (psiF S k0 k Δ) :=
  continuous_const.min (continuous_finset_sum _ fun μ _ => continuous_phi μ k0 k (Δ μ))

theorem psiF_nonneg (S : Finset (Measure (SDEState n))) (k0 k : ℝ)
    (Δ : Measure (SDEState n) → ℝ) (y : SDEState n) : 0 ≤ psiF S k0 k Δ y :=
  le_min zero_le_one (Finset.sum_nonneg fun μ _ => phi_nonneg μ k0 k (Δ μ) y)

theorem psiF_le_one (S : Finset (Measure (SDEState n))) (k0 k : ℝ)
    (Δ : Measure (SDEState n) → ℝ) (y : SDEState n) : psiF S k0 k Δ y ≤ 1 := min_le_left _ _

theorem norm_psiF_le (S : Finset (Measure (SDEState n))) (k0 k : ℝ)
    (Δ : Measure (SDEState n) → ℝ) (y : SDEState n) : ‖psiF S k0 k Δ y‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (psiF_nonneg S k0 k Δ y)]; exact psiF_le_one S k0 k Δ y

/-- the cut-off as a bounded continuous function. -/
noncomputable def psi (S : Finset (Measure (SDEState n))) (k0 k : ℝ)
    (Δ : Measure (SDEState n) → ℝ) : SDEState n →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (psiF S k0 k Δ) (continuous_psiF S k0 k Δ) 1
    (norm_psiF_le S k0 k Δ)

theorem psi_apply (S : Finset (Measure (SDEState n))) (k0 k : ℝ)
    (Δ : Measure (SDEState n) → ℝ) (y : SDEState n) : psi S k0 k Δ y = psiF S k0 k Δ y := rfl

theorem phi_le_psiF {S : Finset (Measure (SDEState n))} {μ : Measure (SDEState n)} (hμ : μ ∈ S)
    (k0 k : ℝ) (Δ : Measure (SDEState n) → ℝ) (y : SDEState n) :
    phi μ k0 k (Δ μ) y ≤ psiF S k0 k Δ y :=
  le_min (phi_le_one μ k0 k (Δ μ) y)
    (Finset.single_le_sum (f := fun ν => phi ν k0 k (Δ ν) y)
      (fun ν _ => phi_nonneg ν k0 k (Δ ν) y) hμ)

theorem psiF_le_indicator (S : Finset (Measure (SDEState n))) {k0 : ℝ} {k : ℕ}
    (hk0 : 1 ≤ k0) (hk : k0 < k) (Δ : Measure (SDEState n) → ℝ) (hΔ : ∀ μ ∈ S, 0 < Δ μ)
    {y : SDEState n} (hy : y ∈ openOrthant n) :
    psiF S k0 k Δ y ≤ (⋃ μ ∈ S, Kbox μ k (Δ μ)).indicator 1 y := by
  by_cases hK : y ∈ ⋃ μ ∈ S, Kbox μ k (Δ μ)
  · rw [Set.indicator_of_mem hK]; exact psiF_le_one S k0 k Δ y
  · rw [Set.indicator_of_notMem hK]
    have h0 : ∀ μ ∈ S, phi μ k0 k (Δ μ) y = 0 := by
      intro μ hμ
      refine le_antisymm ?_ (phi_nonneg _ _ _ _ _)
      by_contra hc
      push_neg at hc
      exact hK (Set.mem_biUnion hμ (mem_Kbox_of_phi_pos hk0 hk (hΔ μ hμ) hy hc))
    unfold psiF
    rw [Finset.sum_eq_zero h0]
    exact min_le_right _ _

theorem measurableSet_Kbox (μ : Measure (SDEState n)) (k : ℕ) (Δ : ℝ) :
    MeasurableSet (Kbox μ k Δ) := by
  have hc : ∀ i : Fin n, Measurable fun y : SDEState n => y i := fun i =>
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable
  have e : Kbox μ k Δ = (⋂ i, {y : SDEState n | 0 < y i}) ∩
      ((⋂ i ∈ supp μ, ({y : SDEState n | (k : ℝ)⁻¹ ≤ y i} ∩ {y | y i ≤ k})) ∩
      ⋂ i, ⋂ (_ : i ∉ supp μ), {y : SDEState n | y i < Δ}) := by
    ext y
    simp only [Kbox, openOrthant, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  exact (MeasurableSet.iInter fun i => measurableSet_lt measurable_const (hc i)).inter
    ((MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (measurableSet_le measurable_const (hc i)).inter (measurableSet_le (hc i) measurable_const)).inter
    (MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      measurableSet_lt (hc i) measurable_const))

end StochKolmogorov.Classify.Psi

end Mod_Psi

-- ===== module K1a =====
section Mod_K1a

/-! K1a of theorem_1_3 (8f909832): an ergodic invariant measure is concentrated on the interior of its
own face. Pure measure theory from face invariance (Extinct.lemma_3_1 clause 2 / Persist
kolmogorov_sde_face_invariance): open faces `F I` partition the orthant and are forward invariant, so
`μ|F I` (normalised) is invariant; extremality forces `μ (F I) ∈ {0,1}`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.K1a

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ}

/-- The open face whose positive coordinates are exactly `I`. -/
def F (I : Finset (Fin n)) : Set (SDEState n) := {x | x ∈ orthant n ∧ ∀ i, i ∈ I ↔ 0 < x i}

theorem coord_meas (i : Fin n) : Measurable fun x : SDEState n => x i :=
  (PiLp.continuous_apply 2 _ i).measurable

theorem measurableSet_orthant : MeasurableSet (orthant n) := by
  have e : orthant n = ⋂ i, {x : SDEState n | 0 ≤ x i} := by
    ext x; simp [orthant]
  rw [e]; exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (coord_meas i)

theorem measurableSet_F (I : Finset (Fin n)) : MeasurableSet (F I) := by
  have e : F I = orthant n ∩ ⋂ i, {x : SDEState n | i ∈ I ↔ 0 < x i} := by
    ext x; simp [F]
  rw [e]
  refine measurableSet_orthant.inter (MeasurableSet.iInter fun i => ?_)
  by_cases hi : i ∈ I
  · simp only [hi, true_iff]; exact measurableSet_lt measurable_const (coord_meas i)
  · simp only [hi, false_iff, not_lt]; exact measurableSet_le (coord_meas i) measurable_const

/-- The positive coordinates of a point. -/
noncomputable def pos (x : SDEState n) : Finset (Fin n) := Finset.univ.filter fun i => 0 < x i

theorem mem_F_pos {x : SDEState n} (hx : x ∈ orthant n) : x ∈ F (pos x) :=
  ⟨hx, fun i => by simp [pos]⟩

theorem F_unique {x : SDEState n} {I J : Finset (Fin n)} (hI : x ∈ F I) (hJ : x ∈ F J) : I = J := by
  ext i; rw [hI.2 i, hJ.2 i]

theorem orthant_subset : orthant n ⊆ ⋃ I : Finset (Fin n), F I :=
  fun x hx => Set.mem_iUnion.2 ⟨pos x, mem_F_pos hx⟩

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Face invariance at fixed times, in the `F I` form. -/
def FaceInv (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ F I → ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ F I

/-- The clause-2 form of `Extinct.lemma_3_1` gives `FaceInv`. -/
theorem faceInv_of_clause {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (h : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0)) :
    FaceInv P X := by
  intro I x hx t
  filter_upwards [h I x hx.1 hx.2] with ω hω
  obtain ⟨h1, h2⟩ := hω t
  refine ⟨fun i => ?_, fun i => ⟨fun hi => h1 i hi, fun hp => ?_⟩⟩
  · by_cases hi : i ∈ I
    · exact (h1 i hi).le
    · exact (h2 i hi).ge
  · by_contra hi
    rw [h2 i hi] at hp
    exact lt_irrefl _ hp

theorem trans_null {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n} {t : ℝ≥0}
    {x : SDEState n} {S : Set (SDEState n)} (hS : MeasurableSet S)
    (h : ∀ᵐ ω ∂P, X x t ω ∉ S) : StochKolmogorov.Classify.trans P X t x S = 0 := by
  unfold StochKolmogorov.Classify.trans
  by_cases hm : AEMeasurable (X x t) P
  · rw [Measure.map_apply₀ hm hS.nullMeasurableSet]
    rw [ae_iff] at h
    convert h using 2
    ext ω; simp
  · rw [Measure.map_of_not_aemeasurable hm]; simp

theorem le_of_sum {a b c d : ℝ≥0∞} (hac : a ≤ c) (hbd : b ≤ d) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (h : a + b = c + d) : a = c ∧ b = d := by
  refine ⟨le_antisymm hac ?_, le_antisymm hbd ?_⟩
  · have : c + d ≤ a + d := h ▸ add_le_add le_rfl hbd
    exact (ENNReal.add_le_add_iff_right hd).1 this
  · have : c + d ≤ c + b := h ▸ add_le_add hac le_rfl
    exact (ENNReal.add_le_add_iff_left hc).1 this

/-- Step A: the invariance relation splits along every open face. -/
theorem restrict_rel {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : FaceInv P X) {μ : Measure (SDEState n)} [IsFiniteMeasure μ]
    (horth : μ (orthant n)ᶜ = 0)
    (hinv : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂μ = μ A)
    (I : Finset (Fin n)) (t : ℝ≥0) (A : Set (SDEState n)) (hA : MeasurableSet A) :
    ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂μ = μ (A ∩ F I) ∧
      ∫⁻ x in (F I)ᶜ, StochKolmogorov.Classify.trans P X t x A ∂μ = μ (A ∩ (F I)ᶜ) := by
  have hF := measurableSet_F I
  have k1 : ∀ x ∈ F I, StochKolmogorov.Classify.trans P X t x (F I)ᶜ = 0 := by
    intro x hx
    refine trans_null hF.compl ?_
    filter_upwards [hface I x hx t] with ω hω
    simpa using hω
  have k2 : ∀ x ∈ orthant n, x ∉ F I → StochKolmogorov.Classify.trans P X t x (F I) = 0 := by
    intro x hx hxI
    have hxJ := mem_F_pos hx
    refine trans_null hF ?_
    filter_upwards [hface _ x hxJ t] with ω hω hωI
    have e := F_unique hω hωI
    exact hxI (e ▸ hxJ)
  have hao : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact horth
  have e1 : ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂μ ≤ μ (A ∩ F I) := by
    calc ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂μ
        = ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x (A ∩ F I) ∂μ := by
          refine lintegral_congr_ae ((ae_restrict_iff' hF).2 (ae_of_all _ fun x hx => ?_))
          exact (measure_inter_conull (k1 x hx)).symm
      _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x (A ∩ F I) ∂μ :=
          setLIntegral_le_lintegral _ _
      _ = μ (A ∩ F I) := hinv t _ (hA.inter hF)
  have e2 : ∫⁻ x in (F I)ᶜ, StochKolmogorov.Classify.trans P X t x A ∂μ ≤ μ (A ∩ (F I)ᶜ) := by
    calc ∫⁻ x in (F I)ᶜ, StochKolmogorov.Classify.trans P X t x A ∂μ
        = ∫⁻ x in (F I)ᶜ, StochKolmogorov.Classify.trans P X t x (A ∩ (F I)ᶜ) ∂μ := by
          refine lintegral_congr_ae ((ae_restrict_iff' hF.compl).2 ?_)
          filter_upwards [hao] with x hx hxc
          refine (measure_inter_conull ?_).symm
          rw [compl_compl]; exact k2 x hx hxc
      _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x (A ∩ (F I)ᶜ) ∂μ :=
          setLIntegral_le_lintegral _ _
      _ = μ (A ∩ (F I)ᶜ) := hinv t _ (hA.inter hF.compl)
  refine le_of_sum e1 e2 (measure_ne_top _ _) (measure_ne_top _ _) ?_
  rw [lintegral_add_compl _ hF, hinv t A hA, ← Set.diff_eq, measure_inter_add_diff A hF]

/-- A normalised restriction satisfying the split relation is invariant. -/
theorem inv_restrict {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    {μ : Measure (SDEState n)} (horth : μ (orthant n)ᶜ = 0) {S : Set (SDEState n)}
    (hS : MeasurableSet S) {c : ℝ≥0∞} (hc : c = μ S) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hrel : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ x in S, StochKolmogorov.Classify.trans P X t x A ∂μ = μ (A ∩ S)) :
    IsInvariant P X (c⁻¹ • μ.restrict S) := by
  refine ⟨⟨?_⟩, ?_, ?_⟩
  · rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, ← hc,
      smul_eq_mul, ENNReal.inv_mul_cancel hc0 hct]
  · rw [Measure.smul_apply, Measure.restrict_apply' hS,
      measure_mono_null Set.inter_subset_left horth, smul_eq_mul, mul_zero]
  · intro t A hA
    rw [lintegral_smul_measure, hrel t A hA, Measure.smul_apply, Measure.restrict_apply hA,
      smul_eq_mul]

/-- Step B: an ergodic measure gives each open face mass `0` or `1`. -/
theorem face_zero_or_one {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : FaceInv P X) {μ : Measure (SDEState n)} (hE : IsErgodic P X μ)
    (I : Finset (Fin n)) : μ (F I) = 0 ∨ μ (F I) = 1 := by
  obtain ⟨⟨hprob, horth, hinv⟩, hext⟩ := hE
  haveI := hprob
  have hF := measurableSet_F I
  by_contra hcon
  push_neg at hcon
  obtain ⟨h0, h1⟩ := hcon
  set a : ℝ≥0 := (μ (F I)).toNNReal with ha_def
  have ha : (a : ℝ≥0∞) = μ (F I) := ENNReal.coe_toNNReal (measure_ne_top _ _)
  have hlt : μ (F I) < 1 := lt_of_le_of_ne prob_le_one h1
  have ha0 : 0 < a := ENNReal.toNNReal_pos h0 (measure_ne_top _ _)
  have ha1 : a < 1 := by
    have : (a : ℝ≥0∞) < 1 := by rw [ha]; exact hlt
    exact_mod_cast this
  have hb : ((1 - a : ℝ≥0) : ℝ≥0∞) = μ (F I)ᶜ := by
    rw [prob_compl_eq_one_sub hF, ← ha, ENNReal.coe_sub, ENNReal.coe_one]
  have hb0 : ((1 - a : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [hb, prob_compl_eq_one_sub hF]; exact (tsub_pos_of_lt hlt).ne'
  have ha0' : (a : ℝ≥0∞) ≠ 0 := by rw [ha]; exact h0
  have hrel := restrict_rel hface horth hinv I
  have inv1 : IsInvariant P X ((a : ℝ≥0∞)⁻¹ • μ.restrict (F I)) :=
    inv_restrict horth hF ha ha0' ENNReal.coe_ne_top fun t A hA => (hrel t A hA).1
  have inv2 : IsInvariant P X (((1 - a : ℝ≥0) : ℝ≥0∞)⁻¹ • μ.restrict (F I)ᶜ) :=
    inv_restrict horth hF.compl hb hb0 ENNReal.coe_ne_top fun t A hA => (hrel t A hA).2
  have hdec : μ = (a : ℝ≥0∞) • ((a : ℝ≥0∞)⁻¹ • μ.restrict (F I)) +
      ((1 - a : ℝ≥0) : ℝ≥0∞) • (((1 - a : ℝ≥0) : ℝ≥0∞)⁻¹ • μ.restrict (F I)ᶜ) := by
    rw [smul_smul, smul_smul, ENNReal.mul_inv_cancel ha0' ENNReal.coe_ne_top,
      ENNReal.mul_inv_cancel hb0 ENNReal.coe_ne_top, one_smul, one_smul,
      Measure.restrict_add_restrict_compl hF]
  have heq := hext _ _ inv1 inv2 a ha0 ha1 hdec
  have hc := congrArg (fun m : Measure (SDEState n) => m (F I)ᶜ) heq
  simp only [Measure.smul_apply, Measure.restrict_apply hF.compl, Set.compl_inter_self,
    measure_empty, smul_eq_mul, mul_zero] at hc
  rw [← hb] at hc
  exact hb0 hc.symm

/-- K1a: an ergodic invariant measure is concentrated on `faceInt μ`. -/
theorem concentrates {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : FaceInv P X) {μ : Measure (SDEState n)} (hE : IsErgodic P X μ) :
    μ (faceInt μ)ᶜ = 0 := by
  have horth := hE.1.2.1
  haveI := hE.1.1
  have hcov : ∃ I, μ (F I) = 1 := by
    by_contra h
    push_neg at h
    have h0 : ∀ I, μ (F I) = 0 := fun I => (face_zero_or_one hface hE I).resolve_right (h I)
    have z : μ (orthant n) = 0 := measure_mono_null orthant_subset (measure_iUnion_null h0)
    have o : μ (orthant n) = 1 := (prob_compl_eq_zero_iff measurableSet_orthant).1 horth
    rw [z] at o
    exact zero_ne_one o
  obtain ⟨I, hI⟩ := hcov
  have hIc : μ (F I)ᶜ = 0 := (prob_compl_eq_zero_iff (measurableSet_F I)).2 hI
  have hsupp : supp μ = I := by
    ext i
    simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      by_contra hi
      apply h
      refine measure_mono_null ?_ hIc
      intro x hx hxF
      exact hi ((hxF.2 i).2 hx)
    · intro hi h
      have hle : μ (F I) ≤ μ {x : SDEState n | 0 < x i} :=
        measure_mono fun x hx => (hx.2 i).1 hi
      rw [hI, h] at hle
      exact absurd hle (by norm_num)
  refine measure_mono_null ?_ hIc
  intro x hx hxF
  apply hx
  have hxo : ∀ i, 0 ≤ x i := hxF.1
  refine ⟨⟨hxF.1, fun i hi => ?_⟩, fun i hi => ?_⟩
  · rw [hsupp] at hi
    rcases (hxo i).lt_or_eq with h | h
    · exact absurd ((hxF.2 i).2 h) hi
    · exact h.symm
  · rw [hsupp] at hi
    exact (hxF.2 i).1 hi

end StochKolmogorov.Classify.K1a

end Mod_K1a

-- ===== module UGlue =====
section Mod_UGlue

/-! (5.39) from the paper's claim `U(ω) ⊆ Conv(M) \ Conv(M²)` a.s. (p. 28) (8f909832, K2):
`K0` the face boxes `K⁰_μ`, `exists_k0` (U5: `μ(K⁰_μ) > 0` for `k0` large, all `μ ∈ M¹`),
`pos_of_conv` (`∫ψ dπ > 0` for `π ∈ Conv(M) \ Conv(M²)`), `K2_of_conv` (K2 from Lemma 5.7 tightness,
Lemma 5.9, interior invariance and the claim). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.UGlue

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

/-- `K⁰_μ` (p. 28). -/
def K0 (μ : Measure (SDEState n)) (k0 : ℝ) : Set (SDEState n) :=
  {y | (∀ i ∈ supp μ, k0⁻¹ ≤ y i ∧ y i ≤ k0) ∧ ∀ i, i ∉ supp μ → y i = 0}

theorem K0_mono (μ : Measure (SDEState n)) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    K0 μ a ⊆ K0 μ b := by
  intro y ⟨h1, h2⟩
  refine ⟨fun i hi => ⟨le_trans (inv_anti₀ (by linarith) hab) (h1 i hi).1,
    le_trans (h1 i hi).2 hab⟩, h2⟩

theorem faceInt_subset (μ : Measure (SDEState n)) :
    faceInt μ ⊆ ⋃ m : ℕ, K0 μ ((m : ℝ) + 1) := by
  classical
  intro y hy
  obtain ⟨⟨ho, hz⟩, hp⟩ := hy
  obtain ⟨m, hm⟩ := exists_nat_gt (∑ i, (y i + (y i)⁻¹))
  refine Set.mem_iUnion.2 ⟨m, fun i hi => ?_, hz⟩
  have hyi := hp i hi
  have hs : y i + (y i)⁻¹ ≤ ∑ j, (y j + (y j)⁻¹) :=
    Finset.single_le_sum (f := fun j => y j + (y j)⁻¹)
      (fun j _ => add_nonneg (ho j) (inv_nonneg.2 (ho j))) (Finset.mem_univ i)
  have hinv : 0 < (y i)⁻¹ := inv_pos.2 hyi
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  refine ⟨?_, by linarith⟩
  rw [inv_le_comm₀ hm1 hyi]
  linarith

theorem exists_k0_one [MeasurableSpace Ω] {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : K1a.FaceInv P X) {μ : Measure (SDEState n)} (hE : IsErgodic P X μ) :
    ∃ m : ℕ, 0 < μ (K0 μ ((m : ℝ) + 1)) := by
  haveI := hE.1.1
  by_contra h
  push_neg at h
  have h0 : ∀ m : ℕ, μ (K0 μ ((m : ℝ) + 1)) = 0 := fun m => nonpos_iff_eq_zero.1 (h m)
  have hc := K1a.concentrates hface hE
  have hU : μ (faceInt μ) = 0 := measure_mono_null (faceInt_subset μ) (measure_iUnion_null h0)
  have : μ Set.univ = 0 := by
    have := measure_union_le (μ := μ) (faceInt μ) (faceInt μ)ᶜ
    rw [Set.union_compl_self, hU, hc, add_zero] at this
    exact nonpos_iff_eq_zero.1 this
  simp at this

/-- U5: one `k0 ≥ 1` with `μ(K⁰_μ) > 0` for every `μ` in a finite set of ergodic measures. -/
theorem exists_k0 [MeasurableSpace Ω] {P : Measure Ω} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hface : K1a.FaceInv P X) (S : Finset (Measure (SDEState n)))
    (hS : ∀ μ ∈ S, IsErgodic P X μ) :
    ∃ k0 : ℝ, 1 ≤ k0 ∧ ∀ μ ∈ S, 0 < μ (K0 μ k0) := by
  classical
  have hch : ∀ μ ∈ S, ∃ m : ℕ, 0 < μ (K0 μ ((m : ℝ) + 1)) := fun μ hμ =>
    exists_k0_one hface (hS μ hμ)
  choose! f hf using hch
  refine ⟨((S.sup f : ℕ) : ℝ) + 1, by
    have : (0 : ℝ) ≤ ((S.sup f : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith, fun μ hμ => ?_⟩
  refine lt_of_lt_of_le (hf μ hμ) (measure_mono (K0_mono μ (by
    have : (0 : ℝ) ≤ ((f μ : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith) ?_))
  have : f μ ≤ S.sup f := Finset.le_sup hμ
  have : ((f μ : ℕ) : ℝ) ≤ ((S.sup f : ℕ) : ℝ) := by exact_mod_cast this
  linarith

theorem K0_subset_support (S : Finset (Measure (SDEState n))) {μ : Measure (SDEState n)}
    (hμ : μ ∈ S) {k0 k : ℝ} (hk0 : 1 ≤ k0) (hk : k0 < k) (Δ : Measure (SDEState n) → ℝ) :
    K0 μ k0 ⊆ Function.support (Psi.psi S k0 k Δ) := by
  intro y ⟨h1, h2⟩
  have h := Psi.phi_le_psiF hμ k0 k Δ y
  rw [Psi.phi_eq_one hk0 hk h1 h2] at h
  rw [Function.mem_support, Psi.psi_apply]
  linarith

/-- `∫ ψ dπ > 0` for `π ∈ Conv(M) \ Conv(M²)`. -/
theorem pos_of_conv [MeasurableSpace Ω] {P : Measure Ω} {C : Coeffs n}
    {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (S : Finset (Measure (SDEState n))) (hS : ∀ μ ∈ M1 P C X, μ ∈ S)
    {k0 k : ℝ} (hk0 : 1 ≤ k0) (hk : k0 < k) (Δ : Measure (SDEState n) → ℝ)
    (hpos : ∀ μ ∈ M1 P C X, 0 < μ (K0 μ k0))
    {π : Measure (SDEState n)} (h1 : π ∈ conv (bdryErgodic P X)) (h2 : π ∉ conv (M2 P C X)) :
    0 < ∫ y, Psi.psi S k0 k Δ y ∂π := by
  classical
  obtain ⟨s, p, hs, hp, hsum, rfl⟩ := h1
  have hex : ∃ μ ∈ s, μ ∈ M1 P C X := by
    by_contra hc
    push_neg at hc
    exact h2 ⟨s, p, fun μ hμ => ⟨hs hμ, hc μ hμ⟩, hp, hsum, rfl⟩
  obtain ⟨μ, hμs, hμ1⟩ := hex
  haveI : IsFiniteMeasure (∑ ν ∈ s, (p ν : ℝ≥0∞) • ν) := by
    refine ⟨?_⟩
    rw [Measure.coe_finset_sum, Finset.sum_apply]
    refine ENNReal.sum_lt_top.2 fun ν hν => ?_
    haveI := (hs hν).1.1.1
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top ν _)
  have hint : Integrable (fun y => Psi.psi S k0 k Δ y) (∑ ν ∈ s, (p ν : ℝ≥0∞) • ν) :=
    BoundedContinuousFunction.integrable _ _
  refine (integral_pos_iff_support_of_nonneg (f := fun y => Psi.psi S k0 k Δ y)
    (fun y => Psi.psiF_nonneg S k0 k Δ y) hint).2 ?_
  have hK := K0_subset_support S (hS μ hμ1) hk0 hk Δ
  calc (0 : ℝ≥0∞) < (p μ : ℝ≥0∞) * μ (K0 μ k0) :=
        ENNReal.mul_pos (by exact_mod_cast (hp μ hμs).ne') (hpos μ hμ1).ne'
    _ ≤ (p μ : ℝ≥0∞) * μ (Function.support (Psi.psi S k0 k Δ)) := by gcongr
    _ ≤ ∑ ν ∈ s, (p ν : ℝ≥0∞) * ν (Function.support (Psi.psi S k0 k Δ)) :=
        Finset.single_le_sum (f := fun ν => (p ν : ℝ≥0∞) * ν (Function.support (Psi.psi S k0 k Δ)))
          (fun _ _ => bot_le) hμs
    _ = (∑ ν ∈ s, (p ν : ℝ≥0∞) • ν) (Function.support (Psi.psi S k0 k Δ)) := by
        rw [Measure.coe_finset_sum, Finset.sum_apply]
        rfl

/-- K2 (cover) from Lemma 5.7 (tightness clause), Lemma 5.9, interior invariance and the claim
`U(ω) ⊆ Conv(M) \ Conv(M²)` a.s. (p. 28). -/
theorem K2_of_conv [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n)
    (hface : K1a.FaceInv P X) (hM1 : (M1 P C X).Finite)
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X y t ω})
    (h59 : ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ x ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X x μ)).toReal)
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (hint : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, X x s ω ∈ openOrthant n)
    (hU : ∀ᵐ ω ∂P, ∀ π ∈ limitSet X x ω,
      π ∈ conv (bdryErgodic P X) ∧ π ∉ conv (M2 P C X)) :
    ∀ᵐ ω ∂P, ∃ μ ∈ M1 P C X, ω ∈ extinctEvent C X x μ := by
  classical
  set S := hM1.toFinset with hSdef
  have hSm : ∀ μ ∈ S, μ ∈ M1 P C X := fun μ hμ => hM1.mem_toFinset.1 hμ
  have hSe : ∀ μ ∈ S, IsErgodic P X μ := fun μ hμ => (hSm μ hμ).1.1
  obtain ⟨k0, hk0, hk0pos⟩ := exists_k0 hface S hSe
  obtain ⟨k, hk⟩ := exists_nat_gt k0
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) < k := lt_of_le_of_lt hk0 hk
    exact_mod_cast this.le
  let Δ : Measure (SDEState n) → ℝ := fun μ =>
    if h : μ ∈ M1 P C X then Classical.choose (h59 μ h k hk1 (1 / 2) (by norm_num)) else 1
  have hΔ : ∀ μ ∈ S, 0 < Δ μ := by
    intro μ hμ
    simp only [Δ, dif_pos (hSm μ hμ)]
    exact (Classical.choose_spec (h59 μ (hSm μ hμ) k hk1 (1 / 2) (by norm_num))).1
  have hΔK : ∀ μ (h : μ ∈ M1 P C X), ∀ y ∈ Kbox μ k (Δ μ),
      1 - 1 / 2 < (P (extinctEvent C X y μ)).toReal := by
    intro μ h y hy
    simp only [Δ, dif_pos h] at hy
    exact (Classical.choose_spec (h59 μ h k hk1 (1 / 2) (by norm_num))).2 y hy
  have hprob : ∀ μ ∈ M1 P C X, IsProbabilityMeasure μ := fun μ h => h.1.1.1.1
  refine Rec540.K2_of_U P C B X hX hC hinv hM1 hprob h57 x hx (⋃ μ ∈ S, Kbox μ k (Δ μ))
    (Finset.measurableSet_biUnion S fun μ _ => Psi.measurableSet_Kbox μ k (Δ μ)) ?_
    (Psi.psi S k0 k Δ) (fun y => Psi.psiF_nonneg S k0 k Δ y) (fun y => Psi.psiF_le_one S k0 k Δ y)
    (fun y hy => Psi.psiF_le_indicator S hk0 hk Δ hΔ hy) hint ?_
  · intro y hy
    obtain ⟨μ, hμ, hyμ⟩ := Set.mem_iUnion₂.1 hy
    refine ⟨fun i => (hyμ.1 i).le, μ, hSm μ hμ, ?_⟩
    have := hΔK μ (hSm μ hμ) y hyμ
    linarith
  · filter_upwards [hU] with ω hω π hπ
    exact pos_of_conv S (fun μ h => hM1.mem_toFinset.2 h) hk0 hk Δ
      (fun μ h => hk0pos μ (hM1.mem_toFinset.2 h)) (hω π hπ).1 (hω π hπ).2

end StochKolmogorov.Classify.UGlue

end Mod_UGlue

-- ===== module ErgSing =====
section Mod_ErgSing

/-! Uniqueness core for K1b / K2b of theorem_1_3 (8f909832), pure measure theory:
* `dichotomy`: two ergodic invariant measures are equal or mutually singular (Hahn decomposition;
  `(μ-ν)⁺` is super-invariant, hence invariant, hence a multiple of `μ` by extremality). No
  measurability of `x ↦ trans t x A` is used (only superadditivity of the lower integral).
* `eq_of_overlap`: two ergodic measures charging a common set `K` on which the transition laws
  overlap (`ε ≤ P_t(x,A) + P_t(y,Aᶜ)`) are equal. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.ErgSing

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

/-- The setwise invariance relation. -/
def Rel (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (m : Measure (SDEState n)) :
    Prop :=
  ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
    ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m = m A

/-- The transition laws from points of the orthant are probability measures. -/
def TotOne (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ x ∈ orthant n, ∀ t : ℝ≥0, StochKolmogorov.Classify.trans P X t x Set.univ = 1

theorem ge_of_sum {a b c d : ℝ≥0∞} (hca : c ≤ a) (hdb : d ≤ b) (hc : c ≠ ∞) (hd : d ≠ ∞)
    (h : a + b ≤ c + d) : a = c ∧ b = d := by
  refine ⟨le_antisymm ?_ hca, le_antisymm ?_ hdb⟩
  · have : a + d ≤ c + d := (add_le_add le_rfl hdb).trans h
    exact (ENNReal.add_le_add_iff_right hd).1 this
  · have : c + b ≤ c + d := (add_le_add hca le_rfl).trans h
    exact (ENNReal.add_le_add_iff_left hc).1 this

/-- A super-invariant finite measure on the orthant is invariant. -/
theorem super_to_rel (htot : TotOne P X) {m : Measure (SDEState n)} [IsFiniteMeasure m]
    (hm : m (orthant n)ᶜ = 0)
    (hsup : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      m A ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m) : Rel P X m := by
  intro t A hA
  have hao : ∀ᵐ x ∂m, x ∈ orthant n := by rw [ae_iff]; exact hm
  have huniv : ∫⁻ x, StochKolmogorov.Classify.trans P X t x Set.univ ∂m = m Set.univ := by
    rw [← lintegral_one]
    refine lintegral_congr_ae ?_
    filter_upwards [hao] with x hx using htot x hx t
  have hle : ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m +
      ∫⁻ x, StochKolmogorov.Classify.trans P X t x Aᶜ ∂m ≤ m A + m Aᶜ := by
    calc _ ≤ ∫⁻ x, (StochKolmogorov.Classify.trans P X t x A +
            StochKolmogorov.Classify.trans P X t x Aᶜ) ∂m := le_lintegral_add _ _
      _ = ∫⁻ x, StochKolmogorov.Classify.trans P X t x Set.univ ∂m :=
          lintegral_congr fun x => measure_add_measure_compl hA
      _ = m Set.univ := huniv
      _ = m A + m Aᶜ := (measure_add_measure_compl hA).symm
  exact (ge_of_sum (hsup t A hA) (hsup t Aᶜ hA.compl) (measure_ne_top _ _)
    (measure_ne_top _ _) hle).1

/-- Super-invariance of the positive part, from a common remainder `w`. -/
theorem super_of_split {μ ν m m' w : Measure (SDEState n)} (hμi : Rel P X μ) (hνi : Rel P X ν)
    (hμ : μ = m + w) (hν : ν = m' + w) {H : Set (SDEState n)} (hHm : MeasurableSet H)
    (hmc : m Hᶜ = 0)
    (hmA : ∀ A, MeasurableSet A → A ⊆ H → m A ≤ μ A - ν A) :
    ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      m A ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m := by
  have core : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      μ A ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m + ν A := by
    intro t A hA
    have e1 : ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m +
        ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂w = μ A := by
      rw [← lintegral_add_measure, ← hμ]; exact hμi t A hA
    have e2 : ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m' +
        ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂w = ν A := by
      rw [← lintegral_add_measure, ← hν]; exact hνi t A hA
    rw [← e1, ← e2]
    calc _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m +
          (∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m' +
            ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂w) :=
        add_le_add le_rfl le_add_self
      _ = _ := rfl
  intro t A hA
  have hH : m A = m (A ∩ H) := (measure_inter_conull hmc).symm
  rw [hH]
  calc m (A ∩ H) ≤ μ (A ∩ H) - ν (A ∩ H) := hmA _ (hA.inter hHm) Set.inter_subset_right
    _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x (A ∩ H) ∂m :=
        tsub_le_iff_right.2 (core t _ (hA.inter hHm))
    _ ≤ ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m :=
        lintegral_mono fun x => measure_mono Set.inter_subset_left

/-- Extremality applied to a split `μ = m + w` into two invariant parts. -/
theorem ergodic_split {μ m w : Measure (SDEState n)} (hE : IsErgodic P X μ)
    [IsFiniteMeasure m] [IsFiniteMeasure w] (hμ : μ = m + w) (hm : Rel P X m) (hw : Rel P X w)
    (h0 : 0 < m Set.univ) (h1 : m Set.univ < 1) : (m Set.univ)⁻¹ • m = μ := by
  obtain ⟨⟨hprob, horth, hinv⟩, hext⟩ := hE
  have hsum : w Set.univ + m Set.univ = 1 := by
    rw [add_comm, ← Measure.add_apply, ← hμ, measure_univ]
  have hw1 : w Set.univ = 1 - m Set.univ := ENNReal.eq_sub_of_add_eq (measure_ne_top _ _) hsum
  set a : ℝ≥0 := (m Set.univ).toNNReal with ha_def
  have ha : (a : ℝ≥0∞) = m Set.univ := ENNReal.coe_toNNReal (measure_ne_top _ _)
  have ha0 : 0 < a := ENNReal.toNNReal_pos h0.ne' (measure_ne_top _ _)
  have ha1 : a < 1 := by
    have : (a : ℝ≥0∞) < 1 := by rw [ha]; exact h1
    exact_mod_cast this
  have hb : ((1 - a : ℝ≥0) : ℝ≥0∞) = w Set.univ := by
    rw [hw1, ← ha, ENNReal.coe_sub, ENNReal.coe_one]
  have hb0 : ((1 - a : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    rw [hb, hw1]; exact (tsub_pos_of_lt h1).ne'
  have ha0' : (a : ℝ≥0∞) ≠ 0 := by rw [ha]; exact h0.ne'
  have hmo : m (orthant n)ᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc m (orthant n)ᶜ ≤ μ (orthant n)ᶜ := by rw [hμ, Measure.add_apply]; exact le_self_add
      _ = 0 := horth
  have hwo : w (orthant n)ᶜ = 0 := by
    refine le_antisymm ?_ zero_le
    calc w (orthant n)ᶜ ≤ μ (orthant n)ᶜ := by rw [hμ, Measure.add_apply]; exact le_add_self
      _ = 0 := horth
  have inv1 : IsInvariant P X ((a : ℝ≥0∞)⁻¹ • m) := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul, ← ha, ENNReal.inv_mul_cancel ha0' ENNReal.coe_ne_top]
    · rw [Measure.smul_apply, hmo, smul_eq_mul, mul_zero]
    · intro t A hA
      rw [lintegral_smul_measure, hm t A hA, Measure.smul_apply, smul_eq_mul]
  have inv2 : IsInvariant P X (((1 - a : ℝ≥0) : ℝ≥0∞)⁻¹ • w) := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · rw [Measure.smul_apply, smul_eq_mul, ← hb, ENNReal.inv_mul_cancel hb0 ENNReal.coe_ne_top]
    · rw [Measure.smul_apply, hwo, smul_eq_mul, mul_zero]
    · intro t A hA
      rw [lintegral_smul_measure, hw t A hA, Measure.smul_apply, smul_eq_mul]
  have hdec : μ = (a : ℝ≥0∞) • ((a : ℝ≥0∞)⁻¹ • m) +
      ((1 - a : ℝ≥0) : ℝ≥0∞) • (((1 - a : ℝ≥0) : ℝ≥0∞)⁻¹ • w) := by
    rw [smul_smul, smul_smul, ENNReal.mul_inv_cancel ha0' ENNReal.coe_ne_top,
      ENNReal.mul_inv_cancel hb0 ENNReal.coe_ne_top, one_smul, one_smul, hμ]
  have := hext _ _ inv1 inv2 a ha0 ha1 hdec
  rw [ha] at this
  exact this

/-- Two ergodic invariant measures are equal or mutually singular. -/
theorem dichotomy (htot : TotOne P X) {μ ν : Measure (SDEState n)} (hEμ : IsErgodic P X μ)
    (hEν : IsErgodic P X ν) :
    μ = ν ∨ ∃ H : Set (SDEState n), MeasurableSet H ∧ μ Hᶜ = 0 ∧ ν H = 0 := by
  haveI := hEμ.1.1
  haveI := hEν.1.1
  have hμi : Rel P X μ := hEμ.1.2.2
  have hνi : Rel P X ν := hEν.1.2.2
  obtain ⟨H, hH, hle, hge⟩ := hahn_decomposition μ ν
  have l1 : ν.restrict H ≤ μ.restrict H := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hle _ (hs.inter hH) Set.inter_subset_right
  have l2 : μ.restrict Hᶜ ≤ ν.restrict Hᶜ := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hge _ (hs.inter hH.compl) Set.inter_subset_right
  set m := μ.restrict H - ν.restrict H with hm_def
  set m' := ν.restrict Hᶜ - μ.restrict Hᶜ with hm'_def
  set w := ν.restrict H + μ.restrict Hᶜ with hw_def
  have hμ : μ = m + w := by
    calc μ = μ.restrict H + μ.restrict Hᶜ := (Measure.restrict_add_restrict_compl hH).symm
      _ = (m + ν.restrict H) + μ.restrict Hᶜ := by rw [Measure.sub_add_cancel_of_le l1]
      _ = m + w := by rw [add_assoc]
  have hν : ν = m' + w := by
    calc ν = ν.restrict H + ν.restrict Hᶜ := (Measure.restrict_add_restrict_compl hH).symm
      _ = ν.restrict H + (m' + μ.restrict Hᶜ) := by rw [Measure.sub_add_cancel_of_le l2]
      _ = m' + w := by rw [add_left_comm]
  have mle : m ≤ μ := hμ ▸ Measure.le_add_right le_rfl
  have m'le : m' ≤ ν := hν ▸ Measure.le_add_right le_rfl
  have wle : w ≤ μ := hμ ▸ Measure.le_add_left le_rfl
  haveI : IsFiniteMeasure m := isFiniteMeasure_of_le μ mle
  haveI : IsFiniteMeasure m' := isFiniteMeasure_of_le ν m'le
  haveI : IsFiniteMeasure w := isFiniteMeasure_of_le μ wle
  have hmc : m Hᶜ = 0 := by
    rw [hm_def, Measure.sub_apply hH.compl l1, Measure.restrict_apply hH.compl,
      Set.compl_inter_self, measure_empty, zero_tsub]
  have hm'c : m' Hᶜᶜ = 0 := by
    rw [hm'_def, Measure.sub_apply hH.compl.compl l2, Measure.restrict_apply hH.compl.compl,
      Set.compl_inter_self, measure_empty, zero_tsub]
  have hmA : ∀ A, MeasurableSet A → A ⊆ H → m A ≤ μ A - ν A := by
    intro A hA hAH
    rw [hm_def, Measure.sub_apply hA l1, Measure.restrict_apply hA, Measure.restrict_apply hA,
      Set.inter_eq_left.2 hAH]
  have hm'A : ∀ A, MeasurableSet A → A ⊆ Hᶜ → m' A ≤ ν A - μ A := by
    intro A hA hAH
    rw [hm'_def, Measure.sub_apply hA l2, Measure.restrict_apply hA, Measure.restrict_apply hA,
      Set.inter_eq_left.2 hAH]
  have orth_of_le : ∀ q : Measure (SDEState n), q ≤ μ → q (orthant n)ᶜ = 0 := fun q hq =>
    le_antisymm ((Measure.le_iff'.1 hq _).trans_eq hEμ.1.2.1) zero_le
  have orth_of_le' : ∀ q : Measure (SDEState n), q ≤ ν → q (orthant n)ᶜ = 0 := fun q hq =>
    le_antisymm ((Measure.le_iff'.1 hq _).trans_eq hEν.1.2.1) zero_le
  have hmR : Rel P X m :=
    super_to_rel htot (orth_of_le m mle) (super_of_split hμi hνi hμ hν hH hmc hmA)
  have hm'R : Rel P X m' :=
    super_to_rel htot (orth_of_le' m' m'le) (super_of_split hνi hμi hν hμ hH.compl hm'c hm'A)
  have hwR : Rel P X w := by
    intro t A hA
    have e1 : ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂m +
        ∫⁻ x, StochKolmogorov.Classify.trans P X t x A ∂w = m A + w A := by
      rw [← lintegral_add_measure, ← Measure.add_apply, ← hμ]; exact hμi t A hA
    rw [hmR t A hA] at e1
    exact (ENNReal.add_right_inj (measure_ne_top m A)).1 e1
  have hsμ : m Set.univ + w Set.univ = 1 := by rw [← Measure.add_apply, ← hμ, measure_univ]
  have hsν : m' Set.univ + w Set.univ = 1 := by rw [← Measure.add_apply, ← hν, measure_univ]
  have hcc : m Set.univ = m' Set.univ :=
    (ENNReal.add_left_inj (measure_ne_top w _)).1 (hsμ.trans hsν.symm)
  have hc1 : m Set.univ ≤ 1 := hsμ ▸ le_self_add
  rcases eq_or_lt_of_le (zero_le : (0:ℝ≥0∞) ≤ m Set.univ) with h0 | h0
  · left
    have z1 : m = 0 := Measure.measure_univ_eq_zero.1 h0.symm
    have z2 : m' = 0 := Measure.measure_univ_eq_zero.1 (hcc ▸ h0.symm)
    rw [hμ, hν, z1, z2]
  rcases eq_or_lt_of_le hc1 with h1 | h1
  · right
    have hw0 : w = 0 := by
      refine Measure.measure_univ_eq_zero.1 ?_
      rw [h1] at hsμ
      have := hsμ
      rw [← add_zero (1 : ℝ≥0∞)] at this
      conv_rhs at this => rw [add_zero]
      exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 (by rw [add_zero]; exact hsμ)
    refine ⟨H, hH, ?_, ?_⟩
    · rw [hμ, hw0, add_zero]; exact hmc
    · rw [hν, hw0, add_zero, ← compl_compl H]; exact hm'c
  · exfalso
    have hs1 := ergodic_split hEμ hμ hmR hwR h0 h1
    have hs2 := ergodic_split hEν hν hm'R hwR (hcc ▸ h0) (hcc ▸ h1)
    have a1 : μ Hᶜ = 0 := by
      rw [← hs1, Measure.smul_apply, hmc, smul_eq_mul, mul_zero]
    have a2 : ν H = 0 := by
      rw [← hs2, Measure.smul_apply, ← compl_compl H, hm'c, smul_eq_mul, mul_zero]
    have hw0 : w Set.univ = 0 := by
      rw [hw_def, Measure.add_apply, Measure.restrict_apply MeasurableSet.univ,
        Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Set.univ_inter, a1, a2, add_zero]
    rw [hw0, add_zero] at hsμ
    exact (ne_of_lt h1) hsμ

/-- Two ergodic measures charging a common overlap set are equal. -/
theorem eq_of_overlap (htot : TotOne P X) {μ ν : Measure (SDEState n)} (hEμ : IsErgodic P X μ)
    (hEν : IsErgodic P X ν) {K : Set (SDEState n)} (hK : MeasurableSet K) (hμK : μ K ≠ 0)
    (hνK : ν K ≠ 0) (t : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hov : ∀ x ∈ K, ∀ y ∈ K, ∀ A : Set (SDEState n), MeasurableSet A →
      ε ≤ StochKolmogorov.Classify.trans P X t x A + StochKolmogorov.Classify.trans P X t y Aᶜ) :
    μ = ν := by
  rcases dichotomy htot hEμ hEν with h | ⟨H, hH, hμH, hνH⟩
  · exact h
  exfalso
  have hy : ∃ y ∈ K, StochKolmogorov.Classify.trans P X t y H < ε := by
    by_contra hc
    push_neg at hc
    have b1 : ε * ν K ≤ ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x H ∂ν := by
      rw [← setLIntegral_const]
      exact lintegral_mono_ae ((ae_restrict_iff' hK).2 (ae_of_all _ hc))
    have b2 : ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x H ∂ν ≤ 0 :=
      (setLIntegral_le_lintegral _ _).trans_eq ((hEν.1.2.2 t H hH).trans hνH)
    have := le_antisymm (b1.trans b2) zero_le
    rcases mul_eq_zero.1 this with h | h
    · exact hε.ne' h
    · exact hνK h
  obtain ⟨y, hyK, hy⟩ := hy
  have hδ : 0 < ε - StochKolmogorov.Classify.trans P X t y H := tsub_pos_of_lt hy
  have hx : ∀ x ∈ K, ε - StochKolmogorov.Classify.trans P X t y H ≤
      StochKolmogorov.Classify.trans P X t x Hᶜ := by
    intro x hx
    have := hov x hx y hyK Hᶜ hH.compl
    rw [compl_compl] at this
    exact tsub_le_iff_right.2 this
  have b1 : (ε - StochKolmogorov.Classify.trans P X t y H) * μ K ≤
      ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x Hᶜ ∂μ := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hK).2 (ae_of_all _ hx))
  have b2 : ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x Hᶜ ∂μ ≤ 0 :=
    (setLIntegral_le_lintegral _ _).trans_eq ((hEμ.1.2.2 t Hᶜ hH.compl).trans hμH)
  have := le_antisymm (b1.trans b2) zero_le
  rcases mul_eq_zero.1 this with h | h
  · exact hδ.ne' h
  · exact hμK h

end StochKolmogorov.Classify.ErgSing

end Mod_ErgSing

-- ===== module K1 =====
section Mod_K1

/-! K1 of theorem_1_3 (8f909832): `M` is finite, modulo the analytic child `FaceOverlap` (TV overlap of
the transition laws on compact boxes inside each open face). K1b: two ergodic measures with the same
support are equal (both live on the same open face by K1a; they charge a common face box; overlap). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.K1

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

theorem totOne_of_family {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hX : IsSolutionFamily P C B X) : TotOne P X := by
  intro x hx t
  haveI := hX.1
  unfold StochKolmogorov.Classify.trans
  rw [Measure.map_apply ((hX.2.2 x hx).1 t) MeasurableSet.univ, Set.preimage_univ, measure_univ]

/-- A compact box inside the open face `F S`. -/
def faceBox (S : Finset (Fin n)) (a b : ℝ) : Set (SDEState n) :=
  {x | x ∈ F S ∧ ∀ i ∈ S, a ≤ x i ∧ x i ≤ b}

theorem measurableSet_faceBox (S : Finset (Fin n)) (a b : ℝ) : MeasurableSet (faceBox S a b) := by
  have e : faceBox S a b = F S ∩ ⋂ i ∈ S, ({x : SDEState n | a ≤ x i} ∩ {x | x i ≤ b}) := by
    ext x; simp [faceBox]
  rw [e]
  exact (measurableSet_F S).inter (Finset.measurableSet_biInter S fun i _ =>
    (measurableSet_le measurable_const (coord_meas i)).inter
      (measurableSet_le (coord_meas i) measurable_const))

/-- The analytic child: TV overlap of `P_t(x,·)` and `P_t(y,·)` on each face box. -/
def FaceOverlap (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) (S : Finset (Fin n)) :
    Prop :=
  ∀ a b : ℝ, 0 < a → a ≤ b → ∃ (t : ℝ≥0) (ε : ℝ≥0∞), 0 < ε ∧
    ∀ x ∈ faceBox S a b, ∀ y ∈ faceBox S a b, ∀ A : Set (SDEState n), MeasurableSet A →
      ε ≤ StochKolmogorov.Classify.trans P X t x A + StochKolmogorov.Classify.trans P X t y Aᶜ

/-- The empty face is the point `0`: overlap is trivial. -/
theorem faceOverlap_empty (htot : TotOne P X) : FaceOverlap P X (∅ : Finset (Fin n)) := by
  intro a b _ _
  refine ⟨0, 1, one_pos, fun x hx y hy A hA => ?_⟩
  have hz : ∀ z ∈ faceBox (∅ : Finset (Fin n)) a b, ∀ i, z i = 0 := by
    intro z hz i
    have h1 : 0 ≤ z i := hz.1.1 i
    have h2 : ¬ 0 < z i := fun h => by simpa using (hz.1.2 i).2 h
    exact le_antisymm (not_lt.1 h2) h1
  have hxy : x = y := PiLp.ext fun i => by rw [hz x hx i, hz y hy i]
  rw [hxy, measure_add_measure_compl hA, htot y hy.1.1 0]

theorem mem_some_box {S : Finset (Fin n)} {x : SDEState n} (hx : x ∈ F S) :
    ∃ k : ℕ, x ∈ faceBox S ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1) := by
  have hi : ∀ i ∈ S, ∃ N : ℕ, ((N : ℝ) + 1)⁻¹ ≤ x i ∧ x i ≤ (N : ℝ) + 1 := by
    intro i hiS
    have hp : 0 < x i := (hx.2 i).1 hiS
    obtain ⟨N, hN⟩ := exists_nat_gt (max (x i) (x i)⁻¹)
    refine ⟨N, ?_, ?_⟩
    · have : (x i)⁻¹ < (N : ℝ) + 1 := by linarith [le_max_right (x i) (x i)⁻¹]
      exact (inv_lt_of_inv_lt₀ hp this).le
    · linarith [le_max_left (x i) (x i)⁻¹]
  choose! N hN using hi
  refine ⟨S.sup N, hx, fun i hiS => ?_⟩
  have hle : (N i : ℝ) + 1 ≤ ((S.sup N : ℕ) : ℝ) + 1 := by
    have : N i ≤ S.sup N := Finset.le_sup hiS
    have : (N i : ℝ) ≤ (S.sup N : ℕ) := by exact_mod_cast this
    linarith
  have hpos : (0 : ℝ) < (N i : ℝ) + 1 := by positivity
  refine ⟨le_trans (inv_anti₀ hpos hle) (hN i hiS).1, le_trans (hN i hiS).2 hle⟩

theorem faceBox_mono {S : Finset (Fin n)} {k k' : ℕ} (h : k ≤ k') :
    faceBox S ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1) ⊆ faceBox S ((k' : ℝ) + 1)⁻¹ ((k' : ℝ) + 1) := by
  intro x hx
  have hle : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by
    have : (k : ℝ) ≤ k' := by exact_mod_cast h
    linarith
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  refine ⟨hx.1, fun i hi => ⟨le_trans (inv_anti₀ hpos hle) (hx.2 i hi).1, le_trans (hx.2 i hi).2 hle⟩⟩

theorem faceInt_subset_F (μ : Measure (SDEState n)) : faceInt μ ⊆ F (supp μ) := by
  intro x hx
  refine ⟨hx.1.1, fun i => ⟨fun hi => hx.2 i hi, fun hp => ?_⟩⟩
  by_contra hi
  rw [hx.1.2 i hi] at hp
  exact lt_irrefl _ hp

theorem exists_box_pos {μ : Measure (SDEState n)} {S : Finset (Fin n)} (h : μ (F S) ≠ 0) :
    ∃ k : ℕ, μ (faceBox S ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  refine measure_mono_null (fun x hx => ?_) (measure_iUnion_null hc)
  obtain ⟨k, hk⟩ := mem_some_box hx
  exact Set.mem_iUnion.2 ⟨k, hk⟩

/-- K1b: two ergodic measures with the same support are equal. -/
theorem eq_of_supp_eq (hface : FaceInv P X) (htot : TotOne P X)
    (hov : ∀ S : Finset (Fin n), S ≠ Finset.univ → FaceOverlap P X S) {μ ν : Measure (SDEState n)}
    (hEμ : IsErgodic P X μ) (hμo : μ (openOrthant n) = 0) (hEν : IsErgodic P X ν)
    (hs : supp μ = supp ν) : μ = ν := by
  haveI := hEμ.1.1
  haveI := hEν.1.1
  have hμF : μ (F (supp μ))ᶜ = 0 :=
    measure_mono_null (Set.compl_subset_compl.2 (faceInt_subset_F μ)) (concentrates hface hEμ)
  have hνF : ν (F (supp μ))ᶜ = 0 := by
    rw [hs]
    exact measure_mono_null (Set.compl_subset_compl.2 (faceInt_subset_F ν)) (concentrates hface hEν)
  have hμ1 : μ (F (supp μ)) ≠ 0 := by
    rw [(prob_compl_eq_zero_iff (measurableSet_F _)).1 hμF]; exact one_ne_zero
  have hν1 : ν (F (supp μ)) ≠ 0 := by
    rw [(prob_compl_eq_zero_iff (measurableSet_F _)).1 hνF]; exact one_ne_zero
  obtain ⟨k1, hk1⟩ := exists_box_pos hμ1
  obtain ⟨k2, hk2⟩ := exists_box_pos hν1
  have hpos : (0 : ℝ) < ((max k1 k2 : ℕ) : ℝ) + 1 := by positivity
  have hab : (((max k1 k2 : ℕ) : ℝ) + 1)⁻¹ ≤ ((max k1 k2 : ℕ) : ℝ) + 1 := by
    have h1 : (1 : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) + 1 := by
      have : (0 : ℝ) ≤ ((max k1 k2 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact le_trans (inv_le_one_of_one_le₀ h1) h1
  have hne : supp μ ≠ Finset.univ := by
    intro hu
    apply hμ1
    have hsub : F (supp μ) ⊆ openOrthant n := by
      intro x hx
      show ∀ i, 0 < x i
      intro i
      exact (hx.2 i).1 (hu ▸ Finset.mem_univ i)
    exact measure_mono_null hsub hμo
  obtain ⟨t, ε, hε, hov'⟩ := hov (supp μ) hne _ _ (inv_pos.2 hpos) hab
  refine eq_of_overlap htot hEμ hEν (measurableSet_faceBox _ _ _) ?_ ?_ t hε hov'
  · exact fun h => hk1 (measure_mono_null (faceBox_mono (le_max_left k1 k2)) h)
  · exact fun h => hk2 (measure_mono_null (faceBox_mono (le_max_right k1 k2)) h)

/-- K1: `M` is finite. -/
theorem M_finite (hface : FaceInv P X) (htot : TotOne P X)
    (hov : ∀ S : Finset (Fin n), S ≠ Finset.univ → FaceOverlap P X S) :
    (bdryErgodic P X).Finite := by
  have hinj : Set.InjOn supp (bdryErgodic P X) := fun μ hμ ν hν h =>
    eq_of_supp_eq hface htot hov hμ.1 hμ.2 hν.1 h
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

end StochKolmogorov.Classify.K1

end Mod_K1

-- ===== module KinvConv =====
section Mod_KinvConv

/-! K2b of theorem_1_3 (8f909832): an invariant probability measure with no mass on the open orthant
lies in `Conv(M)` (finite convex combination of boundary ergodic measures). Per open face `F I`
(`I ≠ univ`): two invariant probabilities living on `F I` are equal (Hahn split into singular
invariant parts + TV overlap on a face box), so the normalized restriction of `π` to `F I` is ergodic. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.KinvConv

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

/-- Singular finite invariant measures cannot both charge an overlap set. -/
theorem false_of_overlap {m m' : Measure (SDEState n)} (hm : Rel P X m) (hm' : Rel P X m')
    {H : Set (SDEState n)} (hH : MeasurableSet H) (hmH : m Hᶜ = 0) (hm'H : m' H = 0)
    {K : Set (SDEState n)} (hK : MeasurableSet K) (hmK : m K ≠ 0) (hm'K : m' K ≠ 0)
    (t : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε)
    (hov : ∀ x ∈ K, ∀ y ∈ K, ∀ A : Set (SDEState n), MeasurableSet A →
      ε ≤ StochKolmogorov.Classify.trans P X t x A + StochKolmogorov.Classify.trans P X t y Aᶜ) :
    False := by
  have hy : ∃ y ∈ K, StochKolmogorov.Classify.trans P X t y H < ε := by
    by_contra hc
    push_neg at hc
    have b1 : ε * m' K ≤ ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x H ∂m' := by
      rw [← setLIntegral_const]
      exact lintegral_mono_ae ((ae_restrict_iff' hK).2 (ae_of_all _ hc))
    have b2 : ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x H ∂m' ≤ 0 :=
      (setLIntegral_le_lintegral _ _).trans_eq ((hm' t H hH).trans hm'H)
    have := le_antisymm (b1.trans b2) zero_le
    rcases mul_eq_zero.1 this with h | h
    · exact hε.ne' h
    · exact hm'K h
  obtain ⟨y, hyK, hy⟩ := hy
  have hδ : 0 < ε - StochKolmogorov.Classify.trans P X t y H := tsub_pos_of_lt hy
  have hx : ∀ x ∈ K, ε - StochKolmogorov.Classify.trans P X t y H ≤
      StochKolmogorov.Classify.trans P X t x Hᶜ := by
    intro x hx
    have := hov x hx y hyK Hᶜ hH.compl
    rw [compl_compl] at this
    exact tsub_le_iff_right.2 this
  have b1 : (ε - StochKolmogorov.Classify.trans P X t y H) * m K ≤
      ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x Hᶜ ∂m := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hK).2 (ae_of_all _ hx))
  have b2 : ∫⁻ x in K, StochKolmogorov.Classify.trans P X t x Hᶜ ∂m ≤ 0 :=
    (setLIntegral_le_lintegral _ _).trans_eq ((hm t Hᶜ hH.compl).trans hmH)
  have := le_antisymm (b1.trans b2) zero_le
  rcases mul_eq_zero.1 this with h | h
  · exact hδ.ne' h
  · exact hmK h

/-- Two invariant probabilities living on the open face `F I` are equal. -/
theorem inv_eq_of_face (htot : TotOne P X) {I : Finset (Fin n)} (hov : FaceOverlap P X I)
    {μ ν : Measure (SDEState n)} (hμI : IsInvariant P X μ) (hνI : IsInvariant P X ν)
    (hμF : μ (F I)ᶜ = 0) (hνF : ν (F I)ᶜ = 0) : μ = ν := by
  haveI := hμI.1
  haveI := hνI.1
  have hμi : Rel P X μ := hμI.2.2
  have hνi : Rel P X ν := hνI.2.2
  obtain ⟨H, hH, hle, hge⟩ := hahn_decomposition μ ν
  have l1 : ν.restrict H ≤ μ.restrict H := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hle _ (hs.inter hH) Set.inter_subset_right
  have l2 : μ.restrict Hᶜ ≤ ν.restrict Hᶜ := by
    rw [Measure.le_iff]; intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs]
    exact hge _ (hs.inter hH.compl) Set.inter_subset_right
  set m := μ.restrict H - ν.restrict H with hm_def
  set m' := ν.restrict Hᶜ - μ.restrict Hᶜ with hm'_def
  set w := ν.restrict H + μ.restrict Hᶜ with hw_def
  have hμ : μ = m + w := by
    calc μ = μ.restrict H + μ.restrict Hᶜ := (Measure.restrict_add_restrict_compl hH).symm
      _ = (m + ν.restrict H) + μ.restrict Hᶜ := by rw [Measure.sub_add_cancel_of_le l1]
      _ = m + w := by rw [add_assoc]
  have hν : ν = m' + w := by
    calc ν = ν.restrict H + ν.restrict Hᶜ := (Measure.restrict_add_restrict_compl hH).symm
      _ = ν.restrict H + (m' + μ.restrict Hᶜ) := by rw [Measure.sub_add_cancel_of_le l2]
      _ = m' + w := by rw [add_left_comm]
  have mle : m ≤ μ := hμ ▸ Measure.le_add_right le_rfl
  have m'le : m' ≤ ν := hν ▸ Measure.le_add_right le_rfl
  haveI : IsFiniteMeasure m := isFiniteMeasure_of_le μ mle
  haveI : IsFiniteMeasure m' := isFiniteMeasure_of_le ν m'le
  have wle : w ≤ μ := hμ ▸ Measure.le_add_left le_rfl
  haveI : IsFiniteMeasure w := isFiniteMeasure_of_le μ wle
  have hmc : m Hᶜ = 0 := by
    rw [hm_def, Measure.sub_apply hH.compl l1, Measure.restrict_apply hH.compl,
      Set.compl_inter_self, measure_empty, zero_tsub]
  have hm'c : m' H = 0 := by
    rw [hm'_def, Measure.sub_apply hH l2, Measure.restrict_apply hH,
      Set.inter_compl_self, measure_empty, zero_tsub]
  have hmA : ∀ A, MeasurableSet A → A ⊆ H → m A ≤ μ A - ν A := by
    intro A hA hAH
    rw [hm_def, Measure.sub_apply hA l1, Measure.restrict_apply hA, Measure.restrict_apply hA,
      Set.inter_eq_left.2 hAH]
  have hm'A : ∀ A, MeasurableSet A → A ⊆ Hᶜ → m' A ≤ ν A - μ A := by
    intro A hA hAH
    rw [hm'_def, Measure.sub_apply hA l2, Measure.restrict_apply hA, Measure.restrict_apply hA,
      Set.inter_eq_left.2 hAH]
  have hm'cc : m' Hᶜᶜ = 0 := by rw [compl_compl]; exact hm'c
  have null_of_le : ∀ (q r : Measure (SDEState n)) (S : Set (SDEState n)), q ≤ r → r S = 0 →
      q S = 0 := fun q r S hq hr => le_antisymm ((Measure.le_iff'.1 hq _).trans_eq hr) zero_le
  have hmR : Rel P X m :=
    super_to_rel htot (null_of_le m μ _ mle hμI.2.1) (super_of_split hμi hνi hμ hν hH hmc hmA)
  have hm'R : Rel P X m' :=
    super_to_rel htot (null_of_le m' ν _ m'le hνI.2.1)
      (super_of_split hνi hμi hν hμ hH.compl hm'cc hm'A)
  have hsμ : m Set.univ + w Set.univ = 1 := by rw [← Measure.add_apply, ← hμ, measure_univ]
  have hsν : m' Set.univ + w Set.univ = 1 := by rw [← Measure.add_apply, ← hν, measure_univ]
  have hcc : m Set.univ = m' Set.univ :=
    (ENNReal.add_left_inj (measure_ne_top w _)).1 (hsμ.trans hsν.symm)
  by_cases h0 : m Set.univ = 0
  · have z1 : m = 0 := Measure.measure_univ_eq_zero.1 h0
    have z2 : m' = 0 := Measure.measure_univ_eq_zero.1 (hcc ▸ h0)
    rw [hμ, hν, z1, z2]
  exfalso
  have hmF : m (F I) ≠ 0 := by
    intro hz
    apply h0
    have := measure_union_le (μ := m) (F I) (F I)ᶜ
    rw [Set.union_compl_self, hz, null_of_le m μ _ mle hμF, add_zero] at this
    exact le_antisymm this zero_le
  have hm'F : m' (F I) ≠ 0 := by
    intro hz
    apply h0
    rw [hcc]
    have := measure_union_le (μ := m') (F I) (F I)ᶜ
    rw [Set.union_compl_self, hz, null_of_le m' ν _ m'le hνF, add_zero] at this
    exact le_antisymm this zero_le
  obtain ⟨k1, hk1⟩ := exists_box_pos hmF
  obtain ⟨k2, hk2⟩ := exists_box_pos hm'F
  set k := max k1 k2
  have hK := measurableSet_faceBox (n := n) I ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)
  have hmK : m (faceBox I ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)) ≠ 0 := fun hz =>
    hk1 (measure_mono_null (faceBox_mono (le_max_left k1 k2)) hz)
  have hm'K : m' (faceBox I ((k : ℝ) + 1)⁻¹ ((k : ℝ) + 1)) ≠ 0 := fun hz =>
    hk2 (measure_mono_null (faceBox_mono (le_max_right k1 k2)) hz)
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hab : ((k : ℝ) + 1)⁻¹ ≤ (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    exact le_trans (inv_le_one_of_one_le₀ this) this
  obtain ⟨t, ε, hε, hovt⟩ := hov _ _ (inv_pos.2 hk0) hab
  exact false_of_overlap hmR hm'R hH hmc hm'c hK hmK hm'K t hε hovt

/-- An invariant probability living on the open face `F I` is ergodic. -/
theorem ergodic_of_face (htot : TotOne P X) {I : Finset (Fin n)} (hov : FaceOverlap P X I)
    {π : Measure (SDEState n)} (hπ : IsInvariant P X π) (hπF : π (F I)ᶜ = 0) :
    IsErgodic P X π := by
  refine ⟨hπ, fun ν₁ ν₂ h1 _ a ha _ he => ?_⟩
  refine inv_eq_of_face htot hov h1 hπ ?_ hπF
  have hle : (a : ℝ≥0∞) * ν₁ (F I)ᶜ ≤ π (F I)ᶜ := by
    rw [he, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact le_self_add
  rw [hπF] at hle
  have := le_antisymm hle zero_le
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (by exact_mod_cast ha.ne')
  · exact h

theorem F_disjoint {I J : Finset (Fin n)} (h : I ≠ J) : Disjoint (F I) (F J) :=
  Set.disjoint_left.2 fun _ hI hJ => h (F_unique hI hJ)

theorem orthant_eq_iUnion : orthant n = ⋃ I ∈ (Finset.univ : Finset (Finset (Fin n))), F I := by
  ext x
  simp only [Finset.mem_univ, Set.iUnion_true, Set.mem_iUnion]
  exact ⟨fun hx => ⟨pos x, mem_F_pos hx⟩, fun ⟨_, h⟩ => h.1⟩

theorem F_univ_subset : F (Finset.univ : Finset (Fin n)) ⊆ openOrthant n :=
  fun _ hx i => (hx.2 i).1 (Finset.mem_univ i)

theorem openOrthant_null_of_ne {I : Finset (Fin n)} (hI : I ≠ Finset.univ)
    {x : SDEState n} (hx : x ∈ F I) : x ∉ openOrthant n := by
  intro ho
  apply hI
  ext i
  simp only [Finset.mem_univ, iff_true]
  exact (hx.2 i).2 (ho i)

/-- K2b: an invariant probability with no mass on the open orthant lies in `Conv(M)`. -/
theorem conv_of_inv (htot : TotOne P X) (hface : FaceInv P X)
    (hov : ∀ I : Finset (Fin n), I ≠ Finset.univ → FaceOverlap P X I)
    {π : Measure (SDEState n)} (hπ : IsInvariant P X π) (hπo : π (openOrthant n) = 0) :
    π ∈ conv (bdryErgodic P X) := by
  classical
  haveI := hπ.1
  set T := (Finset.univ : Finset (Finset (Fin n))).filter (fun I => π (F I) ≠ 0) with hT
  have hTne : ∀ I ∈ T, I ≠ Finset.univ := by
    intro I hI he
    rw [hT, Finset.mem_filter, he] at hI
    exact hI.2 (measure_mono_null F_univ_subset hπo)
  let g : Finset (Fin n) → Measure (SDEState n) := fun I => (π (F I))⁻¹ • π.restrict (F I)
  have hrelI : ∀ I, ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ x in F I, StochKolmogorov.Classify.trans P X t x A ∂π = π (A ∩ F I) :=
    fun I t A hA => (restrict_rel hface hπ.2.1 hπ.2.2 I t A hA).1
  have hgI : ∀ I ∈ T, IsInvariant P X (g I) := fun I hI =>
    inv_restrict hπ.2.1 (measurableSet_F I) rfl (Finset.mem_filter.1 hI).2 (measure_ne_top _ _)
      (hrelI I)
  have hgF : ∀ I, g I (F I)ᶜ = 0 := by
    intro I
    simp only [g, Measure.smul_apply, Measure.restrict_apply (measurableSet_F I).compl,
      Set.compl_inter_self, measure_empty, smul_eq_mul, mul_zero]
  have hgE : ∀ I ∈ T, g I ∈ bdryErgodic P X := by
    intro I hI
    refine ⟨ergodic_of_face htot (hov I (hTne I hI)) (hgI I hI) (hgF I), ?_⟩
    exact measure_mono_null (show openOrthant n ⊆ (F I)ᶜ from
      fun x hx hxF => openOrthant_null_of_ne (hTne I hI) hxF hx) (hgF I)
  have hgFI : ∀ I ∈ T, g I (F I) = 1 := by
    intro I hI
    have hc0 := (Finset.mem_filter.1 hI).2
    simp only [g, Measure.smul_apply, Measure.restrict_apply (measurableSet_F I), Set.inter_self,
      smul_eq_mul]
    exact ENNReal.inv_mul_cancel hc0 (measure_ne_top _ _)
  have hinj : ∀ I ∈ T, ∀ J ∈ T, g I = g J → I = J := by
    intro I hI J hJ he
    by_contra hne
    have h1 := hgFI I hI
    rw [he] at h1
    have : g J (F I) = 0 :=
      measure_mono_null (fun x hx hxJ => (F_disjoint hne).ne_of_mem hx hxJ rfl) (hgF J)
    rw [this] at h1
    exact zero_ne_one h1
  let w : Finset (Fin n) → ℝ≥0 := fun I => (π (F I)).toNNReal
  have hw : ∀ I, (w I : ℝ≥0∞) = π (F I) := fun I => ENNReal.coe_toNNReal (measure_ne_top _ _)
  let p : Measure (SDEState n) → ℝ≥0 := fun ν => ∑ I ∈ T, if g I = ν then w I else 0
  have hp : ∀ J ∈ T, p (g J) = w J := by
    intro J hJ
    simp only [p]
    rw [Finset.sum_eq_single J]
    · simp
    · intro I hI hIJ
      rw [if_neg (fun h => hIJ (hinj I hI J hJ h))]
    · intro h; exact absurd hJ h
  -- the face decomposition of `π`
  have hsum_sets : ∀ A : Set (SDEState n), MeasurableSet A →
      ∑ I ∈ T, π (A ∩ F I) = π A := by
    intro A hA
    have hall : ∑ I ∈ (Finset.univ : Finset (Finset (Fin n))), π (A ∩ F I) = π A := by
      rw [← measure_biUnion_finset]
      · rw [← Set.inter_iUnion₂, ← orthant_eq_iUnion]
        have := measure_inter_add_diff (μ := π) A (measurableSet_orthant (n := n))
        rw [show π (A \ orthant n) = 0 from measure_mono_null (Set.diff_subset_compl _ _) hπ.2.1,
          add_zero] at this
        exact this
      · intro I _ J _ hIJ
        exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (F_disjoint hIJ)
      · intro I _; exact hA.inter (measurableSet_F I)
    rw [← hall, hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun I _ => ?_
    split_ifs with h
    · rfl
    · push_neg at h
      exact (measure_mono_null Set.inter_subset_right h).symm
  refine ⟨T.image g, p, ?_, ?_, ?_, ?_⟩
  · intro ν hν
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hν)
    exact hgE I hI
  · intro ν hν
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hν
    rw [hp I hI]
    exact ENNReal.toNNReal_pos (Finset.mem_filter.1 hI).2 (measure_ne_top _ _)
  · rw [Finset.sum_image hinj]
    rw [Finset.sum_congr rfl fun I hI => hp I hI]
    have h1 := hsum_sets Set.univ MeasurableSet.univ
    simp only [Set.univ_inter, measure_univ] at h1
    have : ((∑ I ∈ T, w I : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [ENNReal.coe_finset_sum]
      simp only [hw]
      exact h1
    exact_mod_cast this
  · rw [Finset.sum_image hinj]
    ext A hA
    rw [Measure.coe_finset_sum, Finset.sum_apply, ← hsum_sets A hA]
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [hp I hI, hw I]
    simp only [g, Measure.smul_apply, Measure.restrict_apply hA, smul_eq_mul]
    rw [← mul_assoc, ENNReal.mul_inv_cancel (Finset.mem_filter.1 hI).2 (measure_ne_top _ _),
      one_mul]

end StochKolmogorov.Classify.KinvConv

end Mod_KinvConv

-- ===== module K2a =====
section Mod_K2a

/-! K2a of theorem_1_3 (8f909832): no invariant probability charges the open orthant.
`ae_eq_Gam`: with Lemma 5.7 tightness, `E_y =ᵐ {rational path ∈ Gam2.Gam C μ}` for every `y`.
`pos_of'`: K4 without the cover hypothesis (breaks the K2/K4 circle).
`no_interior`: stationarity from `π|openOrthant` + `pos_of'` + exponential decay of a coordinate on `E_y`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.K2a

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K4

variable {n : ℕ} {Ω : Type*}

theorem ae_eq_Gam [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n) {B : ℝ≥0 → Ω → SDEState n}
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X y t ω})
    (μ : Measure (SDEState n)) (hμ : IsProbabilityMeasure μ) (y : SDEState n) (hy : y ∈ orthant n) :
    K3.rpath X y ⁻¹' Gam2.Gam C μ =ᵐ[P] extinctEvent C X y μ := by
  have hc := (hX.2.2 y hy).2.1
  filter_upwards [h57 y hy] with ω hT
  exact propext ⟨fun h => Gam2.extinct_of_RC C μ X y ω (hc ω) ((Gam2.mem_Gam_iff C μ X y ω (hc ω)).1 h),
    fun h => (Gam2.mem_Gam_iff C μ X y ω (hc ω)).2 (Gam2.RC_of_extinct C μ X y ω (hc ω) hT h)⟩

theorem pos_of' [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X y t ω})
    (h59 : ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ y ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X y μ)).toReal)
    (hreach : ∀ x ∈ openOrthant n, ∀ U : Set (SDEState n), IsOpen U → U.Nonempty →
      U ⊆ openOrthant n → ∃ t : ℝ≥0, 0 < P {ω | X x t ω ∈ U})
    (hFD : K4.FDMarkov P X) :
    ∀ x ∈ openOrthant n, ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ) := by
  intro x hx μ hμ
  haveI : IsProbabilityMeasure P := hX.1
  have hxo : x ∈ orthant n := fun i => (hx i).le
  have hsol := hX.2.2 x hxo
  obtain ⟨Δ, hΔ, h5⟩ := h59 μ hμ 2 (by norm_num) (1 / 2) (by norm_num)
  set U : Set (SDEState n) := ⋂ i, {y : SDEState n | (i ∈ supp μ → 1 / 2 < y i ∧ y i < 2) ∧
    (i ∉ supp μ → 0 < y i ∧ y i < Δ)} with hUdef
  have hci : ∀ i : Fin n, Continuous fun y : SDEState n => y i := fun i => PiLp.continuous_apply 2 _ i
  have hUo : IsOpen U := by
    refine isOpen_iInter_of_finite fun i => ?_
    by_cases h : i ∈ supp μ
    · simp only [h, not_true_eq_false, IsEmpty.forall_iff, and_true, forall_const]
      exact (isOpen_lt continuous_const (hci i)).inter (isOpen_lt (hci i) continuous_const)
    · simp only [h, IsEmpty.forall_iff, true_and, not_false_eq_true, forall_const]
      exact (isOpen_lt continuous_const (hci i)).inter (isOpen_lt (hci i) continuous_const)
  have hUint : U ⊆ openOrthant n := by
    intro y hy i
    have := Set.mem_iInter.mp hy i
    by_cases h : i ∈ supp μ
    · linarith [(this.1 h).1]
    · exact (this.2 h).1
  have hUK : U ⊆ Kbox μ 2 Δ := by
    intro y hy
    refine ⟨hUint hy, fun i hi => ?_, fun i hi => ((Set.mem_iInter.mp hy i).2 hi).2⟩
    have := (Set.mem_iInter.mp hy i).1 hi
    constructor
    · norm_num; linarith [this.1]
    · norm_num; linarith [this.2]
  have hUne : U.Nonempty := by
    refine ⟨WithLp.toLp 2 (fun i => if i ∈ supp μ then (1 : ℝ) else Δ / 2), Set.mem_iInter.mpr fun i => ?_⟩
    by_cases h : i ∈ supp μ
    · simp only [PiLp.toLp_apply, if_pos h, Set.mem_setOf_eq]
      exact ⟨fun _ => ⟨by norm_num, by norm_num⟩, fun h' => absurd h h'⟩
    · simp only [PiLp.toLp_apply, if_neg h, Set.mem_setOf_eq]
      exact ⟨fun h' => absurd h' h, fun _ => ⟨by linarith, by linarith⟩⟩
  obtain ⟨t, ht⟩ := hreach x hx U hUo hUne hUint
  set Γ := Gam2.Gam C μ with hΓ
  haveI : IsProbabilityMeasure (trans P X t x) :=
    Measure.isProbabilityMeasure_map (hsol.1 t).aemeasurable
  have hYm : Measurable (shiftPath X x t) := measurable_pi_lambda _ fun q => hsol.1 _
  have hZm : ∀ y, Measurable (Zf X y) := by
    intro y
    unfold Zf
    split_ifs with h
    · exact K3.measurable_rpath X y (hX.2.2 y h).1
    · exact measurable_const
  have hmix := PathMix.mix_all P (shiftPath X x t) hYm (Zf X) hZm (trans P X t x) (hFD x hx t) Γ
    (Gam2.measurableSet_Gam C μ)
  haveI : IsProbabilityMeasure μ := hμ.1.1.1.1
  have hae : K4.shiftPath X x t ⁻¹' Γ =ᵐ[P] extinctEvent C X x μ := by
    filter_upwards [ae_eq_Gam P C X hX h57 μ hμ.1.1.1.1 x hxo] with ω hω
    rw [← hω]
    exact propext (Gam2.shift_mem_iff C μ X x ω (hsol.2.1 ω) t)
  -- on `U` the sink probability is at least 1/2
  have hy : ∀ y ∈ U, ENNReal.ofReal (1 / 2) ≤ P (Zf X y ⁻¹' Γ) := by
    intro y hyU
    have hyo : y ∈ orthant n := fun i => (hUint hyU i).le
    have hZ : Zf X y = K3.rpath X y := by funext ω; simp only [Zf, if_pos hyo]
    rw [hZ, measure_congr (ae_eq_Gam P C X hX h57 μ hμ.1.1.1.1 y hyo)]
    have := h5 y (hUK hyU)
    exact ENNReal.ofReal_le_of_le_toReal (by linarith)
  have hκU : trans P X t x U ≠ 0 := by
    unfold trans
    rw [Measure.map_apply (hsol.1 t) hUo.measurableSet]
    exact ht.ne'
  calc (0 : ℝ≥0∞) < ENNReal.ofReal (1 / 2) * trans P X t x U :=
        ENNReal.mul_pos (by simp) hκU
    _ = ∫⁻ _ in U, ENNReal.ofReal (1 / 2) ∂(trans P X t x) := (setLIntegral_const U _).symm
    _ ≤ ∫⁻ y in U, P (Zf X y ⁻¹' Γ) ∂(trans P X t x) := setLIntegral_mono hmix.1 hy
    _ ≤ ∫⁻ y, P (Zf X y ⁻¹' Γ) ∂(trans P X t x) := setLIntegral_le_lintegral U _
    _ = P (shiftPath X x t ⁻¹' Γ) := hmix.2.symm
    _ = P (extinctEvent C X x μ) := measure_congr hae

/-- K2a: no invariant probability charges the open orthant. -/
theorem no_interior [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X y t ω})
    (h59 : ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ y ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X y μ)).toReal)
    (hreach : ∀ x ∈ openOrthant n, ∀ U : Set (SDEState n), IsOpen U → U.Nonempty →
      U ⊆ openOrthant n → ∃ t : ℝ≥0, 0 < P {ω | X x t ω ∈ U})
    (hFD : K4.FDMarkov P X) (hface : K1a.FaceInv P X) (hM1 : (M1 P C X).Nonempty)
    {π : Measure (SDEState n)} (hπ : IsInvariant P X π) : π (openOrthant n) = 0 := by
  haveI : IsProbabilityMeasure P := hX.1
  haveI := hπ.1
  by_contra hne
  obtain ⟨μ, hμ⟩ := hM1
  haveI hμp : IsProbabilityMeasure μ := hμ.1.1.1.1
  have hsupp : ∃ i0, i0 ∉ supp μ := by
    by_contra h
    push_neg at h
    have hc := K1a.concentrates hface hμ.1.1
    have hsub : faceInt μ ⊆ openOrthant n := fun x hx i => hx.2 i (h i)
    have h0 : μ (faceInt μ) = 0 := measure_mono_null hsub hμ.1.2
    have := measure_union_le (μ := μ) (faceInt μ) (faceInt μ)ᶜ
    rw [Set.union_compl_self, h0, hc, add_zero, measure_univ] at this
    exact absurd this (by norm_num)
  obtain ⟨i0, hi0⟩ := hsupp
  have hlam : lyap C i0 μ < 0 := hμ.2.1 i0 hi0
  set Γ := Gam2.Gam C μ with hΓdef
  have hΓ : MeasurableSet Γ := Gam2.measurableSet_Gam C μ
  let x0 : SDEState n := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hx0 : x0 ∈ openOrthant n := fun i => by simp [x0]
  have hx0o : x0 ∈ orthant n := fun i => (hx0 i).le
  have hsol0 := hX.2.2 x0 hx0o
  haveI : IsProbabilityMeasure (trans P X 0 x0) :=
    Measure.isProbabilityMeasure_map (hsol0.1 0).aemeasurable
  have hZm : ∀ y, Measurable (Zf X y) := by
    intro y
    unfold Zf
    split_ifs with h
    · exact K3.measurable_rpath X y (hX.2.2 y h).1
    · exact measurable_const
  have hmeas : ∀ S : Set (ℚ → SDEState n), MeasurableSet S →
      Measurable (fun y => P (Zf X y ⁻¹' S)) := fun S hS =>
    (PathMix.mix_all P (shiftPath X x0 0) (measurable_pi_lambda _ fun q => hsol0.1 _) (Zf X) hZm
      (trans P X 0 x0) (hFD x0 hx0 0) S hS).1
  set g : SDEState n → ℝ≥0∞ := fun y => P (Zf X y ⁻¹' Γ) with hgdef
  have hgm : Measurable g := hmeas Γ hΓ
  have hZ : ∀ y ∈ orthant n, Zf X y = K3.rpath X y := fun y hy => by
    funext ω; simp only [Zf, if_pos hy]
  have hgpos : ∀ y ∈ openOrthant n, 0 < g y := by
    intro y hy
    have hyo : y ∈ orthant n := fun i => (hy i).le
    show 0 < P (Zf X y ⁻¹' Γ)
    rw [hZ y hyo, measure_congr (ae_eq_Gam P C X hX h57 μ hμp y hyo)]
    exact pos_of' P C B X hX h57 h59 hreach hFD y hy μ hμ
  have hFu : K1a.F (Finset.univ : Finset (Fin n)) = openOrthant n := by
    ext x
    constructor
    · intro hx i; exact (hx.2 i).1 (Finset.mem_univ i)
    · intro hx; exact ⟨fun i => (hx i).le, fun i => ⟨fun _ => hx i, fun _ => Finset.mem_univ i⟩⟩
  have hOm : MeasurableSet (openOrthant n) := by rw [← hFu]; exact K1a.measurableSet_F _
  set ρ := π.restrict (openOrthant n) with hρdef
  have hρinv : ∀ (t : ℝ≥0) (A : Set (SDEState n)), MeasurableSet A →
      ∫⁻ y, trans P X t y A ∂ρ = ρ A := by
    intro t A hA
    have := (K1a.restrict_rel hface hπ.2.1 hπ.2.2 Finset.univ t A hA).1
    rw [hFu] at this
    rw [Measure.restrict_apply hA]
    exact this
  let L : ℕ → Set (SDEState n) := fun k => {y | ∀ i, ((k : ℝ) + 1)⁻¹ ≤ y i}
  have hLm : ∀ k, MeasurableSet (L k) := by
    intro k
    have e : L k = ⋂ i, {y : SDEState n | ((k : ℝ) + 1)⁻¹ ≤ y i} := by ext y; simp [L]
    rw [e]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (K1a.coord_meas i)
  let tN : ℕ → ℝ≥0 := fun N => ((N : ℚ) : ℝ).toNNReal
  have htN : Tendsto tN atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨⌈(b : ℝ)⌉₊, fun a ha => ?_⟩
    have h1 : (b : ℝ) ≤ (a : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast ha)
    show b ≤ ((a : ℚ) : ℝ).toNNReal
    rw [Rat.cast_natCast]
    exact (Real.le_toNNReal_iff_coe_le (by positivity)).2 h1
  let CN : ℕ → ℕ → Set (ℚ → SDEState n) := fun k N => {f | f (N : ℚ) ∈ L k}
  have hCm : ∀ k N, MeasurableSet (CN k N) := fun k N => (measurable_pi_apply _) (hLm k)
  have hvan : ∀ k, ∀ y ∈ orthant n,
      Tendsto (fun N => P (Zf X y ⁻¹' (CN k N ∩ Γ))) atTop (𝓝 0) := by
    intro k y hy
    have hc := (hX.2.2 y hy).2.1
    have hm := (hX.2.2 y hy).1
    rw [hZ y hy]
    have hδ : (0 : ℝ) < ((k : ℝ) + 1)⁻¹ := by positivity
    have hpt : ∀ ω, ∀ᶠ N in atTop, ω ∉ K3.rpath X y ⁻¹' (CN k N ∩ Γ) := by
      intro ω
      by_cases hω : K3.rpath X y ω ∈ Γ
      · have hRC := (Gam2.mem_Gam_iff C μ X y ω (hc ω)).1 hω
        have hlim := (hRC.1 i0 hi0).1
        set lam := lyap C i0 μ with hlamdef
        set T : ℝ := 2 * Real.log ((k : ℝ) + 1)⁻¹ / lam with hT
        have hev : ∀ᶠ t : ℝ≥0 in atTop, X y t ω i0 < ((k : ℝ) + 1)⁻¹ := by
          filter_upwards [hlim.eventually (gt_mem_nhds (by linarith : lam < lam / 2)),
            eventually_ge_atTop (T + 1).toNNReal] with t ht1 ht2
          have htr : T + 1 ≤ (t : ℝ) :=
            (Real.le_coe_toNNReal _).trans (by exact_mod_cast ht2)
          have hlogδ : Real.log ((k : ℝ) + 1)⁻¹ ≤ 0 := by
            rw [Real.log_inv]
            have : (0 : ℝ) ≤ Real.log ((k : ℝ) + 1) :=
              Real.log_nonneg (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
            linarith
          have hT0 : 0 ≤ T := by
            rw [hT]
            exact div_nonneg_of_nonpos (by linarith) hlam.le
          have htpos : (0 : ℝ) < t := by linarith
          by_cases hx : X y t ω i0 ≤ 0
          · linarith
          push_neg at hx
          have h1 : Real.log (X y t ω i0) < lam / 2 * t := by
            have := (div_lt_iff₀ htpos).1 ht1
            linarith
          have h2 : lam / 2 * (t : ℝ) < lam / 2 * T :=
            mul_lt_mul_of_neg_left (by linarith) (by linarith)
          have h3 : lam / 2 * T = Real.log ((k : ℝ) + 1)⁻¹ := by
            rw [hT]; field_simp [hlam.ne] <;> ring_nf
          exact (Real.log_lt_log_iff hx hδ).1 (by linarith)
        filter_upwards [htN.eventually hev] with N hN hmem
        exact absurd (hmem.1 i0) (not_le.2 hN)
      · exact Eventually.of_forall fun N hmem => hω hmem.2
    have hmeasS : ∀ N, MeasurableSet (K3.rpath X y ⁻¹' (CN k N ∩ Γ)) := fun N =>
      (K3.measurable_rpath X y hm) ((hCm k N).inter hΓ)
    have h2 := tendsto_lintegral_of_dominated_convergence (μ := P) (fun _ => (1 : ℝ≥0∞))
      (F := fun N ω => (K3.rpath X y ⁻¹' (CN k N ∩ Γ)).indicator 1 ω) (f := fun _ => 0)
      (fun N => measurable_one.indicator (hmeasS N))
      (fun N => ae_of_all _ fun ω => by
        simp only [Set.indicator]
        split_ifs <;> simp)
      (by rw [lintegral_const, one_mul]; exact measure_ne_top _ _)
      (ae_of_all _ fun ω => tendsto_const_nhds.congr' (by
        filter_upwards [hpt ω] with N hN
        exact (Set.indicator_of_notMem hN 1).symm))
    rw [lintegral_zero] at h2
    exact h2.congr fun N => lintegral_indicator_one (hmeasS N)
  -- one level set
  have hlev : ∀ k, ρ (L k) ≤ ∫⁻ y, (1 - g y) ∂ρ := by
    intro k
    have hineq : ∀ N, ρ (L k) ≤ ∫⁻ y, P (Zf X y ⁻¹' (CN k N ∩ Γ)) ∂ρ + ∫⁻ y, (1 - g y) ∂ρ := by
      intro N
      rw [← hρinv (tN N) (L k) (hLm k), ← lintegral_add_left (hmeas _ ((hCm k N).inter hΓ))]
      refine lintegral_mono_ae ((ae_restrict_iff' hOm).2 (ae_of_all _ fun y hy => ?_))
      have hyo : y ∈ orthant n := fun i => (hy i).le
      have e1 : trans P X (tN N) y (L k) = P (Zf X y ⁻¹' CN k N) := by
        rw [hZ y hyo]
        unfold trans
        rw [Measure.map_apply ((hX.2.2 y hyo).1 _) (hLm k)]
        rfl
      rw [e1]
      have e2 : 1 - g y = P (Zf X y ⁻¹' Γ)ᶜ := by
        rw [prob_compl_eq_one_sub ((hZm y) hΓ)]
      rw [e2, Set.preimage_inter]
      calc P (Zf X y ⁻¹' CN k N)
          ≤ P (Zf X y ⁻¹' CN k N ∩ Zf X y ⁻¹' Γ) + P (Zf X y ⁻¹' CN k N \ Zf X y ⁻¹' Γ) :=
            measure_le_inter_add_diff _ _ _
        _ ≤ P (Zf X y ⁻¹' CN k N ∩ Zf X y ⁻¹' Γ) + P (Zf X y ⁻¹' Γ)ᶜ := by
            gcongr
            exact Set.diff_subset_compl _ _
    have hlimN : Tendsto (fun N => ∫⁻ y, P (Zf X y ⁻¹' (CN k N ∩ Γ)) ∂ρ) atTop (𝓝 0) := by
      have h2 := tendsto_lintegral_of_dominated_convergence (μ := ρ) (fun _ => (1 : ℝ≥0∞))
        (F := fun N y => P (Zf X y ⁻¹' (CN k N ∩ Γ))) (f := fun _ => 0)
        (fun N => hmeas _ ((hCm k N).inter hΓ))
        (fun N => ae_of_all _ fun y => prob_le_one)
        (by rw [lintegral_const, one_mul]; exact measure_ne_top _ _)
        ((ae_restrict_iff' hOm).2 (ae_of_all _ fun y hy => hvan k y (fun i => (hy i).le)))
      rwa [lintegral_zero] at h2
    have := hlimN.add_const (∫⁻ y, (1 - g y) ∂ρ)
    rw [zero_add] at this
    exact ge_of_tendsto' this hineq
  -- all level sets
  have hmono : Monotone L := by
    intro k k' hkk y hy i
    have hle : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by
      have : (k : ℝ) ≤ k' := by exact_mod_cast hkk
      linarith
    exact le_trans (inv_anti₀ (by positivity) hle) (hy i)
  have hcov : openOrthant n ⊆ ⋃ k, L k := by
    intro y hy
    obtain ⟨m, hm⟩ := exists_nat_gt (∑ i, (y i)⁻¹)
    refine Set.mem_iUnion.2 ⟨m, fun i => ?_⟩
    have hs : (y i)⁻¹ ≤ ∑ j, (y j)⁻¹ :=
      Finset.single_le_sum (f := fun j => (y j)⁻¹) (fun j _ => (inv_pos.2 (hy j)).le)
        (Finset.mem_univ i)
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [inv_le_comm₀ hm1 (hy i)]
    linarith
  have hρu : ρ Set.univ ≤ ∫⁻ y, (1 - g y) ∂ρ := by
    have h1 : ρ Set.univ ≤ ρ (⋃ k, L k) := by
      rw [hρdef, Measure.restrict_apply MeasurableSet.univ, Measure.restrict_apply
        (MeasurableSet.iUnion hLm), Set.univ_inter]
      exact measure_mono fun y hy => ⟨hcov hy, hy⟩
    exact h1.trans (le_of_tendsto' (tendsto_measure_iUnion_atTop hmono) hlev)
  have hG : 0 < ∫⁻ y, g y ∂ρ := by
    rw [lintegral_pos_iff_support hgm]
    have h1 : ρ (openOrthant n) ≠ 0 := by
      rw [hρdef, Measure.restrict_apply hOm, Set.inter_self]; exact hne
    exact lt_of_lt_of_le (pos_iff_ne_zero.2 h1)
      (measure_mono fun y hy => (hgpos y hy).ne')
  have hsub : ∫⁻ y, (1 - g y) ∂ρ = ρ Set.univ - ∫⁻ y, g y ∂ρ := by
    rw [lintegral_sub hgm (ne_top_of_le_ne_top (measure_ne_top ρ Set.univ)
      ((lintegral_mono fun y => (prob_le_one : g y ≤ 1)).trans_eq (by rw [lintegral_const, one_mul])))
      (ae_of_all _ fun y => (prob_le_one : g y ≤ 1)), lintegral_const, one_mul]
  rw [hsub] at hρu
  have hne0 : ρ Set.univ ≠ 0 := by
    intro h0
    apply hne
    have : ρ (openOrthant n) = 0 := measure_mono_null (Set.subset_univ _) h0
    rwa [hρdef, Measure.restrict_apply hOm, Set.inter_self] at this
  exact absurd hρu (not_le.2 (ENNReal.sub_lt_self (measure_ne_top _ _) hne0 hG.ne'))

end StochKolmogorov.Classify.K2a

end Mod_K2a

-- ===== module Face =====
section Mod_Face

/-! FaceOverlap (the open analytic child of K1) from the PROVED platform theorem
`StochKolmogorov.Persist.kolmogorov_face_box_tv_overlap` (44879068), whose model definitions are
literally those of `Classify` (same file modulo the namespace). Here its conclusion is a hypothesis
`hTV`; the reduction supplies it from the child theorem applied to `persistCoeffs C`. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace StochKolmogorov.Classify.Face

open StochKolmogorov.Classify EthierKurtz StochKolmogorov.Classify.K1a
  StochKolmogorov.Classify.ErgSing StochKolmogorov.Classify.K1

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {X : SDEState n → ℝ≥0 → Ω → SDEState n}

/-- The same coefficients, read as `Persist` coefficients. -/
def persistCoeffs (C : Coeffs n) : StochKolmogorov.Persist.Coeffs n := ⟨C.f, C.g, C.Γ⟩

theorem persist_family {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hX : IsSolutionFamily P C B X) :
    StochKolmogorov.Persist.IsSolutionFamily P (persistCoeffs C) B X := hX

theorem persist_hC {C : Coeffs n}
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ∀ i, LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((persistCoeffs C).f i) ∧
      LocallyLipschitzOn (StochKolmogorov.Persist.orthant n) ((persistCoeffs C).g i) := hC

theorem persist_hpd {C : Coeffs n}
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef) :
    ∀ x ∈ StochKolmogorov.Persist.orthant n, (Matrix.of fun i j => (persistCoeffs C).g i x *
      (persistCoeffs C).g j x * (persistCoeffs C).sig i j).PosDef := hpd

/-- The conclusion of `kolmogorov_face_box_tv_overlap` for the family `X`. -/
def FaceTV (P : Measure Ω) (X : SDEState n → ℝ≥0 → Ω → SDEState n) : Prop :=
  ∀ (I : Finset (Fin n)) {α β : ℝ}, 0 < α → α ≤ β →
    ∃ T : ℝ≥0, ∃ ε : ℝ, 0 < ε ∧
      ∀ x ∈ StochKolmogorov.Persist.faceOpen I, (∀ i ∈ I, α ≤ x i ∧ x i ≤ β) →
      ∀ y ∈ StochKolmogorov.Persist.faceOpen I, (∀ i ∈ I, α ≤ y i ∧ y i ≤ β) →
        MarkovChainCLT.tvDist (StochKolmogorov.Persist.trans P X T x)
          (StochKolmogorov.Persist.trans P X T y) ≤ 1 - ε

theorem faceBox_faceOpen {S : Finset (Fin n)} {a b : ℝ} {x : SDEState n}
    (hx : x ∈ faceBox S a b) : x ∈ StochKolmogorov.Persist.faceOpen S := by
  refine ⟨hx.1.1, fun i hi => ?_, fun i hi => (hx.1.2 i).1 hi⟩
  have h1 : 0 ≤ x i := hx.1.1 i
  have h2 : ¬ 0 < x i := fun h => hi ((hx.1.2 i).2 h)
  exact le_antisymm (not_lt.1 h2) h1

theorem abs_le_tvDist (μ ν : Measure (SDEState n)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {A : Set (SDEState n)} (hA : MeasurableSet A) :
    |(μ A).toReal - (ν A).toReal| ≤ MarkovChainCLT.tvDist μ ν := by
  unfold MarkovChainCLT.tvDist
  refine le_csSup ⟨1, ?_⟩ ⟨A, hA, rfl⟩
  rintro r ⟨B, -, rfl⟩
  have h1 : (μ B).toReal ≤ 1 := by
    have := prob_le_one (μ := μ) (s := B)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  have h2 : (ν B).toReal ≤ 1 := by
    have := prob_le_one (μ := ν) (s := B)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  rw [abs_le]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := μ B), ENNReal.toReal_nonneg (a := ν B)]

theorem eps_le_of_tvDist (μ ν : Measure (SDEState n)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {ε : ℝ} (h : MarkovChainCLT.tvDist μ ν ≤ 1 - ε)
    {A : Set (SDEState n)} (hA : MeasurableSet A) :
    ENNReal.ofReal ε ≤ μ A + ν Aᶜ := by
  have h0 := (abs_le_tvDist μ ν hA).trans h
  have hc : (ν Aᶜ).toReal = 1 - (ν A).toReal := by
    rw [prob_compl_eq_one_sub hA, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      ENNReal.toReal_one]
  have e : μ A + ν Aᶜ = ENNReal.ofReal ((μ A).toReal + (ν Aᶜ).toReal) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (measure_ne_top μ A), ENNReal.ofReal_toReal (measure_ne_top ν Aᶜ)]
  rw [e]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hc]
  have := (abs_le.1 h0).1
  linarith

theorem faceOverlap_of_tv {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hX : IsSolutionFamily P C B X) (hTV : FaceTV P X) (S : Finset (Fin n)) :
    FaceOverlap P X S := by
  haveI : IsProbabilityMeasure P := hX.1
  intro a b ha hab
  obtain ⟨T, ε, hε, hT⟩ := hTV S ha hab
  refine ⟨T, ENNReal.ofReal ε, ENNReal.ofReal_pos.2 hε, fun x hx y hy A hA => ?_⟩
  have hxo := faceBox_faceOpen hx
  have hyo := faceBox_faceOpen hy
  have hmx : Measurable (X x T) := (hX.2.2 x hx.1.1).1 T
  have hmy : Measurable (X y T) := (hX.2.2 y hy.1.1).1 T
  haveI : IsProbabilityMeasure (StochKolmogorov.Persist.trans P X T x) :=
    Measure.isProbabilityMeasure_map hmx.aemeasurable
  haveI : IsProbabilityMeasure (StochKolmogorov.Persist.trans P X T y) :=
    Measure.isProbabilityMeasure_map hmy.aemeasurable
  exact eps_le_of_tvDist _ _ (hT x hxo (fun i hi => hx.2 i hi) y hyo (fun i hi => hy.2 i hi)) hA

/-- K1 (`M` finite) with the face overlap discharged by `FaceTV`. -/
theorem M_finite' {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n} (hX : IsSolutionFamily P C B X)
    (hface : FaceInv P X) (hTV : FaceTV P X) :
    (bdryErgodic P X).Finite :=
  M_finite hface (totOne_of_family hX) (fun S _ => faceOverlap_of_tv hX hTV S)

end StochKolmogorov.Classify.Face

end Mod_Face

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

-- ===== module UcTop =====
section Mod_UcTop

/-! hU' of 8f909832 (paper p.28: `U(ω) ⊆ Conv(M) \ Conv(M²)` a.s.): Lemma 5.7 clause 2 (each
`π ∈ U(ω)` invariant) + K2a (`π(ℝⁿ,◦₊) = 0`) + K2b (`π ∈ Conv(M)`) + U-c (`π ∉ Conv(M²)` from
`λᵢ(π) ≤ 0` and the pointwise Assumption 1.5). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.UcTop

open StochKolmogorov.Classify EthierKurtz

variable {n : ℕ} {Ω : Type*}

theorem hU_of [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X y t ω} ∧
        ∀ π ∈ limitSet X y ω, IsInvariant P X π)
    (h59 : ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ y ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X y μ)).toReal)
    (hreach : ∀ x ∈ openOrthant n, ∀ U : Set (SDEState n), IsOpen U → U.Nonempty →
      U ⊆ openOrthant n → ∃ t : ℝ≥0, 0 < P {ω | X x t ω ∈ U})
    (hFD : K4.FDMarkov P X) (hface : K1a.FaceInv P X) (hM1 : (M1 P C X).Nonempty)
    (hTV : Face.FaceTV P X) (h15 : Assumption15 P C X)
    (x : SDEState n) (hx : x ∈ openOrthant n)
    (hlyap : ∀ᵐ ω ∂P, ∀ π ∈ limitSet X x ω, ∀ i, lyap C i π ≤ 0) :
    ∀ᵐ ω ∂P, ∀ π ∈ limitSet X x ω,
      π ∈ conv (bdryErgodic P X) ∧ π ∉ conv (M2 P C X) := by
  have hx' : x ∈ orthant n := fun i => (hx i).le
  have h57t : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X y t ω} :=
    fun y hy => (h57 y hy).mono fun ω h => h.1
  filter_upwards [h57 x hx', UcGlue.not_conv_M2 h15 hlyap] with ω h1 h2 π hπ
  have hinvπ := h1.2 π hπ
  exact ⟨KinvConv.conv_of_inv (K1.totOne_of_family hX) hface
    (fun I _ => Face.faceOverlap_of_tv hX hTV I) hinvπ
    (K2a.no_interior P C B X hX h57t h59 hreach hFD hface hM1 hinvπ), h2 π hπ⟩

end StochKolmogorov.Classify.UcTop

end Mod_UcTop

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

-- ===== module Top =====
section Mod_Top

/-! Top assembly of Theorem 1.3 (s13): every proved library piece chained; the hypotheses are
exactly the remaining obligations (sibling conclusions, child R, child C (via hFD), hL, hmom). -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Top

open StochKolmogorov.Classify EthierKurtz

theorem top_core {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h15 : Assumption15 P C X) (hM1 : (M1 P C X).Nonempty)
    -- Extinct.lemma_3_1 clause 2 (Proved b37a009a)
    (hcl : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0))
    -- Persist.kolmogorov_face_box_tv_overlap (Proved 44879068)
    (hTV : Face.FaceTV P X)
    -- FDM.fdMarkov_of over child C
    (hFD : K4.FDMarkov P X)
    -- child R
    (hreach : ∀ x ∈ openOrthant n, ∀ U : Set (SDEState n), IsOpen U → U.Nonempty →
      U ⊆ openOrthant n → ∃ t : ℝ≥0, 0 < P {ω | X x t ω ∈ U})
    -- lemma_5_7, lemma_5_9
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X y t ω} ∧
        ∀ π ∈ limitSet X y ω, IsInvariant P X π)
    (h59 : ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ y ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X y μ)).toReal)
    -- lemma_5_4 clause 1 and lemma_5_6, at some δ₁ > 0
    (δ₁ : ℝ) (hδ₁ : 0 < δ₁)
    (h54 : ∃ Khat : ℝ, 0 < Khat ∧ ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ₁ (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t))
    (h56 : ∀ x ∈ orthant n, ∀ ω : Ω, (∀ t, X x t ω ∈ orthant n) → ∀ Khat : ℝ,
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
    -- moment bound (Persist.lemma_3_2 clause 1, Proved 15eaca53)
    (hmom : ∀ x ∈ openOrthant n, ∃ δ K : ℝ, 0 < δ ∧ ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x (N : ℝ≥0) ω i) ^ δ) ∂P ≤ ENNReal.ofReal K)
    -- NEW: log LLN along squares
    (hL : ∀ x ∈ openOrthant n, ∀ᵐ ω ∂P, ∀ i, Tendsto (fun m : ℕ =>
      Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω i) / ((m ^ 2 : ℕ) : ℝ)
      - ∫ y, (C.f i y - C.sig i i * C.g i y ^ 2 / 2) ∂(occ X x ((m ^ 2 : ℕ) : ℝ) ω))
        atTop (𝓝 0)) :
    ∀ x ∈ openOrthant n,
      (∑' μ : M1 P C X, P (extinctEvent C X x (μ : Measure (SDEState n)))) = 1 ∧
        ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ) := by
  haveI : IsProbabilityMeasure P := hX.1
  have hC := hA.2.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hface : K1a.FaceInv P X := K1a.faceInv_of_clause hcl
  have hstay : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n := by
    intro x hx
    filter_upwards [hcl (K1a.pos x) x hx (fun i => (K1a.mem_F_pos hx).2 i)] with ω hω t i
    by_cases hi : i ∈ K1a.pos x
    · exact ((hω t).1 i hi).le
    · exact ((hω t).2 i hi).ge
  have hinv : ∀ x ∈ orthant n, ∀ s : ℝ≥0, ∀ᵐ ω ∂P, X x s ω ∈ orthant n := fun x hx s =>
    (hstay x hx).mono fun ω h => h s
  have hint : ∀ x ∈ openOrthant n, ∀ᵐ ω ∂P, ∀ s : ℝ≥0, X x s ω ∈ openOrthant n := by
    intro x hx
    filter_upwards [hcl Finset.univ x (fun i => (hx i).le)
      (fun i => ⟨fun _ => hx i, fun _ => Finset.mem_univ i⟩)] with ω hω s i
    exact (hω s).1 i (Finset.mem_univ i)
  have hfin : (M1 P C X).Finite :=
    (Face.M_finite' hX hface hTV).subset (fun μ hμ => hμ.1)
  have h57t : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {ν | ∃ t : ℝ, 1 ≤ t ∧ ν = occ X y t ω} :=
    fun y hy => (h57 y hy).mono fun ω h => h.1
  have hfc : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hC i).1.continuousOn
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  have hcover : ∀ x ∈ openOrthant n, ∀ᵐ ω ∂P, ∃ μ ∈ M1 P C X, ω ∈ extinctEvent C X x μ := by
    intro x hx
    have hxo : x ∈ orthant n := fun i => (hx i).le
    have hsol := hX.2.2 x hxo
    obtain ⟨δ, K, hδ, hmx⟩ := hmom x hx
    have hB := HB.log_le P X x c hc hsol.1 hδ hmx (hstay x hxo)
    obtain ⟨Kh, hKh, h54x⟩ := h54
    have hlyap := UcGlue.lyap_nonpos P C X c δ₁ hδ₁ hfc hgc x hsol.2.1 (h56 x hxo)
      ⟨Kh, hKh, h54x x hxo⟩ ((h57 x hxo).mono fun ω h => h.2) (hstay x hxo) (hL x hx) hB
    exact UGlue.K2_of_conv P C B X hX hC hinv hface hfin h57t h59 x hx (hint x hx)
      (UcTop.hU_of P C B X hX h57 h59 hreach hFD hface hM1 hTV h15 x hx hlyap)
  have htot := K1.totOne_of_family hX
  have hov : ∀ S : Finset (Fin n), S ≠ Finset.univ → K1.FaceOverlap P X S :=
    fun S _ => Face.faceOverlap_of_tv hX hTV S
  have hinj : ∀ μ ∈ M1 P C X, ∀ ν ∈ M1 P C X, supp μ = supp ν → μ = ν :=
    fun μ hμ ν hν hs => K1.eq_of_supp_eq hface htot hov hμ.1.1 hμ.1.2 hν.1.1 hs
  have hnm : ∀ x ∈ openOrthant n, ∀ μ ∈ M1 P C X,
      NullMeasurableSet (extinctEvent C X x μ) P := by
    intro x hx
    have hsol := hX.2.2 x (fun i => (hx i).le)
    exact K3.nullMeasurable_of_cover P C X x hsol.1 hsol.2.1 (M1 P C X) hinj (hcover x hx)
  exact Assemble.assemble P C X hfin hcover hnm
    (K2a.pos_of' P C B X hX h57t h59 hreach hFD)


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

/-- Theorem 1.3 from the remaining obligations, with the δ plumbing done (s13). -/
theorem top_main {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) (h15 : Assumption15 P C X) (hM1 : (M1 P C X).Nonempty)
    (H31 : ∀ δ₀, IsDelta0 C γb δ₀ →
      ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0))
    (hTV : Face.FaceTV P X) (hFD : K4.FDMarkov P X)
    (hreach : ∀ x ∈ openOrthant n, ∀ U : Set (SDEState n), IsOpen U → U.Nonempty →
      U ⊆ openOrthant n → ∃ t : ℝ≥0, 0 < P {ω | X x t ω ∈ U})
    (h57 : ∀ y ∈ orthant n, ∀ᵐ ω ∂P,
      IsTightMeasureSet {μ | ∃ t : ℝ, 1 ≤ t ∧ μ = occ X y t ω} ∧
        ∀ π ∈ limitSet X y ω, IsInvariant P X π)
    (h59 : ∀ μ ∈ M1 P C X, ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ Δ : ℝ, 0 < Δ ∧
      ∀ y ∈ Kbox μ k Δ, 1 - ε < (P (extinctEvent C X y μ)).toReal)
    (H54 : ∀ δ₀, IsDelta0 C γb δ₀ → ∀ δ' : ℝ, Assumption14 C δ' → δ' ≤ δ₀ →
      ∃ Khat : ℝ, 0 < Khat ∧ ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ' (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t))
    (H56 : ∀ δ₀, IsDelta0 C γb δ₀ → ∀ δ' : ℝ, Assumption14 C δ' → δ' ≤ δ₀ →
      ∀ x ∈ orthant n, ∀ ω : Ω, (∀ t, X x t ω ∈ orthant n) → ∀ Khat : ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ' (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t)) →
      ∀ (Ts : ℕ → ℝ) (π : Measure (SDEState n)), Tendsto Ts atTop atTop → IsInvariant P X π →
      (∀ h : SDEState n →ᵇ ℝ,
        Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π))) →
      ∀ (h : SDEState n → ℝ) (Kh δ : ℝ), ContinuousOn h (orthant n) → 0 < Kh → 0 ≤ δ →
        δ < δ' → (∀ y ∈ orthant n, |h y| < Kh * growthWeight C c δ y) →
        Integrable h π ∧
          Tendsto (fun k => ∫ y, h y ∂(occ X x (Ts k) ω)) atTop (𝓝 (∫ y, h y ∂π)))
    (H32 : ∀ δ₀, IsDelta0 C γb δ₀ → ∃ H₁ : ℝ, ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
        ∫⁻ ω, ENNReal.ofReal ((1 + ∑ i, c i * X x t ω i) ^ δ₀) ∂P ≤
          ENNReal.ofReal (H₁ + (1 + ∑ i, c i * x i) ^ δ₀ * Real.exp (-δ₀ * γb * t)))
    (hL : ∀ x ∈ openOrthant n, ∀ᵐ ω ∂P, ∀ i, Tendsto (fun m : ℕ =>
      Real.log (X x ((m ^ 2 : ℕ) : ℝ≥0) ω i) / ((m ^ 2 : ℕ) : ℝ)
      - ∫ y, (C.f i y - C.sig i i * C.g i y ^ 2 / 2) ∂(occ X x ((m ^ 2 : ℕ) : ℝ) ω))
        atTop (𝓝 0)) :
    ∀ x ∈ openOrthant n,
      (∑' μ : M1 P C X, P (extinctEvent C X x (μ : Measure (SDEState n)))) = 1 ∧
        ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ) := by
  have hγ : 0 < γb := hA.2.2.2.1
  obtain ⟨δ₀, hδ₀⟩ := exists_isDelta0 C γb hγ
  have hδ' : 0 < min δ₁ δ₀ := lt_min h14.1 hδ₀.1
  have h14' := a14_mono C h14 hδ' (min_le_left _ _)
  obtain ⟨H₁, h1⟩ := H32 δ₀ hδ₀
  exact top_core P C B X hX c γb hA h15 hM1 (H31 δ₀ hδ₀) hTV hFD hreach h57 h59 (min δ₁ δ₀) hδ'
    (H54 δ₀ hδ₀ _ h14' (min_le_right _ _)) (H56 δ₀ hδ₀ _ h14' (min_le_right _ _))
    (hmom_of P X c hA.2.2.1 γb δ₀ H₁ hγ hδ₀.1 h1) hL

end StochKolmogorov.Classify.Top

end Mod_Top

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

/-! Reduction glue (s15): Theorem 1.3 from `Top.top_main`, every hypothesis supplied by a child
theorem: Extinct.lemma_3_1 (cl. 2), Persist.kolmogorov_face_box_tv_overlap, the conditional
finite-dimensional Markov property (inside `FDM.fdMarkov_of`), interior_open_set_reachable,
lemmas 5.4, 5.6, 5.7, 5.9, Persist.lemma_3_2 (3.7) and log_lln_squares. -/

section RedGlue

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace StochKolmogorov.Classify.Red

open StochKolmogorov.Classify EthierKurtz

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
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) (h15 : Assumption15 P C X) (hM1 : (M1 P C X).Nonempty) :
    ∀ x ∈ openOrthant n,
      (∑' μ : M1 P C X, P (extinctEvent C X x (μ : Measure (SDEState n)))) = 1 ∧
        ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ) := by
  have hpd := hA.1
  have hC := hA.2.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  obtain ⟨δ₀, hδ₀⟩ := Top.exists_isDelta0 C γb hγ
  have hcl : ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0) :=
    (StochKolmogorov.Extinct.lemma_3_1 hn P ⟨C.f, C.g, C.Γ⟩ B X hX c γb hA _
      (delta_small C hδ₀)).2.1
  have H31 : ∀ δ₀, IsDelta0 C γb δ₀ →
      ∀ (I : Finset (Fin n)) (x : SDEState n), x ∈ orthant n → (∀ i, i ∈ I ↔ 0 < x i) →
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (∀ i ∈ I, 0 < X x t ω i) ∧ (∀ i, i ∉ I → X x t ω i = 0) :=
    fun _ _ => hcl
  have hfc : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hC i).1.continuousOn
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  have hδ' : 0 < min δ₁ δ₀ := lt_min h14.1 hδ₀.1
  have h14' := Top.a14_mono C h14 hδ' (min_le_left _ _)
  have H54 : ∀ δ₀, IsDelta0 C γb δ₀ → ∀ δ' : ℝ, Assumption14 C δ' → δ' ≤ δ₀ →
      ∃ Khat : ℝ, 0 < Khat ∧ ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℝ in atTop,
        ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (growthWeight C c δ' (X x s.toNNReal ω))
          ≤ ENNReal.ofReal ((Khat + ε) * t) :=
    fun δ₀ hδ₀ δ' h hle => (lemma_5_4 hn P C B X hX c γb hA δ₀ hδ₀ δ' h hle).1
  refine Top.top_main P C B X hX c γb hA δ₁ h14 h15 hM1 H31
    (fun I _ _ ha hab => StochKolmogorov.Persist.kolmogorov_face_box_tv_overlap P
      (Face.persistCoeffs C) B X (Face.persist_family hX) (Face.persist_hC hC)
      (Face.persist_hpd hpd) I ha hab)
    (FDM.fdMarkov_of P C B X hX hC (fun x hx s => by
      filter_upwards [stay_of P X hcl x hx] with ω hω using hω s))
    (interior_open_set_reachable P C B X hX hC hpd)
    (fun y hy => lemma_5_7 hn P C B X hX c γb hA δ₁ h14 y hy)
    (lemma_5_9 hn P C B X hX c γb hA δ₁ h14)
    H54
    (fun δ₀ hδ₀ δ' h hle => lemma_5_6 hn P C B X hX c γb hA δ₀ hδ₀ δ' h hle)
    (fun δ₀ hδ₀ => ?_) (fun x hx => ?_)
  · obtain ⟨H₁, H₂, -, -, h1, -, -⟩ := StochKolmogorov.Persist.lemma_3_2 hn P (Face.persistCoeffs C)
      B X (Face.persist_family hX) c γb hA δ₀ hδ₀
    exact ⟨H₁, h1⟩
  · have hxo : x ∈ orthant n := fun i => (hx i).le
    obtain ⟨K, hK0, hK⟩ := H54 δ₀ hδ₀ (min δ₁ δ₀) h14' (min_le_right _ _)
    exact HLglue.hL_of P C X c hc hfc hgc x (hX.2.2 x hxo).2.1 (stay_of P X hcl x hxo) hδ'.le
      ⟨K, hK0, hK x hxo⟩
      (log_lln_squares P C B X hX (fun i => ⟨hfc i, hgc i⟩) x hx (stay_open_of P X hcl x hx))

end StochKolmogorov.Classify.Red

end RedGlue

open MeasureTheory ProbabilityTheory Filter StochKolmogorov.Classify EthierKurtz in
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₁ : ℝ) (h14 : Assumption14 C δ₁) (h15 : Assumption15 P C X) (hM1 : (M1 P C X).Nonempty) :
    ∀ x ∈ openOrthant n,
      (∑' μ : M1 P C X, P (extinctEvent C X x (μ : Measure (SDEState n)))) = 1 ∧
        ∀ μ ∈ M1 P C X, 0 < P (extinctEvent C X x μ) := by
  exact StochKolmogorov.Classify.Red.main_thm hn P C B X hX c γb hA δ₁ h14 h15 hM1
