-- Prove2me | solution 1 for StochKolmogorov.Persist.kolmogorov_lyapunov_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T05:46:47.317357+00:00
-- url     : https://prove2.me/submissions/6cd5812f-5344-4301-8c8f-0a74df41ff96

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_StochKolmogorov_Persist_Persistence
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula
import Theorems.Thm_EthierKurtz_brownian_ito_integral_locality_and_continuity

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option linter.all false


-- ===== ItoM1 =====
section FlatM_ItoM1

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

end BM

section AEC
variable {mΩ : MeasurableSpace Ω}

end AEC

section CP
variable [MeasurableSpace Ω]

end CP

section M2

variable [MeasurableSpace Ω]

end M2

section M3
variable [MeasurableSpace Ω]

theorem completedBrownianPast_mono (P : Measure Ω) (W : ℝ≥0 → Ω → SDEState d)
    (ξ : Ω → SDEState d) {s t : ℝ≥0} (hst : s ≤ t) :
    completedBrownianPast P W ξ s ≤ completedBrownianPast P W ξ t := by
  unfold completedBrownianPast
  refine sup_le_sup_right (sup_le_sup_right ?_ _) _
  refine iSup_le fun r => ?_
  have hr : r.val ≤ t := r.2.trans hst
  exact le_iSup (fun q : Set.Iic t => MeasurableSpace.comap (W q.val) inferInstance) ⟨r.val, hr⟩

end M3

section M4
variable [MeasurableSpace Ω]

end M4


section StopCoef

end StopCoef

section M5
variable [MeasurableSpace Ω]

end M5


section M5b

theorem tendstoInMeasure_zero_of_abs_le [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {F A B : ι → Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (hA : TendstoInMeasure P A l (fun _ => 0)) (hB : TendstoInMeasure P B l (fun _ => 0))
    (hF : ∀ i ω, |F i ω| ≤ K * (|A i ω| + |B i ω|)) :
    TendstoInMeasure P F l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hA hB ⊢
  intro ε hε
  have hε' : 0 < ε / (2 * K) := by positivity
  have hsum := (hA _ hε').add (hB _ hε')
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => ?_)
  refine le_trans (measure_mono ?_) (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Set.mem_union, Real.dist_eq, sub_zero] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hF i ω
  have h2 : K * (|A i ω| + |B i ω|) < K * (ε / (2 * K) + ε / (2 * K)) :=
    mul_lt_mul_of_pos_left (add_lt_add hcon.1 hcon.2) hK
  have h3 : K * (ε / (2 * K) + ε / (2 * K)) = ε := by field_simp; ring
  linarith

theorem tendstoInMeasure_real_iff_sub [MeasurableSpace Ω] {ι : Type*} {l : Filter ι}
    {P : Measure Ω} {f : ι → Ω → ℝ} {g : Ω → ℝ} :
    TendstoInMeasure P f l g ↔ TendstoInMeasure P (fun i ω => f i ω - g ω) l (fun _ => 0) := by
  simp only [tendstoInMeasure_iff_dist, Real.dist_eq, sub_zero]

theorem itoStepValue_eq_sum_indicator (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (u : ℝ) (ω : Ω) :
    itoStepValue t n c u ω = ∑ k ∈ Finset.range (2 ^ n),
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
  unfold itoStepValue
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Set.indicator_apply, Set.mem_Ioc]

theorem intervalIntegrable_indicator_Ioc_const (T a b C : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun u => (Set.Ioc a b).indicator (fun _ => C) u) volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  exact (integrableOn_const (by simp)).indicator measurableSet_Ioc

theorem itoStepValue_intervalIntegrable (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    IntervalIntegrable (fun u => itoStepValue t n c u ω) volume 0 t.val := by
  have heq : (fun u => itoStepValue t n c u ω) = ∑ k ∈ Finset.range (2 ^ n), fun u =>
      (Set.Ioc ((k : ℝ) * t.val / (2 : ℝ) ^ n) (((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n)).indicator
        (fun _ => c k ω) u := by
    funext u; rw [Finset.sum_apply, itoStepValue_eq_sum_indicator]
  rw [heq]
  exact IntervalIntegrable.sum _ (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ t.2)

end M5b

section M5c
variable [MeasurableSpace Ω]

end M5c


section M6refine

end M6refine


section M6osc

/-- The dyadic time `j t / 2^N`. -/
noncomputable def dyTime (t : ℝ≥0) (N j : ℕ) : ℝ≥0 := (j : ℝ≥0) * t / (2 : ℝ≥0) ^ N

/-- Oscillation event: two dyadic times in `[0,t]` at distance at most `δ` at which `H` differs
by more than `η`. -/
def oscSet (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (δ η : ℝ) : Set Ω :=
  ⋃ p : (ℕ × ℕ) × (ℕ × ℕ), {ω | p.1.2 ≤ 2 ^ p.1.1 ∧ p.2.2 ≤ 2 ^ p.2.1 ∧
    |(dyTime t p.1.1 p.1.2 : ℝ) - dyTime t p.2.1 p.2.2| ≤ δ ∧
    η < |H (dyTime t p.1.1 p.1.2) ω - H (dyTime t p.2.1 p.2.2) ω|}

theorem dyTime_le (t : ℝ≥0) {N j : ℕ} (h : j ≤ 2 ^ N) : dyTime t N j ≤ t := by
  unfold dyTime
  rw [div_le_iff₀ (by positivity)]
  calc (j : ℝ≥0) * t ≤ (2 : ℝ≥0) ^ N * t :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h) zero_le
    _ = t * 2 ^ N := mul_comm _ _

theorem oscSet_mono (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) {δ δ' : ℝ} (hδ : δ ≤ δ') (η : ℝ) :
    oscSet H t δ η ⊆ oscSet H t δ' η := by
  intro ω hω
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hω
  exact Set.mem_iUnion.2 ⟨p, hp.1, hp.2.1, hp.2.2.1.trans hδ, hp.2.2.2⟩

theorem iInter_oscSet_eq_empty {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) = ∅ := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
  intro hall
  have huc : UniformContinuousOn (fun s => H s ω) (Set.Icc 0 t) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hHc ω).continuousOn
  obtain ⟨δ, hδ, hδuc⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨n, hn⟩ := exists_nat_gt ((t : ℝ) / δ)
  have h2n : (n : ℝ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  have htn : (t : ℝ) / 2 ^ n < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hn
    nlinarith
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  linarith

end M6osc


section M6cauchy
variable [MeasurableSpace Ω]

end M6cauchy


section M6limit
variable [MeasurableSpace Ω]

end M6limit


section M6trunc

/-- Every `u ∈ (0,t]` lies in a cell `(t_k, t_{k+1}]` of the dyadic grid, where the step process
takes the value `c k`. -/
theorem itoStepValue_eq_cell (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioc 0 t.val) (ω : Ω) :
    ∃ k : ℕ, k < 2 ^ n ∧ (k : ℝ) * t.val / 2 ^ n < u ∧ u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n ∧
      itoStepValue t n c u ω = c k ω := by
  have ht : (0 : ℝ) < t.val := lt_of_lt_of_le hu.1 hu.2
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hx0 : 0 < u * 2 ^ n / t.val := by have := hu.1; positivity
  have hxle : u * 2 ^ n / t.val ≤ 2 ^ n := by
    rw [div_le_iff₀ ht]
    have := mul_le_mul_of_nonneg_right hu.2 h2.le
    linarith only [this]
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith only [this, hkR]
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith only [hlt]
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith only [hge]
  refine ⟨k, hk2, hlo, hhi, ?_⟩
  unfold itoStepValue
  rw [Finset.sum_eq_single k]
  · rw [if_pos ⟨hlo, hhi⟩]
  · intro l _ hlk
    rw [if_neg]
    rintro ⟨h1, h1'⟩
    rcases lt_or_gt_of_ne hlk with hl | hl
    · have hl' : (l : ℝ) + 1 ≤ k := by exact_mod_cast hl
      have : ((l : ℝ) + 1) * t.val / 2 ^ n ≤ (k : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      exact absurd hlo (not_lt.2 (h1'.trans this))
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      exact absurd h1 (not_lt.2 (hhi.trans this))
  · intro hk'; exact absurd (Finset.mem_range.2 hk2) hk'

/-- Off the oscillation event of mesh `t/2^n`, `H` at the left grid point `t_k` is within `η` of
`H u` for every `u ∈ [t_k, t_{k+1}]` (dyadic approximation of `u` from the left + continuity). -/
theorem abs_H_sub_le_of_not_mem_oscSet {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (n k : ℕ) {η : ℝ} (hη : 0 ≤ η) {ω : Ω}
    (hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η) (hk : k < 2 ^ n) {u : ℝ} (hu0 : 0 ≤ u)
    (hlo : (k : ℝ) * t.val / 2 ^ n ≤ u) (hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n)
    (hut : u ≤ t.val) :
    |H (dyTime t n k) ω - H u.toNNReal ω| ≤ η := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rcases ht.eq_or_lt with h0 | hpos
  · have hu : u = 0 := le_antisymm (h0 ▸ hut) hu0
    have hd : dyTime t n k = 0 := by
      have : t = 0 := NNReal.coe_eq_zero.1 h0.symm
      simp [dyTime, this]
    rw [hu, hd, Real.toNNReal_zero, sub_self, abs_zero]
    exact hη
  set y : ℕ → ℝ := fun m => u * 2 ^ (m + n) / t.val with hy
  set s : ℕ → ℝ≥0 := fun m => dyTime t (m + n) ⌊y m⌋₊ with hs
  have hsR : ∀ m, (s m : ℝ) = (⌊y m⌋₊ : ℝ) * t.val / 2 ^ (m + n) := fun m => by
    simp [hs, dyTime]
  have hy0 : ∀ m, 0 ≤ y m := fun m => by simp only [hy]; positivity
  have hyt : ∀ m, y m * t.val / 2 ^ (m + n) = u := fun m => by
    simp only [hy]; field_simp
  have hs_le : ∀ m, (s m : ℝ) ≤ u := fun m => by
    rw [hsR, ← hyt m]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (Nat.floor_le (hy0 m)) ht)
      (by positivity)
  have hs_gt : ∀ m, u - t.val / 2 ^ (m + n) ≤ (s m : ℝ) := fun m => by
    have h1 := Nat.lt_floor_add_one (y m)
    have h3 : u - t.val / 2 ^ (m + n) = (y m - 1) * t.val / 2 ^ (m + n) := by
      rw [← hyt m]; field_simp; try ring
    rw [hsR, h3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [h1]) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      have hm2 := mul_le_mul_of_nonneg_left hlo (pow_pos (two_pos (α := ℝ)) m).le
      linarith only [hm2]
    have hfl : ((k * 2 ^ m : ℕ) : ℝ) ≤ (⌊y m⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor hkm
    have e : (dyTime t n k : ℝ) = ((k * 2 ^ m : ℕ) : ℝ) * t.val / 2 ^ (m + n) := by
      simp only [dyTime]; push_cast; rw [pow_add]; field_simp; try rfl
    rw [e, hsR]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfl ht) (by positivity)
  have hdk : (dyTime t n k : ℝ) = (k : ℝ) * t.val / 2 ^ n := by simp [dyTime]
  have hbound : ∀ m, |H (dyTime t n k) ω - H (s m) ω| ≤ η := fun m => by
    by_contra hc
    refine hω (Set.mem_iUnion.2 ⟨((n, k), (m + n, ⌊y m⌋₊)), hk.le, ?_, ?_, lt_of_not_ge hc⟩)
    · refine Nat.floor_le_of_le ?_
      simp only [hy]
      rw [div_le_iff₀ hpos]; push_cast
      exact (mul_le_mul_of_nonneg_right hut (by positivity)).trans_eq (mul_comm _ _)
    · show |(dyTime t n k : ℝ) - (s m : ℝ)| ≤ (t : ℝ) / 2 ^ n
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (hs_ge m))]
      have e1 : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by ring
      have e2 := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith only [e1, e2, hhi]
  have hreal : Tendsto (fun m => (s m : ℝ)) atTop (𝓝 u) := by
    have hpow : Tendsto (fun m : ℕ => t.val / 2 ^ (m + n)) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ))).comp
        (tendsto_add_atTop_nat n)
      exact Tendsto.div_atTop tendsto_const_nhds h
    have hlow : Tendsto (fun m : ℕ => u - t.val / 2 ^ (m + n)) atTop (𝓝 u) := by
      simpa using (tendsto_const_nhds (x := u)).sub hpow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hs_gt hs_le
  have hnn : Tendsto s atTop (𝓝 u.toNNReal) := by
    have := (continuous_real_toNNReal.tendsto u).comp hreal
    simpa [Function.comp_def] using this
  have hcont : Continuous fun x : ℝ≥0 => |H (dyTime t n k) ω - H x ω| :=
    (continuous_const.sub (hHc ω)).abs
  exact le_of_tendsto' ((hcont.tendsto u.toNNReal).comp hnn) (fun m => hbound m)

end M6trunc

section M6exist
variable [MeasurableSpace Ω]

/-- M6: every continuous process adapted to the completed Brownian past has an Ito integral
against each Brownian coordinate. -/
theorem exists_hasBrownianItoIntegral {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).1 j H hHm hHc
end M6exist


section M7grid

end M7grid

section M7zero
variable [MeasurableSpace Ω]

end M7zero


section M7qv
variable [MeasurableSpace Ω]

end M7qv

section M7c
variable [MeasurableSpace Ω]

end M7c

section M8a
variable [MeasurableSpace Ω]

theorem tendstoInMeasure_mul_left_real {ι : Type*} {l : Filter ι} {P : Measure Ω}
    {f : ι → Ω → ℝ} {g : Ω → ℝ} (a : Ω → ℝ) {R : ℝ} (hR : 0 < R) (ha : ∀ ω, |a ω| ≤ R)
    (hf : TendstoInMeasure P f l g) :
    TendstoInMeasure P (fun i ω => a ω * f i ω) l (fun ω => a ω * g ω) := by
  rw [tendstoInMeasure_real_iff_sub] at hf ⊢
  refine tendstoInMeasure_zero_of_abs_le hR hf hf fun i ω => ?_
  rw [← mul_sub, abs_mul]
  nlinarith [ha ω, abs_nonneg (f i ω - g ω), abs_nonneg (a ω)]

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

/-- Locality of the Ito integral: integrands agreeing on the dyadic grid of `[0, s]` on an event
give integrals agreeing a.e. on that event at time `s`. -/
theorem hasBrownianItoIntegral_eq_on {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H H' J J' : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hH'm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s))
    (hH'c : ∀ ω, Continuous fun s => H' s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H' J') (s : ℝ≥0) (E : Set Ω)
    (hE : ∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N → H (dyTime s N i) ω = H' (dyTime s N i) ω) :
    ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).1 j H H' J J' hHm hHc hH'm hH'c hJ hJ' s E hE
end M8c

section M8d
variable [MeasurableSpace Ω]

end M8d

section M8e
variable [MeasurableSpace Ω]

end M8e


section M8f
variable [MeasurableSpace Ω]

end M8f


section M8f2
variable [MeasurableSpace Ω]

theorem itoStepValue_integral (t : ℝ≥0) (n : ℕ) (c : ℕ → Ω → ℝ) (ω : Ω) :
    ∫ u in (0 : ℝ)..t.val, itoStepValue t n c u ω =
      (∑ k ∈ Finset.range (2 ^ n), c k ω) * ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
  have hT : (0 : ℝ) ≤ t.val := t.2
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  simp_rw [itoStepValue_eq_sum_indicator]
  rw [intervalIntegral.integral_finsetSum
    (fun k _ => intervalIntegrable_indicator_Ioc_const _ _ _ _ hT), Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 := Finset.mem_range.1 hk
  have hk' : (k : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.succ_le_of_lt hk0
  have ha : 0 ≤ (k : ℝ) * t.val / (2 : ℝ) ^ n :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg k) hT) h2.le
  have hab : (k : ℝ) * t.val / (2 : ℝ) ^ n ≤ ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith
  rw [intervalIntegral.integral_of_le hT, integral_indicator_const _ measurableSet_Ioc,
    measureReal_restrict_apply measurableSet_Ioc,
    Set.inter_eq_left.2 (Set.Ioc_subset_Ioc ha hbT), Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  simp only [NNReal.val_eq_coe, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat]
  field_simp
  ring

/-- M8f: left-point Riemann sums of a pathwise continuous process converge pathwise. -/
theorem riemann_tendsto {H : ℝ≥0 → Ω → ℝ} (hHc : ∀ ω, Continuous fun s => H s ω)
    (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) atTop (𝓝 (∫ u in (0 : ℝ)..t.val, H u.toNNReal ω)) := by
  have ht : (0 : ℝ) ≤ t.val := t.2
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * (t.val + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hempty := iInter_oscSet_eq_empty hHc t hη
  have hex : ∃ n0 : ℕ, ω ∉ oscSet H t ((t : ℝ) / 2 ^ n0) η := by
    by_contra h
    push_neg at h
    have hmem : ω ∈ (⋂ n : ℕ, oscSet H t ((t : ℝ) / 2 ^ n) η) := Set.mem_iInter.2 h
    rw [hempty] at hmem
    exact hmem
  obtain ⟨n0, hn0⟩ := hex
  refine ⟨n0, fun n hn => ?_⟩
  have hω : ω ∉ oscSet H t ((t : ℝ) / 2 ^ n) η := fun h => hn0 (oscSet_mono H t
    (div_le_div_of_nonneg_left (NNReal.coe_nonneg t) (by positivity)
      (pow_le_pow_right₀ one_le_two hn)) η h)
  have hI := itoStepValue_integral t n (fun k ω => H (dyTime t n k) ω) ω
  have hHi : IntervalIntegrable (fun u : ℝ => H u.toNNReal ω) volume 0 t.val :=
    ((hHc ω).comp continuous_real_toNNReal).intervalIntegrable _ _
  rw [Real.dist_eq, ← hI, ← intervalIntegral.integral_sub
    (itoStepValue_intervalIntegrable _ _ _ _) hHi]
  have hb : ∀ u ∈ Set.uIoc (0 : ℝ) t.val,
      ‖itoStepValue t n (fun k ω => H (dyTime t n k) ω) u ω - H u.toNNReal ω‖ ≤ η := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    obtain ⟨k, hk, hlo, hhi, hval⟩ :=
      itoStepValue_eq_cell t n (fun k ω => H (dyTime t n k) ω) hu ω
    rw [hval, Real.norm_eq_abs]
    exact abs_H_sub_le_of_not_mem_oscSet hHc t n k hη.le hω hk hu.1.le hlo.le hhi hu.2
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg ht, Real.norm_eq_abs] at hle
  refine lt_of_le_of_lt hle ?_
  rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  linarith only [hε, mul_nonneg hε.le ht]

end M8f2


section M8f3
variable [MeasurableSpace Ω]

end M8f3


section M8gTaylor
open Set

end M8gTaylor

section M8g
variable [MeasurableSpace Ω]

end M8g


section M8g2

end M8g2


section M8g3
variable [MeasurableSpace Ω]

end M8g3

section M8g4
variable [MeasurableSpace Ω]

/-- Coordinates of a linear functional on `SDEState d`. -/
theorem clm_coord (L : SDEState d →L[ℝ] ℝ) (v : SDEState d) :
    L v = ∑ i, v i * L (EuclideanSpace.single i 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]

theorem clm2_coord (B : SDEState d →L[ℝ] SDEState d →L[ℝ] ℝ) (v w : SDEState d) :
    B v w = ∑ i, ∑ i', v i * w i' *
      B (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) := by
  rw [clm_coord (B v) w]
  have h : ∀ i', B v (EuclideanSpace.single i' 1) =
      ∑ i, v i * B (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) := fun i' =>
    clm_coord (B.flip (EuclideanSpace.single i' 1)) v
  simp only [h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

end M8g4

section M8g5
variable [MeasurableSpace Ω]

/-- M8g5: **Ito's formula** for a `C²` function of a `d`-dimensional Ito process
`X^i = X^i_0 + Σ_j ∫ H^{ij} dW^j + ∫ b^i du` (continuous adapted coefficients). -/
theorem ito_formula {P : Measure Ω} [IsFiniteMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) {e : ℕ} {X : ℝ≥0 → Ω → SDEState e}
    (hXm : ∀ s, Measurable (X s)) (hXc : ∀ ω, Continuous fun s => X s ω)
    (hXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (X s))
    {H J : Fin e → Fin d → ℝ≥0 → Ω → ℝ} {b : Fin e → ℝ≥0 → Ω → ℝ}
    (hHm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H i j s))
    (hHc : ∀ i j ω, Continuous fun s => H i j s ω)
    (hJ : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (H i j) (J i j))
    (hbm : ∀ i s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (b i s))
    (hbc : ∀ i ω, Continuous fun s => b i s ω)
    (hX : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (i : Fin e), X s ω i = X 0 ω i + (∑ j, J i j s ω) +
      ∫ u in (0 : ℝ)..s.val, b i u.toNNReal ω)
    {f : SDEState e → ℝ} (hf : ContDiff ℝ 2 f) {K : Fin e → Fin d → ℝ≥0 → Ω → ℝ}
    (hK : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j)
      (fun s ω => fderiv ℝ f (X s ω) (EuclideanSpace.single i 1) * H i j s ω) (K i j))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂P, f (X t ω) = f (X 0 ω) + (∑ i, ∑ j, K i j t ω) +
      (∑ i, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ f (X u.toNNReal ω) (EuclideanSpace.single i 1) * b i u.toNNReal ω) +
      (1 / 2) * ∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ f) (X u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H i j u.toNNReal ω * H i' j u.toNNReal ω := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).2.2 e X hXm hXc hXa H J b hHm hHc hJ hbm hbc hX f hf K hK t
end M8g5

section M9a
variable [MeasurableSpace Ω]

/-- M9a: the Ito integral of a bounded continuous adapted integrand is square integrable,
with `E[J_t²] ≤ C² t` and mean zero. -/
theorem ito_integral_memLp_meanZero {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H J : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ} (hC : ∀ s ω, |H s ω| ≤ C)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J) (t : ℝ≥0) :
    MemLp (J t) 2 P ∧ ∫ ω, J t ω ^ 2 ∂P ≤ C ^ 2 * t ∧ ∫ ω, J t ω ∂P = 0 := by
  exact (EthierKurtz.brownian_ito_integral_and_formula hW x₀).2.1 j H J hHm hHc C hC hJ t
end M9a


section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem line_hasDerivAt {f : E → ℝ} (hf : Differentiable ℝ f) (u v : E) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (u + r • v)) (fderiv ℝ f (u + s • v) v) s := by
  have h := (hf (u + s • v)).hasFDerivAt.comp_hasDerivAt s
    (((hasDerivAt_id s).smul_const v).const_add u)
  simpa [Function.comp_def] using h

theorem line_hasDerivAt2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u v : E) :
    HasDerivAt (fun r : ℝ => fderiv ℝ f (u + r • v) v) (fderiv ℝ (fderiv ℝ f) u v v) 0 := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hc : ∀ w, HasFDerivAt (fun w => fderiv ℝ f w v) ((fderiv ℝ (fderiv ℝ f) w).flip v) w :=
    fun w => by simpa using (hd w).hasFDerivAt.clm_apply (hasFDerivAt_const v w)
  have h := (hc (u + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ)
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u)
  simpa [Function.comp_def] using h

/-- First directional derivative from an explicit line derivative. -/
theorem fderiv_eq_of_line {f : E → ℝ} (hf : Differentiable ℝ f) (u v : E) {c : ℝ}
    (h1 : HasDerivAt (fun r : ℝ => f (u + r • v)) c 0) : fderiv ℝ f u v = c := by
  have h := line_hasDerivAt hf u v 0
  simp only [zero_smul, add_zero] at h
  exact h.unique h1

/-- Second directional derivative `D²f(u)(v,v)` from explicit line derivatives. -/
theorem fderiv2_eq_of_line {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u v : E) {φ' : ℝ → ℝ} {c : ℝ}
    (h1 : ∀ s, HasDerivAt (fun r : ℝ => f (u + r • v)) (φ' s) s) (h2 : HasDerivAt φ' c 0) :
    fderiv ℝ (fderiv ℝ f) u v v = c := by
  have hdf : Differentiable ℝ f := hf.differentiable two_ne_zero
  have e : (fun r : ℝ => fderiv ℝ f (u + r • v) v) = φ' :=
    funext fun s => (line_hasDerivAt hdf u v s).unique (h1 s)
  have h := line_hasDerivAt2 hf u v
  rw [e] at h
  exact h.unique h2

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

def ixc (k : Fin d) : Fin (d + d + 1) := Fin.castSucc (Fin.castAdd d k)
def iyc (k : Fin d) : Fin (d + d + 1) := Fin.castSucc (Fin.natAdd d k)
def iac : Fin (d + d + 1) := Fin.last _

theorem coord_contDiff {e : ℕ} (i : Fin e) {n : ℕ∞} :
    ContDiff ℝ n (fun u : SDEState e => u i) :=
  (EuclideanSpace.proj i : SDEState e →L[ℝ] ℝ).contDiff

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

/-- `(x, y, a) ↦ u` with `u (ixc k) = x k`, `u (iyc k) = y k`, `u iac = a`. -/
noncomputable def pack (x y : SDEState d) (a : ℝ) : SDEState (d + d + 1) :=
  WithLp.toLp 2 (fun i => Fin.lastCases a (fun j => Fin.addCases (fun k => x k) (fun k => y k) j) i)

@[simp] theorem pack_ixc (x y : SDEState d) (a : ℝ) (k : Fin d) : pack x y a (ixc k) = x k := by
  simp [pack, ixc]

@[simp] theorem pack_iyc (x y : SDEState d) (a : ℝ) (k : Fin d) : pack x y a (iyc k) = y k := by
  show Fin.lastCases a (fun j => Fin.addCases (fun k => x k) (fun k => y k) j)
    (Fin.castSucc (Fin.natAdd d k)) = y k
  rw [Fin.lastCases_castSucc, Fin.addCases_right]

@[simp] theorem pack_iac (x y : SDEState d) (a : ℝ) : pack x y a iac = a := by
  simp [pack, iac]

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

/-- Column `j` of a diffusion matrix. -/
noncomputable def scol (s : SDEDiffusion d) (j : Fin d) : SDEState d :=
  WithLp.toLp 2 (fun k => s (k, j))

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

theorem pack_continuous {α : Type*} [TopologicalSpace α] {f g : α → SDEState d} {h : α → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous fun p => pack (f p) (g p) (h p) := by
  unfold pack
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  induction i using Fin.lastCases with
  | last => simp only [Fin.lastCases_last]; exact hh
  | cast j =>
    induction j using Fin.addCases with
    | left k =>
      simp only [Fin.lastCases_castSucc, Fin.addCases_left]
      exact (continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp hf)
    | right k =>
      simp only [Fin.lastCases_castSucc, Fin.addCases_right]
      exact (continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp hg)

theorem scol_continuous {α : Type*} [TopologicalSpace α] {s : α → SDEDiffusion d}
    (hs : Continuous s) (j : Fin d) : Continuous fun p => scol (s p) j := by
  unfold scol
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k =>
    (continuous_apply (k, j)).comp ((PiLp.continuous_ofLp 2 _).comp hs))

end M9d2



section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

theorem hasBrownianItoIntegral_zero [MeasurableSpace Ω] (P : Measure Ω)
    (ℱ : ℝ≥0 → MeasurableSpace Ω) (W : ℝ≥0 → Ω → ℝ) :
    HasBrownianItoIntegral P ℱ W (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨fun t ω => by simp, fun t => ⟨fun _ _ _ => 0, fun _ _ _ => measurable_const,
    fun _ => ⟨0, fun _ _ _ => by simp⟩, ?_, ?_⟩⟩
  · convert (show TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop fun _ => 0 from
      fun ε hε => by simp [hε.ne']) using 1
    funext n ω
    have hz : ∀ u, itoStepValue t n (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) u ω = 0 := fun u =>
      Finset.sum_eq_zero fun k _ => ite_self _
    simp [hz]
  · convert (show TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop fun _ => 0 from
      fun ε hε => by simp [hε.ne']) using 1
    funext n ω; simp [itoStepSum]

theorem measurable_intervalIntegral_of_continuous [MeasurableSpace Ω] (m : MeasurableSpace Ω)
    {H : ℝ≥0 → Ω → ℝ} (t : ℝ≥0) (hHm : ∀ s, s ≤ t → Measurable[m] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω) :
    Measurable[m] (fun ω => ∫ u in (0 : ℝ)..t.val, H u.toNNReal ω) := by
  refine measurable_of_tendsto_metrizable (f := fun n ω => (∑ k ∈ Finset.range (2 ^ n), H (dyTime t n k) ω) *
      ((t / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)) (fun n => ?_)
    (tendsto_pi_nhds.2 fun ω => riemann_tendsto hHc t ω)
  refine Measurable.mul_const ?_ _
  exact Finset.measurable_sum _ fun k hk =>
    hHm _ (dyTime_le t (Finset.mem_range.1 hk).le)

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2


end ItoLib

end FlatM_ItoM1
-- ===== E =====
section FlatM_E
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10b1
/-! M10b-1: pathwise identification of Ito integrals. For an integrand that is an indefinite
integral in time (`h s = h 0 + ∫₀ˢ D`), left-point sums converge pathwise to the integration by
parts value `h t w t - h 0 w 0 - ∫₀ᵗ w D`; and pathwise limits of left-point sums are Ito
integrals in the sense of `HasBrownianItoIntegral`. -/

end M10b1

section M10b2
/-! M10b-2 (generic part): piecewise-linear interpolation of a sequence on the grid `k h`,
defined as a primitive of the piecewise-constant slope. -/

end M10b2

section M10b2s
/-! M10b-2: the truncated Euler scheme with lagged, linearly interpolated coefficients, driven by a
deterministic path `w`. `eulerZZ k = (Z_{k-1}, Z_k)`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)
  (w : ℝ≥0 → SDEState d)

variable {s₁ b₁ h w}

end M10b2s


section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2w


section M10b2i
/-! M10b-2: the scheme driven by standard Brownian motion is an Ito process in the sense of
`ito_formula`. -/

variable [MeasurableSpace Ω] {W : ℝ≥0 → Ω → SDEState d}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10b2i


section M10b4a
/-! M10b-4 (a): Ito formula for `Ff r` along `(X, Y, A)` where `X`, `Y` are general Ito
processes (matrix integrands `HX`, `HY`, drifts `bX`, `bY`), `A = ∫ κ(X, Y)`. -/

end M10b4a


section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

/-- Expectation bound from an Ito decomposition `F = c + Z + D` with `E Z = 0`, `F ≥ 0`. -/
theorem lintegral_le_of_ito [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F Z D E : Ω → ℝ} {c β : ℝ} (hF0 : ∀ᵐ ω ∂P, 0 ≤ F ω) (hZi : Integrable Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (hEq : ∀ᵐ ω ∂P, F ω = c + Z ω + D ω)
    (hD : ∀ᵐ ω ∂P, D ω ≤ β + E ω) (hE : Integrable E P) :
    ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≤ ENNReal.ofReal (c + β + ∫ ω, E ω ∂P) := by
  have hle : ∀ᵐ ω ∂P, F ω ≤ Z ω + (c + β) + E ω := by
    filter_upwards [hEq, hD] with ω h1 h2
    rw [h1]; linarith
  have hi : Integrable (fun ω => Z ω + (c + β) + E ω) P :=
    (hZi.add (integrable_const _)).add hE
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Z ω + (c + β) + E ω) ∂P :=
        lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal (∫ ω, (Z ω + (c + β) + E ω) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (by filter_upwards [hle, hF0] with ω h h0 using h0.trans h)).symm
    _ = ENNReal.ofReal (c + β + ∫ ω, E ω ∂P) := by
        have e1 : ∫ ω, (Z ω + (c + β) + E ω) ∂P = ∫ ω, (Z ω + (c + β)) ∂P + ∫ ω, E ω ∂P :=
          integral_add (hZi.add (integrable_const _)) hE
        have e2 : ∫ ω, (Z ω + (c + β)) ∂P = ∫ ω, Z ω ∂P + ∫ _ω, (c + β) ∂P :=
          integral_add hZi (integrable_const _)
        rw [e1, e2, hZ0, integral_const]
        simp

end M10b4b

end ItoLib

end FlatM_E
-- ===== F =====
section FlatM_F
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c1
/-! M10c-1: the saturating profile `ψ(Q) = 1 - (1 - st(Q/4)) e^{-Q}` (`ψ(0) = 0`, `ψ = 1` for
`Q ≥ 4`, `ψ(Q) ≥ Q/5` on `[0,4]`) and the test function
`Gf r (x, y, a) = e^{-a} χ_r(|x|²) ψ(|x-y|²)` (cut-off in `x` only). -/

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

end M10c3

end ItoLib

end FlatM_F
-- ===== G =====
section FlatM_G
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c4
/-! M10c-4: the Ito formula along `(X, Y, A)` for an arbitrary `C²` test function `F` whose
martingale integrands are bounded (`ito_coupled_F`); applied to `Gf r`. -/

/-- Generator of a `C²` function `F` along `(X, Y, A)` with coefficient values `σx, bx` for `X`
and `σy, by'` for `Y`. -/
noncomputable def driftGen (F : SDEState (d + d + 1) → ℝ) (κ : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) : ℝ :=
  fderiv ℝ F (pack x y a) (pack bx by' κ) +
    (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ F) (pack x y a)
      (pack (scol σx j) (scol σy j) 0) (pack (scol σx j) (scol σy j) 0)

theorem driftGen_coords (F : SDEState (d + d + 1) → ℝ) (κ : ℝ) (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) :
    (∑ i, fderiv ℝ F (pack x y a) (EuclideanSpace.single i 1) * pack bx by' κ i) +
      (1 / 2) * ∑ i, ∑ i', ∑ j, fderiv ℝ (fderiv ℝ F) (pack x y a)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) *
          pack (scol σx j) (scol σy j) 0 i * pack (scol σx j) (scol σy j) 0 i'
      = driftGen F κ σx bx σy by' x y a := by
  unfold driftGen
  rw [clm_coord (fderiv ℝ F (pack x y a)) (pack bx by' κ)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · congr 1
    rw [Finset.sum_congr rfl fun j _ => clm2_coord (fderiv ℝ (fderiv ℝ F) (pack x y a))
      (pack (scol σx j) (scol σy j) 0) (pack (scol σx j) (scol σy j) 0)]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    ring

set_option maxHeartbeats 1000000 in
/-- Ito formula for a `C²` function `F` along `(X, Y, A)` for general Ito processes `X`, `Y`. -/
theorem ito_coupled_F [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {X Y : ℝ≥0 → Ω → SDEState d} {HX HY JX JY : ℝ≥0 → Ω → SDEDiffusion d}
    {bX bY : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hYm : ∀ s, Measurable (Y s))
    (hXc : ∀ ω, Continuous fun s => X s ω) (hYc : ∀ ω, Continuous fun s => Y s ω)
    (hXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (X s))
    (hYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (Y s))
    (hHXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HX s))
    (hHYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HY s))
    (hHXc : ∀ ω, Continuous fun s => HX s ω) (hHYc : ∀ ω, Continuous fun s => HY s ω)
    (hbXa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bX s))
    (hbYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bY s))
    (hbXc : ∀ ω, Continuous fun s => bX s ω) (hbYc : ∀ ω, Continuous fun s => bY s ω)
    (hJX : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => HX s ω (i, j)) (fun s ω => JX s ω (i, j)))
    (hJY : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (fun s ω => HY s ω (i, j)) (fun s ω => JY s ω (i, j)))
    (hXeq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, X s ω i = X 0 ω i + (∑ j, JX s ω (i, j)) +
      ∫ u in (0 : ℝ)..s.val, bX u.toNNReal ω i)
    (hYeq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) i, Y s ω i = Y 0 ω i + (∑ j, JY s ω (i, j)) +
      ∫ u in (0 : ℝ)..s.val, bY u.toNNReal ω i)
    {x0 y0 : SDEState d} (hX0 : ∀ᵐ ω ∂P, X 0 ω = x0) (hY0 : ∀ᵐ ω ∂P, Y 0 ω = y0)
    {κ : SDEState d → SDEState d → ℝ}
    (hκ : Continuous fun p : SDEState d × SDEState d => κ p.1 p.2)
    (hκ0 : ∀ x y, 0 ≤ κ x y) {F : SDEState (d + d + 1) → ℝ} (hF : ContDiff ℝ 2 F)
    (hFb : ∀ i j, ∃ C, ∀ s ω (a : ℝ), 0 ≤ a →
      |fderiv ℝ F (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1) *
        pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i| ≤ C)
    (t : ℝ≥0) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧ ∫ ω, Z ω ∂P = 0 ∧
      ∀ᵐ ω ∂P, F (pack (X t ω) (Y t ω)
          (∫ u in (0 : ℝ)..t.val, κ (X u.toNNReal ω) (Y u.toNNReal ω))) =
        F (pack x0 y0 0) + Z ω + ∫ u in (0 : ℝ)..t.val,
          driftGen F (κ (X u.toNNReal ω) (Y u.toNNReal ω)) (HX u.toNNReal ω) (bX u.toNNReal ω)
            (HY u.toNNReal ω) (bY u.toNNReal ω) (X u.toNNReal ω) (Y u.toNNReal ω)
            (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), κ (X v.toNNReal ω) (Y v.toNNReal ω)) := by
  have hXYc : ∀ ω, Continuous fun s => (X s ω, Y s ω) := fun ω => (hXc ω).prodMk (hYc ω)
  have hXYa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      fun ω => (X s ω, Y s ω) := fun s => (hXa s).prodMk (hYa s)
  have hXYm : ∀ s, Measurable fun ω => (X s ω, Y s ω) := fun s => (hXm s).prodMk (hYm s)
  have hκc : ∀ ω, Continuous fun s => κ (X s ω) (Y s ω) := fun ω => hκ.comp (hXYc ω)
  -- the clock `A`
  let A : ℝ≥0 → Ω → ℝ := fun s ω => ∫ u in (0 : ℝ)..s.val, κ (X u.toNNReal ω) (Y u.toNNReal ω)
  have hAa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (A s) := fun s =>
    measurable_intervalIntegral_of_continuous _ s
      (fun u hu => hκ.measurable.comp ((hXYa u).mono (completedBrownianPast_mono P W _ hu) le_rfl))
      hκc
  have hAm : ∀ s, Measurable (A s) := fun s =>
    measurable_intervalIntegral_of_continuous _ s (fun u _ => hκ.measurable.comp (hXYm u)) hκc
  have hA0 : ∀ s ω, 0 ≤ A s ω := fun s ω =>
    intervalIntegral.integral_nonneg s.2 fun u _ => hκ0 _ _
  have hAc : ∀ ω, Continuous fun s => A s ω := fun ω => by
    have hgc : Continuous fun u : ℝ => κ (X u.toNNReal ω) (Y u.toNNReal ω) :=
      (hκc ω).comp continuous_real_toNNReal
    have hp : Continuous fun b : ℝ => ∫ u in (0 : ℝ)..b, κ (X u.toNNReal ω) (Y u.toNNReal ω) :=
      continuous_iff_continuousAt.2 fun b =>
        (hgc.integral_hasStrictDerivAt 0 b).hasDerivAt.continuousAt
    exact hp.comp NNReal.continuous_coe
  -- the coupled process `U`
  let U : ℝ≥0 → Ω → SDEState (d + d + 1) := fun s ω => pack (X s ω) (Y s ω) (A s ω)
  have hpk : Continuous fun q : SDEState d × SDEState d × ℝ => pack q.1 q.2.1 q.2.2 :=
    pack_continuous continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)
  have hUm : ∀ s, Measurable (U s) := fun s =>
    (hpk.measurable.comp ((hXm s).prodMk ((hYm s).prodMk (hAm s))) :)
  have hUa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (U s) := fun s =>
    (hpk.measurable.comp ((hXa s).prodMk ((hYa s).prodMk (hAa s))) :)
  have hUc : ∀ ω, Continuous fun s => U s ω := fun ω =>
    hpk.comp ((hXc ω).prodMk ((hYc ω).prodMk (hAc ω)))
  have hcol : ∀ (i : Fin (d + d + 1)) (j : Fin d),
      Continuous fun p : SDEDiffusion d × SDEDiffusion d =>
        pack (scol p.1 j) (scol p.2 j) 0 i := fun i j =>
    ((coord_contDiff i (n := 0)).continuous).comp
      (pack_continuous (scol_continuous continuous_fst j)
        (scol_continuous continuous_snd j) continuous_const)
  have hbf : ∀ i : Fin (d + d + 1), Continuous fun q : SDEState d × SDEState d × ℝ =>
      pack q.1 q.2.1 q.2.2 i := fun i =>
    ((coord_contDiff i (n := 0)).continuous).comp hpk
  have hHH : ∀ ω, Continuous fun s => (HX s ω, HY s ω) := fun ω => (hHXc ω).prodMk (hHYc ω)
  have hHHa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      fun ω => (HX s ω, HY s ω) := fun s => (hHXa s).prodMk (hHYa s)
  have hBB : ∀ ω, Continuous fun s => (bX s ω, bY s ω, κ (X s ω) (Y s ω)) := fun ω =>
    (hbXc ω).prodMk ((hbYc ω).prodMk (hκc ω))
  have hBBa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      fun ω => (bX s ω, bY s ω, κ (X s ω) (Y s ω)) := fun s =>
    (hbXa s).prodMk ((hbYa s).prodMk (hκ.measurable.comp (hXYa s)))
  let HU : Fin (d + d + 1) → Fin d → ℝ≥0 → Ω → ℝ := fun i j s ω =>
    pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i
  let JU : Fin (d + d + 1) → Fin d → ℝ≥0 → Ω → ℝ := fun i j s ω =>
    pack (WithLp.toLp 2 fun k => JX s ω (k, j)) (WithLp.toLp 2 fun k => JY s ω (k, j)) 0 i
  let bU : Fin (d + d + 1) → ℝ≥0 → Ω → ℝ := fun i s ω =>
    pack (bX s ω) (bY s ω) (κ (X s ω) (Y s ω)) i
  have hHm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HU i j s) :=
    fun i j s => ((hcol i j).measurable.comp (hHHa s) :)
  have hHc : ∀ i j ω, Continuous fun s => HU i j s ω := fun i j ω => (hcol i j).comp (hHH ω)
  have hbm : ∀ i s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bU i s) :=
    fun i s => ((hbf i).measurable.comp (hBBa s) :)
  have hbc : ∀ i ω, Continuous fun s => bU i s ω := fun i ω => (hbf i).comp (hBB ω)
  have hJ : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) (HU i j) (JU i j) := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      have e1 : HU (Fin.last _) j = fun _ _ => 0 := by
        funext s ω; exact pack_iac _ _ _
      have e2 : JU (Fin.last _) j = fun _ _ => 0 := by
        funext s ω; exact pack_iac _ _ _
      rw [e1, e2]; exact hasBrownianItoIntegral_zero _ _ _
    | cast i' =>
      induction i' using Fin.addCases with
      | left k =>
        have e1 : HU (Fin.castSucc (Fin.castAdd d k)) j = fun s ω => HX s ω (k, j) := by
          funext s ω; exact pack_ixc _ _ _ k
        have e2 : JU (Fin.castSucc (Fin.castAdd d k)) j = fun s ω => JX s ω (k, j) := by
          funext s ω; exact pack_ixc _ _ _ k
        rw [e1, e2]; exact hJX k j
      | right k =>
        have e1 : HU (Fin.castSucc (Fin.natAdd d k)) j = fun s ω => HY s ω (k, j) := by
          funext s ω; exact pack_iyc _ _ _ k
        have e2 : JU (Fin.castSucc (Fin.natAdd d k)) j = fun s ω => JY s ω (k, j) := by
          funext s ω; exact pack_iyc _ _ _ k
        rw [e1, e2]; exact hJY k j
  have hUeq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (i : Fin (d + d + 1)), U s ω i = U 0 ω i +
      (∑ j, JU i j s ω) + ∫ u in (0 : ℝ)..s.val, bU i u.toNNReal ω := by
    filter_upwards [hXeq, hYeq] with ω hx hy s i
    induction i using Fin.lastCases with
    | last =>
      show U s ω iac = U 0 ω iac + (∑ j, JU iac j s ω) + ∫ u in (0 : ℝ)..s.val, bU iac u.toNNReal ω
      simp [U, JU, bU, A]
    | cast i' =>
      induction i' using Fin.addCases with
      | left k =>
        show U s ω (ixc k) = U 0 ω (ixc k) + (∑ j, JU (ixc k) j s ω) +
          ∫ u in (0 : ℝ)..s.val, bU (ixc k) u.toNNReal ω
        simp only [U, JU, bU, pack_ixc]
        exact hx s k
      | right k =>
        show U s ω (iyc k) = U 0 ω (iyc k) + (∑ j, JU (iyc k) j s ω) +
          ∫ u in (0 : ℝ)..s.val, bU (iyc k) u.toNNReal ω
        simp only [U, JU, bU, pack_iyc]
        exact hy s k
  -- the martingale integrals
  have hD1c : Continuous (fderiv ℝ F) :=
    hF.continuous_fderiv two_ne_zero
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hKf : ∀ (i : Fin (d + d + 1)) (j : Fin d),
      Continuous fun q : (SDEState d × SDEState d × ℝ) × (SDEDiffusion d × SDEDiffusion d) =>
        fderiv ℝ F (pack q.1.1 q.1.2.1 q.1.2.2) (EuclideanSpace.single i 1) *
          pack (scol q.2.1 j) (scol q.2.2 j) 0 i := fun i j =>
    ((hD1c.comp (hpk.comp continuous_fst)).clm_apply continuous_const).mul
      ((hcol i j).comp continuous_snd)
  have hKm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      (fun ω => fderiv ℝ F (U s ω) (EuclideanSpace.single i 1) * HU i j s ω) :=
    fun i j s => ((hKf i j).measurable.comp
      (((hXa s).prodMk ((hYa s).prodMk (hAa s))).prodMk (hHHa s)) :)
  have hKc : ∀ i j ω, Continuous
      (fun s => fderiv ℝ F (U s ω) (EuclideanSpace.single i 1) * HU i j s ω) :=
    fun i j ω => ((hKf i j).comp (((hXc ω).prodMk ((hYc ω).prodMk (hAc ω))).prodMk (hHH ω)) :)
  choose K hK using fun (i : Fin (d + d + 1)) (j : Fin d) =>
    exists_hasBrownianItoIntegral hW x₀ j (hKm i j) (hKc i j)
  have hito := ito_formula hW x₀ hUm hUc hUa hHm hHc hJ hbm hbc hUeq hF hK t
  have hKb : ∀ i j, ∃ C, ∀ s ω,
      |fderiv ℝ F (U s ω) (EuclideanSpace.single i 1) * HU i j s ω| ≤ C := fun i j => by
    obtain ⟨C, hC⟩ := hFb i j
    exact ⟨C, fun s ω => hC s ω (A s ω) (hA0 s ω)⟩
  have hKi : ∀ i j, Integrable (K i j t) P ∧ ∫ ω, K i j t ω ∂P = 0 := fun i j => by
    obtain ⟨C, hC⟩ := hKb i j
    obtain ⟨h1, -, h3⟩ := ito_integral_memLp_meanZero hW x₀ j (hKm i j) (hKc i j) hC (hK i j) t
    exact ⟨h1.integrable one_le_two, h3⟩
  refine ⟨fun ω => ∑ i, ∑ j, K i j t ω, ?_, ?_, ?_⟩
  · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hKi i j).1
  · rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hKi i j).1]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hKi i j).1]
    exact Finset.sum_eq_zero fun j _ => (hKi i j).2
  · filter_upwards [hito, hX0, hY0] with ω h hx0 hy0
    have hU0 : F (U 0 ω) = F (pack x0 y0 0) := by
      show F (pack (X 0 ω) (Y 0 ω) (A 0 ω)) = _
      rw [hx0, hy0]
      simp [A]
    show F (U t ω) = F (pack x0 y0 0) + (∑ i, ∑ j, K i j t ω) + _
    rw [h, hU0, add_assoc]
    congr 1
    have hφ : Continuous fun u : ℝ => U u.toNNReal ω := (hUc ω).comp continuous_real_toNNReal
    have hF1c : ∀ i, Continuous fun u : ℝ =>
        fderiv ℝ F (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω :=
      fun i => ((hD1c.comp hφ).clm_apply continuous_const).mul
        ((hbc i ω).comp continuous_real_toNNReal)
    have hF2c : ∀ i i' j, Continuous fun u : ℝ =>
        fderiv ℝ (fderiv ℝ F) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω :=
      fun i i' j => ((((hD2c.comp hφ).clm_apply continuous_const).clm_apply
        continuous_const).mul ((hHc i j ω).comp continuous_real_toNNReal)).mul
        ((hHc i' j ω).comp continuous_real_toNNReal)
    have E1 : (∑ i, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ F (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω) =
        ∫ u in (0 : ℝ)..t.val, ∑ i,
          fderiv ℝ F (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω :=
      (intervalIntegral.integral_finsetSum fun i _ => (hF1c i).intervalIntegrable _ _).symm
    have E2 : (∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ F) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω) =
        ∫ u in (0 : ℝ)..t.val, ∑ i, ∑ i', ∑ j,
        fderiv ℝ (fderiv ℝ F) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω := by
      rw [intervalIntegral.integral_finsetSum fun i _ =>
        (continuous_finsetSum _ fun i' _ => continuous_finsetSum _ fun j _ =>
          hF2c i i' j).intervalIntegrable _ _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum fun i' _ =>
        (continuous_finsetSum _ fun j _ => hF2c i i' j).intervalIntegrable _ _]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [intervalIntegral.integral_finsetSum fun j _ => (hF2c i i' j).intervalIntegrable _ _]
    have hI1 := (continuous_finsetSum Finset.univ fun i _ => hF1c i).intervalIntegrable
      (μ := volume) 0 t.val
    have hI2 : IntervalIntegrable (fun u : ℝ => (1 / 2 : ℝ) * ∑ i, ∑ i', ∑ j,
        fderiv ℝ (fderiv ℝ F) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω)
        volume 0 t.val :=
      (continuous_const.mul (continuous_finsetSum Finset.univ fun i _ =>
        continuous_finsetSum Finset.univ fun i' _ => continuous_finsetSum Finset.univ
          fun j _ => hF2c i i' j)).intervalIntegrable _ _
    rw [E1, E2, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1 hI2]
    refine intervalIntegral.integral_congr fun u _ => ?_
    exact driftGen_coords F _ _ _ _ _ _ _ _


end M10c4


section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

end M10c5


section M10c6
/-! M10c-6: pathwise error of the truncated Euler scheme: on `[0, T]` the coefficient errors
`s₁(Y_u) - H_u`, `b₁(Y_u) - b_u` are `O(osc_w(h) + h)` (lag start `a = y`). -/

theorem euc_norm_le_sum' {ι : Type*} [Fintype ι] (v : EuclideanSpace ℝ ι) :
    ‖v‖ ≤ ∑ k, |v k| := by
  rw [EuclideanSpace.norm_eq]
  calc √(∑ k, ‖v k‖ ^ 2) ≤ √((∑ k, |v k|) ^ 2) := by
        apply Real.sqrt_le_sqrt
        simp only [Real.norm_eq_abs]
        exact Finset.sum_sq_le_sq_sum_of_nonneg fun k _ => abs_nonneg _
    _ = ∑ k, |v k| := Real.sqrt_sq (Finset.sum_nonneg fun k _ => abs_nonneg _)

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c6

end ItoLib

end FlatM_G
-- ===== H =====
section FlatM_H
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10c7
/-! M10c-7: the Euler scheme's coefficient error `‖s₁(Y_u) - H_u‖`, `‖b₁(Y_u) - b_u‖` is
`≤ 2 L K` with `K = d (3 d S δ + 2 S h)` (`δ` = oscillation of `w` over gaps `≤ h` on `[0, T]`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}
  {w : ℝ≥0 → SDEState d}

end M10c7

section M10c8
/-! M10c-8: the coupled expectation bound `lintegral_Gf_le` with `Y` the truncated Euler scheme
driven by `W` (lag start `a = y = x₀`), `s₁ = σ₀`, `b₁ = b₀` on `B̄_{R+3}`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

end M10c8

section M10c9
/-! M10c-9: `E ∫₀ᵗ eulerErr → 0` along any mesh sequence `hₙ → 0` (globally Lipschitz,
bounded truncated coefficients). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c9

section M10c10
/-! M10c-10: the truncated Euler scheme converges to the SDE solution in probability on the
event that `X` stays in `B̄_R` (truncation radius `≥ R + 3`). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10c10

end ItoLib

end FlatM_H
-- ===== I =====
section FlatM_I
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d1
/-! M10d-1 (b5 groundwork): the cell noise `ζ_j = (1/h) ∫₀ʰ (W(s+h) - W(s+u)) du`: measurable for
the future-increment σ-algebra (so independent of the completed past), mean zero, `E ζ² ≤ h/2`. -/

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

end M10d2

end ItoLib

end FlatM_I
-- ===== J =====
section FlatM_J
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10d3
/-! M10d-3 (b5): one full cell of the Euler scheme in cell-noise form, and L² of the grid values. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

theorem coord_abs_le_state (x : SDEState d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i; rwa [Real.norm_eq_abs] at this

end M10d3

end ItoLib

end FlatM_J
-- ===== K =====
section FlatM_K
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e1
/-! M10e-1 (b6 groundwork): the scheme as a deterministic recursion `zrec` driven by the cell
noises `(ξ_l, ζ_l)`; restart identity `Z_{m+k} = zrec_k(Z_{m-1}, Z_m; noises of cells m, m+1, ...)`;
the noises after cell `m` are measurable for the future-increment σ-algebra. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable {s₁ b₁ h}

end M10e1

section M10e2
/-! M10e-2 (b6): restart at a grid time. Independence of the past pair `(Z_{m-1}, Z_m)` and the
future noises gives `E f(Z_{m+k}) = E[ E' f(zrec_k(Z_{m-1}, Z_m; noises after m)) ]`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e2

end ItoLib

end FlatM_K
-- ===== L =====
section FlatM_L
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10e3
/-! M10e-3 (b6): time homogeneity. The restarted Brownian motion is standard; the noises after
cell `m` are the noises of the restarted motion; any two standard Brownian motions have the same
finite-dimensional laws. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10e3

section M10e4
/-! M10e-4 (b6 DONE): restart in law at a grid time: `E f(Z_{m+k}) = E G(Z_{m-1}, Z_m)` with
`G(a, y) = E f(Z_k from (a, y))`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10e4

end ItoLib

end FlatM_L
-- ===== CB =====
section FlatM_CB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

end FlatM_CB
-- ===== CC =====
section FlatM_CC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C2b
/-! CORE route C2b (s23): one-cell Cameron-Martin for the cell noise `(ξ, ζ)` with a constant shift:
weighting by `cmwPi h u ξ` and shifting `(ξ, ζ) ↦ (ξ + u, ζ + u/2)` preserves the law.
Route: dyadic increments are i.i.d. `N(0, h/2^n)` (`dInc_law`), the dyadic approximation of the
noise is a linear function `psiN` of them (`apx_eq_psiN`), finite-dimensional Cameron-Martin
(`gauss_pi_shift`) at each level, then the limit `n → ∞`. -/

end C2b

end ItoLib

end FlatM_CC
-- ===== CD =====
section FlatM_CD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C3
/-! CORE route C3 (s23): adapted discrete Girsanov over the cells. The first `k` cell noises have
law `ν_k = ν_{k-1} ⊗ ν_1` (independence of the past and time homogeneity); shifting cell `l` by
`(u_l, u_l/2)` with `u_l` a measurable function of the earlier noises and weighting by
`∏ cmwPi h u_l ξ_l` preserves `ν_k` (`girsanov_cells`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end C3

end ItoLib

end FlatM_CD
-- ===== CE =====
section FlatM_CE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {d : ℕ}

section C4a
/-! CORE route C4a (s23): the steered coupling, deterministic part. Two copies of the scheme are run
on one noise sequence; the second copy uses the shifted noise `n + (u, u/2)` with the adapted
steering `u_l = J(Ŷ pair)((X_l - Ŷ_l)/(m - l))`. The shift adds `avgApply p u` to a step
(`zstep_shift`), so with a right inverse `J` of `avgApply` the step adds `(X_l - Ŷ_l)/(m - l)`
(`cstep_steer`). The steered copy is the plain scheme driven by `shV (steerN ..)` (`shV_crec`). -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

variable {s₁ b₁ h J m}

end C4a

end ItoLib

end FlatM_CE
-- ===== CF =====
section FlatM_CF
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

end FlatM_CF
-- ===== CG =====
section FlatM_CG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C4c
/-! CORE route C4c (s24): the steered coupling driven by a Brownian motion. Past-measurability of
the coupled chain, the one-step identity `D_{k+1} = (1 - 1/(m-k)) D_k + h/2 Δb + cellNoise`,
and the second-moment step feeding `steer_rec` (CF.lean). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4c

end ItoLib

end FlatM_CG
-- ===== CH =====
section FlatM_CH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
variable {Ω : Type*}

section C4d
/-! CORE route C4d (s24): lower bound of a weighted event by the relative entropy, with no second
moment of the Girsanov martingale. If `f > 0`, `E f ≤ 1` and `E[-log f] ≤ K`, then
`E[1_E f] ≥ e^{-a} (P E - (K+1)/a)` (Markov on `-log f + f ≥ (-log f)⁺`). -/

end C4d

section C4d2
/-! C4d (s25): the relative entropy of the steering weight. -/
open EthierKurtz

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C4d2

end ItoLib

end FlatM_CH
-- ===== CI =====
section FlatM_CI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
set_option autoImplicit false

namespace ItoLib

section C5a
/-! CORE route C5a (s25): Kolmogorov's maximal inequality in the abstract form needed for the
exit estimate of the Euler chain. The only probabilistic input is the orthogonality of the
"stopped" value `1_{F_k} M_k` to the remaining increment `M_m - M_k`. -/

variable {Ω : Type*} {d : ℕ}

end C5a

end ItoLib

end FlatM_CI
-- ===== CK =====
section FlatM_CK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5c
/-! CORE route C5c (s26): exit estimate for the Euler chain with bounded coefficients.
`Z_k = Z_0 + M_k + D_k` with `M` the martingale part (orthogonal cell increments) and `D` the
drift part (`‖D_k‖ ≤ k h S`); Kolmogorov's maximal inequality on `M` gives
`(δ/2)^2 P(∃ k ≤ m, ‖Z_k - Z_0‖ ≥ δ) ≤ 16 d S^2 m h` once `m h S ≤ δ/2`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end C5c
end ItoLib

end FlatM_CK
-- ===== CL =====
section FlatM_CL
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5d
/-! CORE route C5d (s26): a global, measurable, bounded right inverse of `avgApply` for diffusions
of the form `s x (i, j) = a i x * Γ j i` (the Kolmogorov diffusion read through a projection),
when `Γ` is invertible and `|a i x + a i y| ≥ κ > 0`. -/

variable {d : ℕ}

end C5d
end ItoLib

end FlatM_CL
-- ===== M =====
section FlatM_M
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f1
/-! M10f-1 (b7 groundwork): the restart function `G_k(a, y) = E f(Z_k from (a, y))` is Lipschitz
in the initial pair for Lipschitz `f`, uniformly in the mesh (via `euler_stab_exp`). -/

variable [MeasurableSpace Ω] {P : Measure Ω}
variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f1

end ItoLib

end FlatM_M
-- ===== N =====
section FlatM_N
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10f2
/-! M10f-2 (b7): uniform smallness of Euler cell increments, and the exit probability
`P(path leaves B̄_R before T) → 0`. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {w : ℝ≥0 → SDEState d}

variable [MeasurableSpace Ω]

end M10f2

section M10f3
/-! M10f-3 (b7): the Euler scheme approximates `X_T` in law, up to the exit probability. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f3

section M10f4
/-! M10f-4 (b7): the real-analysis wrap-up of the Chapman-Kolmogorov limit
(reverse Fatou in `n`, dominated convergence in `R`). -/

variable [MeasurableSpace Ω]

end M10f4

section M10f5
/-! M10f-5 (b7): the restart function `eulerG`, its bound and uniform Lipschitz property, and the
approximation `eulerG(y, y) ≈ E f(X^y_t)` up to the exit probability. -/

variable [MeasurableSpace Ω]

variable {P : Measure Ω} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

end M10f5

section M10f6
/-! M10f-6 (b7 DONE): Chapman-Kolmogorov in integrated form for bounded Lipschitz test functions,
with a measurable version `g` of `y ↦ E f(X^y_t)`. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10f6

end ItoLib

end FlatM_N
-- ===== O =====
section FlatM_O
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section M10g
/-! M10g: from integrated Chapman-Kolmogorov identities for thickened indicators (bounded
Lipschitz test functions) to a Markov kernel and set-wise Chapman-Kolmogorov. -/

variable [MeasurableSpace Ω] {P : Measure Ω}

end M10g

end ItoLib

end FlatM_O
-- ===== P =====
section FlatM_P
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10h
/-! M10h (b9/b11): local Lipschitz on compact sets, coordinate clamps, truncation families,
and the Kolmogorov coefficients. -/

/-- Local Lipschitz on `s` gives a Lipschitz bound on every compact `K ⊆ s`. -/
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

variable {d : ℕ}

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

end M10h

section M10i
open StochKolmogorov.Persist
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

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

theorem orthant_isClosed : IsClosed (orthant n) := by
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; simp [orthant]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)

end M10j

end ItoLib

end FlatM_P
-- ===== CM =====
section FlatM_CM
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5dK
/-! CORE route C5d, Kolmogorov instance (s26): the coefficients read through the box clamp
`boxP α β` (box `[α, β]^n` inside the open orthant) are globally Lipschitz and bounded, have the
form `s x (i, j) = aK i x * Γ j i`, and `|aK i x + aK i y| ≥ κ > 0` (Assumption 1.1 part 1). -/

variable {n : ℕ}

/-- Coordinatewise clamp to the box `[α, β]^n`. -/
noncomputable def boxP (α β : ℝ) (x : SDEState n) : SDEState n :=
  WithLp.toLp 2 (fun i => max α (min β (x i)))

theorem boxP_apply (α β : ℝ) (x : SDEState n) (i : Fin n) :
    boxP α β x i = max α (min β (x i)) := rfl

theorem box1_lip (α β a b : ℝ) : |max α (min β a) - max α (min β b)| ≤ |a - b| := by
  rw [abs_le]
  have h1 := le_abs_self (a - b); have h2 := neg_abs_le (a - b)
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

theorem boxP_lip (α β : ℝ) (x y : SDEState n) : ‖boxP α β x - boxP α β y‖ ≤ ‖x - y‖ :=
  norm_sub_le_of_coord fun i => by rw [boxP_apply, boxP_apply]; exact box1_lip _ _ _ _

theorem boxP_mem {α β : ℝ} (hαβ : α ≤ β) (x : SDEState n) (i : Fin n) :
    α ≤ boxP α β x i ∧ boxP α β x i ≤ β := by
  rw [boxP_apply]
  exact ⟨le_max_left _ _, max_le hαβ (min_le_left _ _)⟩

theorem boxP_eq {α β : ℝ} {x : SDEState n} (hx : ∀ i, α ≤ x i ∧ x i ≤ β) : boxP α β x = x := by
  ext i
  rw [boxP_apply, min_eq_right (hx i).2, max_eq_right (hx i).1]

theorem boxP_continuous (α β : ℝ) : Continuous (boxP (n := n) α β) :=
  LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]; exact boxP_lip α β x y)

open StochKolmogorov.Persist

/-- The box `[α, β]^n`. -/
def boxSet (α β : ℝ) : Set (SDEState n) := {u | ∀ l, α ≤ u l ∧ u l ≤ β}

theorem boxSet_isCompact {α β : ℝ} (hα : 0 ≤ α) : IsCompact (boxSet (n := n) α β) := by
  have hc : IsClosed (boxSet (n := n) α β) := by
    have : boxSet (n := n) α β = ⋂ i, ({y : SDEState n | α ≤ y i} ∩ {y | y i ≤ β}) := by
      ext y; simp [boxSet, forall_and]
    rw [this]
    exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
      (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hc ((Metric.isBounded_closedBall
    (x := (0 : SDEState n)) (r := n * β)).subset fun y hy => ?_)
  rw [Metric.mem_closedBall, dist_zero_right]
  exact norm_le_card_mul fun i => by rw [abs_of_nonneg (hα.trans (hy i).1)]; exact (hy i).2

theorem boxP_mem_boxSet {α β : ℝ} (hαβ : α ≤ β) (x : SDEState n) : boxP α β x ∈ boxSet α β :=
  fun l => boxP_mem hαβ x l

end C5dK
end ItoLib

end FlatM_CM
-- ===== CN =====
section FlatM_CN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5g
/-! CORE route, s27: (1) `Γ` is invertible under Assumption 1.1 part 1; (2) a generic discrete
martingale `gmart` built from bounded past-measurable cell coefficients: measurability, second
moment, orthogonality and the Kolmogorov maximal inequality (used for the tracking estimate of
the steered chain). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

end C5g
end ItoLib

end FlatM_CN
-- ===== QA =====
section FlatM_QA
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QA
/-! lemma_3_1 (aaf23e78) toolkit, part QA: continuous versions of Ito integrals.
Dyadic grid `gpt m l = l / 2^m`, the horizon-free step integral `stepM` (mesh `2^{-q}` on
`[0,q]`), its values at finer grid points, and a continuous-time maximal inequality for
differences of step integrals (via `gmart_max`). -/

end QA
end ItoLib

end FlatM_QA
-- ===== QB =====
section FlatM_QB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QB
/-! lemma_3_1 toolkit, part QB: uniform `L²`-continuity of a bounded continuous integrand, and
the pathwise identification of `stepM q t` as the limit of `t`-grid Riemann sums whose
coefficients are the level-`q` left values (grid comparison, step 1). -/

end QB
end ItoLib

end FlatM_QB
-- ===== QC =====
section FlatM_QC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QC
/-! lemma_3_1 toolkit, part QC: grid comparison in `L²` and `stepM q t → J t` in probability
for every fixed `t` (bounded continuous adapted integrand). -/

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

end QC
end ItoLib

end FlatM_QC
-- ===== QD =====
section FlatM_QD
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section QDan
/-! Pure analysis: a sequence of continuous functions with geometrically small successive
differences on growing intervals converges pointwise to a continuous limit. -/

end QDan

section QD

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d}

/-- **Continuous version of the Ito integral** of a bounded continuous adapted integrand. -/
theorem contIto_bdd (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d)
    {H : ℝ≥0 → Ω → ℝ} (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHa : ∀ s, Measurable (H s)) (hHc : ∀ ω, Continuous fun s => H s ω) {C : ℝ}
    (hC : ∀ s ω, |H s ω| ≤ C) :
    ∃ Jc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Jc t ω) ∧
      (∀ t, Measurable[completedBrownianPast P W (fun _ => x₀) t] (Jc t)) ∧
      (∀ t, Measurable (Jc t)) ∧ (∀ ω, Jc 0 ω = 0) ∧
      HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
        (fun s ω => W s ω j) H Jc := by
  exact (EthierKurtz.brownian_ito_integral_locality_and_continuity hW x₀).2.2.1 j H hHm hHa hHc C hC
end QD

end ItoLib

end FlatM_QD
-- ===== Q =====
section FlatM_Q
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10k
/-! M10k (b10 calculus): the cubic negative part `φ(v) = (v⁻)³` (C², `v φ' = 3φ`, `v² φ'' = 6φ`)
and the orthant test function `Hf r u = e^{-a} χ_r(|x|²) Σ_k φ(x_k)`. -/

variable {d : ℕ}

end M10k

section M10l
/-! M10l (b10 drift): generator of `Hf r` inside the ball and its global bound. -/
variable {d : ℕ}

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

end M10m

end ItoLib

end FlatM_Q
-- ===== R =====
section FlatM_R
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10n
/-! M10n (b10 expectation and Markov step): `E Hf_r(X_t, A_t) ≤ Hf_r(x₀) + B/M`, and
`P{X stays in B̄_R on [0,t], ε < Φ(X_t)} ≤ (Hf_r(x₀) + B/M) / (e^{-ct} ε)`. -/
variable {Ω : Type*} {d : ℕ}

end M10n

end ItoLib

end FlatM_R
-- ===== S =====
section FlatM_S
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M10o
/-! M10o (b10 done): orthant invariance of the Kolmogorov solutions, and the Markov statement. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M10o

end ItoLib

end FlatM_S
-- ===== U =====
section FlatM_U
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section M11a
/-! M11a (lemma_3_1 clause 2): pathwise uniqueness for all times at once, and for the Kolmogorov
system. -/

theorem denseRange_rat_toNNReal : DenseRange fun q : ℚ => (q : ℝ).toNNReal := by
  have hs : DenseRange Real.toNNReal := Function.Surjective.denseRange fun x =>
    ⟨(x : ℝ), Real.toNNReal_coe⟩
  exact hs.comp Rat.denseRange_cast continuous_real_toNNReal

open StochKolmogorov.Persist

end M11a

section M11b
/-! M11b (lemma_3_1 clause 4a): `H < ∞`, i.e. `bracket35` is bounded above on the orthant. -/
open StochKolmogorov.Persist
variable {n : ℕ}

theorem l1_continuous : Continuous (l1 (n := n)) :=
  continuous_finset_sum _ fun i _ => (PiLp.continuous_apply 2 _ i).abs

theorem bracket35_continuousOn (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ)
    (hc : c ∈ openOrthant n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ContinuousOn (bracket35 C c γb δ₀) (orthant n) := by
  have hf : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hC i).1.continuousOn
  have hg : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  have hx : ∀ i, Continuous fun x : SDEState n => x i := fun i => PiLp.continuous_apply 2 _ i
  have hden : ∀ x ∈ orthant n, 1 + ∑ i, c i * x i ≠ 0 := fun x hx' => by
    have : 0 ≤ ∑ i, c i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hx' i)
    linarith
  have hD : Continuous fun x : SDEState n => 1 + ∑ i, c i * x i :=
    continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (hx i))
  unfold bracket35 cBracket
  refine ((((ContinuousOn.div ?_ hD.continuousOn hden).sub
    (ContinuousOn.div ?_ (hD.pow 2).continuousOn fun x hx' => pow_ne_zero 2 (hden x hx'))).add
      continuousOn_const).add (continuousOn_const.mul ?_)).add (continuousOn_const.mul ?_)
  · exact continuousOn_finset_sum _ fun i _ =>
      ((continuous_const.mul (hx i)).continuousOn).mul (hf i)
  · refine continuousOn_const.mul (continuousOn_finset_sum _ fun i _ =>
      continuousOn_finset_sum _ fun j _ => ?_)
    exact ((((continuous_const.mul continuous_const).mul (hx i)).mul (hx j)).continuousOn.mul
      (hg i)).mul (hg j)
  · exact continuousOn_finset_sum _ fun i _ =>
      (continuousOn_const.mul (hf i).abs).add ((hg i).pow 2)
  · exact continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ =>
      (((hg i).mul (hg j)).mul continuousOn_const).abs

theorem bracket35_bddAbove (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ)
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) :
    BddAbove ((bracket35 C c γb δ₀) '' orthant n) := by
  obtain ⟨-, hC, hc, hγ, ε, hε, R, hR⟩ := hA
  obtain ⟨hδ0, hδγ, hδg⟩ := hδ
  set K : Set (SDEState n) := orthant n ∩ {x | l1 x ≤ R} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((orthant_isClosed).inter (isClosed_le l1_continuous continuous_const)) ?_
    refine (Metric.isBounded_closedBall (x := (0 : SDEState n)) (r := R)).subset fun x hx => ?_
    rw [mem_closedBall_zero_iff]
    exact (euc_norm_le_sum' x).trans hx.2
  obtain ⟨M1, hM1⟩ := hKc.bddAbove_image
    ((bracket35_continuousOn C c γb δ₀ hc hC).mono Set.inter_subset_left)
  refine ⟨max M1 0, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  by_cases hl : l1 x ≤ R
  · exact (hM1 ⟨x, ⟨hx, hl⟩, rfl⟩).trans (le_max_left _ _)
  · have h1 := hR x hx (not_le.1 hl).le
    have h2 := hδg x hx
    have hfa : 0 ≤ ∑ i, |C.f i x| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hs : ∑ i, (|C.f i x| + C.g i x ^ 2) = ∑ i, |C.f i x| + ∑ i, C.g i x ^ 2 :=
      Finset.sum_add_distrib
    have hs2 : ∑ i, (2 * |C.f i x| + C.g i x ^ 2) = 2 * ∑ i, |C.f i x| + ∑ i, C.g i x ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have h3 : 2 * δ₀ * ∑ i, |C.f i x| ≤ γb * ∑ i, |C.f i x| :=
      mul_le_mul_of_nonneg_right (by linarith) hfa
    unfold bracket35
    rw [hs2]
    rw [hs] at h1
    refine le_trans ?_ (le_max_right _ _)
    linarith only [h1, h2, h3, hε]

end M11b

end ItoLib

end FlatM_U
-- ===== QE =====
section FlatM_QE
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QEneg
variable {Ω : Type*} [MeasurableSpace Ω]

theorem hasBrownianItoIntegral_neg {P : Measure Ω} {ℱ : ℝ≥0 → MeasurableSpace Ω}
    {W H J : ℝ≥0 → Ω → ℝ} (h : HasBrownianItoIntegral P ℱ W H J) :
    HasBrownianItoIntegral P ℱ W (fun s ω => -H s ω) (fun s ω => -J s ω) := by
  refine ⟨fun t ω => by simpa using h.1 t ω, fun t => ?_⟩
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := h.2 t
  have e : ∀ m u ω, itoStepValue t m (fun k ω => -a m k ω) u ω =
      -itoStepValue t m (a m) u ω := by
    intro m u ω
    simp only [itoStepValue, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have e3 : ∀ m ω, itoStepSum W t m (fun k ω => -a m k ω) ω = -itoStepSum W t m (a m) ω := by
    intro m ω
    simp [itoStepSum, Finset.sum_neg_distrib, neg_mul]
  refine ⟨fun m k ω => -a m k ω, fun m k hk => (ha1 m k hk).neg, fun m => ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := ha2 m
    exact ⟨C, fun k hk ω => by simpa using hC k hk ω⟩
  · refine TendstoInMeasure.congr_left (fun m => ae_of_all _ fun ω => ?_) ha3
    simp only [e]
    congr 1; funext u; ring
  · have h4 := tendstoInMeasure_mul_left_real (P := P) (fun _ => (-1 : ℝ)) one_pos
      (fun _ => by simp) ha4
    refine (h4.congr_left (fun m => ae_of_all _ fun ω => ?_)).congr_right (ae_of_all _ fun ω => ?_)
    · simp [e3]
    · simp

end QEneg

section QEF

/-- `F(y, z) = y e^{-z}` on `ℝ²`. -/
noncomputable def Fx (v : SDEState 2) : ℝ := v 0 * Real.exp (-(v 1))

theorem Fx_contDiff : ContDiff ℝ 2 Fx :=
  (coord_contDiff 0).mul ((coord_contDiff 1).neg.exp)

theorem Fx_line (u v : SDEState 2) (r : ℝ) :
    Fx (u + r • v) = (u 0 + r * v 0) * Real.exp (-(u 1 + r * v 1)) := by
  simp [Fx]

theorem Fx_line_deriv (u v : SDEState 2) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Fx (u + r • v))
      ((v 0 - (u 0 + s * v 0) * v 1) * Real.exp (-(u 1 + s * v 1))) s := by
  rw [funext (Fx_line u v)]
  have h := ((((hasDerivAt_id' s).mul_const (v 0)).const_add (u 0))).mul
    ((((hasDerivAt_id' s).mul_const (v 1)).const_add (u 1)).neg.exp)
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  ring

theorem Fx_fderiv (u v : SDEState 2) :
    fderiv ℝ Fx u v = (v 0 - u 0 * v 1) * Real.exp (-(u 1)) := by
  refine fderiv_eq_of_line (Fx_contDiff.differentiable two_ne_zero) u v ?_
  have h := Fx_line_deriv u v 0
  simpa using h

theorem Fx_fderiv2 (u v : SDEState 2) :
    fderiv ℝ (fderiv ℝ Fx) u v v = (u 0 * v 1 ^ 2 - 2 * v 0 * v 1) * Real.exp (-(u 1)) := by
  refine fderiv2_eq_of_line Fx_contDiff u v (fun s => Fx_line_deriv u v s) ?_
  have h := ((((hasDerivAt_id' (0 : ℝ)).mul_const (v 0)).const_add (u 0)).mul_const
    (v 1)).const_sub (v 0) |>.mul
    ((((hasDerivAt_id' (0 : ℝ)).mul_const (v 1)).const_add (u 1)).neg.exp)
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  ring

theorem sum2_bilin {e : ℕ} (B : SDEState e →L[ℝ] SDEState e →L[ℝ] ℝ) (c : Fin e → ℝ) :
    ∑ i, ∑ i', B (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) * c i * c i' =
      B (∑ i, c i • EuclideanSpace.single i 1) (∑ i', c i' • EuclideanSpace.single i' 1) := by
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  ring

theorem vec2_apply0 (a b : ℝ) :
    (a • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) + b • EuclideanSpace.single 1 1 : SDEState 2) 0
      = a := by
  simp

theorem vec2_apply1 (a b : ℝ) :
    (a • EuclideanSpace.single (0 : Fin 2) (1 : ℝ) + b • EuclideanSpace.single 1 1 : SDEState 2) 1
      = b := by
  simp

theorem pair_measurable {Ω : Type*} {m : MeasurableSpace Ω} {a b : Ω → ℝ}
    (ha : Measurable[m] a) (hb : Measurable[m] b) :
    Measurable[m] (fun ω => (WithLp.toLp 2 ![a ω, b ω] : SDEState 2)) := by
  refine (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun i => ?_)
  fin_cases i
  · simpa using ha
  · simpa using hb

theorem pair_continuous {a b : ℝ≥0 → ℝ} (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun s => (WithLp.toLp 2 ![a s, b s] : SDEState 2)) := by
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · simpa using ha
  · simpa using hb

end QEF

section QEface
open StochKolmogorov.Persist
variable {n : ℕ}

theorem posPart_continuous' : Continuous (posPart (n := n)) := continuous_posPart

theorem coef_continuous {φ : SDEState n → ℝ} (hφ : ContinuousOn φ (orthant n)) :
    Continuous fun y : SDEState n => φ (posPart y) :=
  hφ.comp_continuous posPart_continuous' posPart_mem_orthant

theorem coefR_continuous {φ : SDEState n → ℝ} (hφ : ContinuousOn φ (orthant n)) (R : ℝ) :
    Continuous fun y : SDEState n => φ (boxP 0 R (posPart y)) :=
  hφ.comp_continuous ((boxP_continuous 0 R).comp posPart_continuous')
    (fun y l => by rw [boxP_apply]; exact le_max_left _ _)

theorem coefR_bdd {φ : SDEState n → ℝ} (hφ : ContinuousOn φ (orthant n)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ M, ∀ y : SDEState n, |φ (boxP 0 R (posPart y))| ≤ M := by
  obtain ⟨M, hM⟩ := (boxSet_isCompact (n := n) (α := 0) (β := R) le_rfl).exists_bound_of_continuousOn
    (hφ.mono fun u hu l => (hu l).1)
  exact ⟨M, fun y => by simpa [Real.norm_eq_abs] using hM _ (boxP_mem_boxSet hR _)⟩

theorem boxP_posPart_eq {R : ℝ} {y : SDEState n} (hy : ∀ i, |y i| ≤ R) :
    boxP 0 R (posPart y) = posPart y :=
  boxP_eq fun i => ⟨by rw [posPart_apply']; exact le_max_right _ _,
    by rw [posPart_apply']; exact max_le ((le_abs_self _).trans (hy i)) ((abs_nonneg _).trans (hy i))⟩

theorem coord_meas {Ω : Type*} {m : MeasurableSpace Ω} {f : Ω → SDEState n}
    (hf : Measurable[m] f) (i : Fin n) : Measurable[m] (fun ω => f ω i) :=
  ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).measurable.comp hf

theorem integral_sum_cont {ι : Type*} (s : Finset ι) {f : ι → ℝ → ℝ} (hf : ∀ i, Continuous (f i))
    (a b : ℝ) : ∑ i ∈ s, ∫ u in a..b, f i u = ∫ u in a..b, ∑ i ∈ s, f i u :=
  (intervalIntegral.integral_finset_sum fun i _ => (hf i).intervalIntegrable a b).symm

theorem integral_sum3 {a b c : ℕ} (F : Fin a → Fin b → Fin c → ℝ → ℝ)
    (hF : ∀ i k l, Continuous (F i k l)) (α β : ℝ) :
    ∑ i, ∑ k, ∑ l, ∫ u in α..β, F i k l u = ∫ u in α..β, ∑ i, ∑ k, ∑ l, F i k l u := by
  have h1 : ∀ i k, ∑ l, ∫ u in α..β, F i k l u = ∫ u in α..β, ∑ l, F i k l u :=
    fun i k => integral_sum_cont _ (hF i k) α β
  have h2 : ∀ i, ∑ k, ∫ u in α..β, ∑ l, F i k l u = ∫ u in α..β, ∑ k, ∑ l, F i k l u :=
    fun i => integral_sum_cont (f := fun k u => ∑ l, F i k l u) _
      (fun k => continuous_finset_sum _ fun l _ => hF i k l) α β
  have h3 : ∑ i, ∫ u in α..β, ∑ k, ∑ l, F i k l u = ∫ u in α..β, ∑ i, ∑ k, ∑ l, F i k l u :=
    integral_sum_cont (f := fun i u => ∑ k, ∑ l, F i k l u) _
      (fun i => continuous_finset_sum _ fun k _ => continuous_finset_sum _ fun l _ => hF i k l) α β
  simp only [h1, h2]
  exact h3

/-- **Exponential representation** of a Kolmogorov coordinate while the path stays in the box
`[-R,R]ⁿ`: `Y_k(t) = x_k e^{Z(t)}` with `Z` continuous. -/
theorem face_rep {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Coeffs n) {B : ℝ≥0 → Ω → SDEState n} (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x : SDEState n} {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (k : Fin n)
    {R : ℝ} (hR : 0 ≤ R) :
    ∃ Z : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Z t ω) ∧ ∀ t : ℝ≥0, ∀ᵐ ω ∂P,
      (∀ s ≤ t, ∀ i, |Y s ω i| ≤ R) → Y t ω k = x k * Real.exp (Z t ω) := by
  obtain ⟨hYm, hYc, hYa, hY0, J, hJc, hJa, hJ, -, hYeq⟩ := hY
  have hgc0 : Continuous fun y : SDEState n => C.g k (posPart y) :=
    coef_continuous (hC k).2.continuousOn
  have hfc0 : Continuous fun y : SDEState n => C.f k (posPart y) :=
    coef_continuous (hC k).1.continuousOn
  set gR : SDEState n → ℝ := fun y => C.g k (boxP 0 R (posPart y)) with hgR
  set fR : SDEState n → ℝ := fun y => C.f k (boxP 0 R (posPart y)) with hfR
  have hgc : Continuous gR := coefR_continuous (hC k).2.continuousOn R
  have hfc : Continuous fR := coefR_continuous (hC k).1.continuousOn R
  obtain ⟨Mg, hMg⟩ := coefR_bdd (hC k).2.continuousOn hR
  have hYk : ∀ ω, Continuous fun s => Y s ω k := fun ω =>
    ((continuous_apply k).comp (PiLp.continuous_ofLp 2 _)).comp (hYc ω)
  set Hc : Fin n → ℝ≥0 → Ω → ℝ := fun j s ω => gR (Y s ω) * C.Γ j k with hHc
  have hHcm : ∀ j s, Measurable[completedBrownianPast P B (fun _ => x) s] (Hc j s) :=
    fun j s => (hgc.measurable.comp (hYa s)).mul_const _
  have hHca : ∀ j s, Measurable (Hc j s) := fun j s => (hgc.measurable.comp (hYm s)).mul_const _
  have hHcc : ∀ j ω, Continuous fun s => Hc j s ω := fun j ω =>
    (hgc.comp (hYc ω)).mul continuous_const
  have hHcb : ∀ j s ω, |Hc j s ω| ≤ Mg * |C.Γ j k| := fun j s ω => by
    simp only [hHc, abs_mul]; exact mul_le_mul_of_nonneg_right (hMg _) (abs_nonneg _)
  choose Jc hJcc hJcm hJcam hJc0 hJcI using fun j =>
    contIto_bdd hB x j (hHcm j) (hHca j) (hHcc j) (hHcb j)
  set bZ : ℝ≥0 → Ω → ℝ := fun s ω => fR (Y s ω) - (1 / 2) * ∑ j, (Hc j s ω) ^ 2 with hbZ
  have hbZc : ∀ ω, Continuous fun s => bZ s ω := fun ω =>
    (hfc.comp (hYc ω)).sub (continuous_const.mul
      (continuous_finset_sum _ fun j _ => (hHcc j ω).pow 2))
  have hbZm : ∀ s, Measurable[completedBrownianPast P B (fun _ => x) s] (bZ s) := fun s =>
    (hfc.measurable.comp (hYa s)).sub (measurable_const.mul
      (Finset.measurable_sum _ fun j _ => (hHcm j s).pow_const 2))
  have hbZa : ∀ s, Measurable (bZ s) := fun s =>
    (hfc.measurable.comp (hYm s)).sub (measurable_const.mul
      (Finset.measurable_sum _ fun j _ => (hHca j s).pow_const 2))
  set Z : ℝ≥0 → Ω → ℝ := fun t ω => ∑ j, Jc j t ω + ∫ u in (0 : ℝ)..t.val, bZ u.toNNReal ω
    with hZ
  have hprim : ∀ ω, Continuous fun t : ℝ≥0 => ∫ u in (0 : ℝ)..t.val, bZ u.toNNReal ω :=
    fun ω => (intervalIntegral.continuous_primitive (fun a b =>
      ((hbZc ω).comp continuous_real_toNNReal).intervalIntegrable a b) 0).comp
      NNReal.continuous_coe
  have hZc : ∀ ω, Continuous fun t => Z t ω := fun ω =>
    (continuous_finset_sum _ fun j _ => hJcc j ω).add (hprim ω)
  have hZm : ∀ s, Measurable[completedBrownianPast P B (fun _ => x) s] (Z s) := fun s =>
    (Finset.measurable_sum _ fun j _ => hJcm j s).add
      (measurable_intervalIntegral_of_continuous _ s (fun u hu =>
        (hbZm u).mono (completedBrownianPast_mono P B _ hu) le_rfl) hbZc)
  have hZa : ∀ s, Measurable (Z s) := fun s =>
    (Finset.measurable_sum _ fun j _ => hJcam j s).add
      (measurable_intervalIntegral_of_continuous _ s (fun u _ => hbZa u) hbZc)
  have hZ0 : ∀ ω, Z 0 ω = 0 := fun ω => by simp [hZ, hJc0]
  refine ⟨Z, hZc, fun t => ?_⟩
  -- the pair process `(Y_k, Z)`
  set X2 : ℝ≥0 → Ω → SDEState 2 := fun s ω => WithLp.toLp 2 ![Y s ω k, Z s ω] with hX2
  have hX20 : ∀ s ω, X2 s ω 0 = Y s ω k := fun s ω => by simp [hX2]
  have hX21 : ∀ s ω, X2 s ω 1 = Z s ω := fun s ω => by simp [hX2]
  have hXm : ∀ s, Measurable (X2 s) := fun s => pair_measurable (coord_meas (hYm s) k) (hZa s)
  have hXa : ∀ s, Measurable[completedBrownianPast P B (fun _ => x) s] (X2 s) := fun s =>
    pair_measurable (coord_meas (hYa s) k) (hZm s)
  have hXc : ∀ ω, Continuous fun s => X2 s ω := fun ω => pair_continuous (hYk ω) (hZc ω)
  set H2 : Fin 2 → Fin n → ℝ≥0 → Ω → ℝ :=
    ![fun j s ω => Y s ω k * C.g k (posPart (Y s ω)) * C.Γ j k, Hc] with hH2
  set J2 : Fin 2 → Fin n → ℝ≥0 → Ω → ℝ := ![fun j s ω => J s ω (k, j), Jc] with hJ2
  set b2 : Fin 2 → ℝ≥0 → Ω → ℝ := ![fun s ω => Y s ω k * C.f k (posPart (Y s ω)), bZ] with hb2
  have hH2m : ∀ i j s, Measurable[completedBrownianPast P B (fun _ => x) s] (H2 i j s) := by
    refine Fin.forall_fin_two.2 ⟨fun j s => ?_, fun j s => hHcm j s⟩
    exact ((coord_meas (hYa s) k).mul (hgc0.measurable.comp (hYa s))).mul_const _
  have hH2c : ∀ i j ω, Continuous fun s => H2 i j s ω := by
    refine Fin.forall_fin_two.2 ⟨fun j ω => ?_, fun j ω => hHcc j ω⟩
    exact ((hYk ω).mul (hgc0.comp (hYc ω))).mul continuous_const
  have hJ2I : ∀ i j, HasBrownianItoIntegral P (completedBrownianPast P B (fun _ => x))
      (fun s ω => B s ω j) (H2 i j) (J2 i j) :=
    Fin.forall_fin_two.2 ⟨fun j => hJ k j, fun j => hJcI j⟩
  have hb2m : ∀ i s, Measurable[completedBrownianPast P B (fun _ => x) s] (b2 i s) := by
    refine Fin.forall_fin_two.2 ⟨fun s => ?_, fun s => hbZm s⟩
    exact (coord_meas (hYa s) k).mul (hfc0.measurable.comp (hYa s))
  have hb2c : ∀ i ω, Continuous fun s => b2 i s ω := by
    refine Fin.forall_fin_two.2 ⟨fun ω => ?_, fun ω => hbZc ω⟩
    exact (hYk ω).mul (hfc0.comp (hYc ω))
  have hX2eq : ∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (i : Fin 2), X2 s ω i = X2 0 ω i + (∑ j, J2 i j s ω) +
      ∫ u in (0 : ℝ)..s.val, b2 i u.toNNReal ω := by
    filter_upwards [hYeq] with ω h s
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [hX20, hX20]; exact h s k
    · rw [hX21, hX21, hZ0, zero_add]; rfl
  have hD1 : ∀ i : Fin 2, Continuous fun v : SDEState 2 =>
      fderiv ℝ Fx v (EuclideanSpace.single i 1) := fun i =>
    (Fx_contDiff.continuous_fderiv two_ne_zero).clm_apply continuous_const
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ Fx)) :=
    (Fx_contDiff.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hD2 : ∀ i i' : Fin 2, Continuous fun v : SDEState 2 =>
      fderiv ℝ (fderiv ℝ Fx) v (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) :=
    fun i i' => (hD2c.clm_apply continuous_const).clm_apply continuous_const
  have hKm : ∀ i j s, Measurable[completedBrownianPast P B (fun _ => x) s]
      (fun ω => fderiv ℝ Fx (X2 s ω) (EuclideanSpace.single i 1) * H2 i j s ω) :=
    fun i j s => ((hD1 i).measurable.comp (hXa s)).mul (hH2m i j s)
  have hKc : ∀ i j ω, Continuous fun s =>
      fderiv ℝ Fx (X2 s ω) (EuclideanSpace.single i 1) * H2 i j s ω :=
    fun i j ω => ((hD1 i).comp (hXc ω)).mul (hH2c i j ω)
  choose K hK using fun i j => exists_hasBrownianItoIntegral hB x j (hKm i j) (hKc i j)
  have hito := ito_formula hB x hXm hXc hXa hH2m hH2c hJ2I hb2m hb2c hX2eq Fx_contDiff hK t
  set E : Set Ω := {ω | ∀ s ≤ t, ∀ i, |Y s ω i| ≤ R} with hE
  -- the two martingale parts cancel while the path stays in the box
  have hcan : ∀ j, ∀ᵐ ω ∂P, ω ∈ E → K 0 j t ω = -K 1 j t ω := by
    intro j
    have hneg := hasBrownianItoIntegral_neg (hK 1 j)
    refine hasBrownianItoIntegral_eq_on hB x j (hKm 0 j) (hKc 0 j) (fun s => (hKm 1 j s).neg)
      (fun ω => (hKc 1 j ω).neg) (hK 0 j) hneg t E ?_
    intro ω hω N i hi
    have hbox := hω _ (dyTime_le t hi)
    set s := dyTime t N i
    simp only [Pi.neg_apply]
    have e0 : H2 0 j s ω = Y s ω k * C.g k (posPart (Y s ω)) * C.Γ j k := rfl
    have e1 : H2 1 j s ω = C.g k (posPart (Y s ω)) * C.Γ j k := by
      show C.g k (boxP 0 R (posPart (Y s ω))) * C.Γ j k = _
      rw [boxP_posPart_eq hbox]
    rw [e0, e1, Fx_fderiv, Fx_fderiv, hX20, hX21]
    simp
    ring
  -- the drift parts cancel
  have hpt : ∀ ω ∈ E, ∀ s ≤ t, (∑ i, fderiv ℝ Fx (X2 s ω) (EuclideanSpace.single i 1) * b2 i s ω)
      + (1 / 2) * (∑ i, ∑ i', ∑ j, fderiv ℝ (fderiv ℝ Fx) (X2 s ω) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1) * H2 i j s ω * H2 i' j s ω) = 0 := by
    intro ω hω s hs
    have hbox := hω s hs
    have hswap : (∑ i, ∑ i', ∑ j, fderiv ℝ (fderiv ℝ Fx) (X2 s ω) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1) * H2 i j s ω * H2 i' j s ω) =
        ∑ j, ∑ i, ∑ i', fderiv ℝ (fderiv ℝ Fx) (X2 s ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H2 i j s ω * H2 i' j s ω := by
      calc
        _ = ∑ i, ∑ j, ∑ i', fderiv ℝ (fderiv ℝ Fx) (X2 s ω) (EuclideanSpace.single i 1)
              (EuclideanSpace.single i' 1) * H2 i j s ω * H2 i' j s ω :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    have hb : ∀ j, (∑ i, ∑ i', fderiv ℝ (fderiv ℝ Fx) (X2 s ω) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1) * H2 i j s ω * H2 i' j s ω) =
        (Y s ω k * (C.g k (posPart (Y s ω)) * C.Γ j k) ^ 2
          - 2 * (Y s ω k * C.g k (posPart (Y s ω)) * C.Γ j k) * (C.g k (posPart (Y s ω)) * C.Γ j k))
          * Real.exp (-(Z s ω)) := by
      intro j
      have e0 : H2 0 j s ω = Y s ω k * C.g k (posPart (Y s ω)) * C.Γ j k := rfl
      have e1 : H2 1 j s ω = C.g k (posPart (Y s ω)) * C.Γ j k := by
        show C.g k (boxP 0 R (posPart (Y s ω))) * C.Γ j k = _
        rw [boxP_posPart_eq hbox]
      rw [sum2_bilin _ (fun i => H2 i j s ω), Fx_fderiv2, Fin.sum_univ_two,
        vec2_apply0, vec2_apply1, e0, e1, hX20, hX21]
    have ef : fR (Y s ω) = C.f k (posPart (Y s ω)) := by
      show C.f k (boxP 0 R (posPart (Y s ω))) = _
      rw [boxP_posPart_eq hbox]
    have eg : ∀ j, Hc j s ω = C.g k (posPart (Y s ω)) * C.Γ j k := fun j => by
      show C.g k (boxP 0 R (posPart (Y s ω))) * C.Γ j k = _
      rw [boxP_posPart_eq hbox]
    have e1 : b2 1 s ω = C.f k (posPart (Y s ω)) -
        (1 / 2) * ∑ j, (C.g k (posPart (Y s ω)) * C.Γ j k) ^ 2 := by
      show fR (Y s ω) - (1 / 2) * ∑ j, (Hc j s ω) ^ 2 = _
      rw [ef]; simp only [eg]
    have e0 : b2 0 s ω = Y s ω k * C.f k (posPart (Y s ω)) := rfl
    rw [hswap, Finset.sum_congr rfl fun j _ => hb j, Fin.sum_univ_two, e0, e1, Fx_fderiv,
      Fx_fderiv, hX20, hX21]
    have hsum : ∀ j, (Y s ω k * (C.g k (posPart (Y s ω)) * C.Γ j k) ^ 2
          - 2 * (Y s ω k * C.g k (posPart (Y s ω)) * C.Γ j k) * (C.g k (posPart (Y s ω)) * C.Γ j k))
          * Real.exp (-(Z s ω)) =
        -(Y s ω k * Real.exp (-(Z s ω))) * (C.g k (posPart (Y s ω)) * C.Γ j k) ^ 2 :=
      fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => hsum j, ← Finset.mul_sum]
    simp
    ring
  have hint : ∀ ω ∈ E, (∑ i, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ Fx (X2 u.toNNReal ω) (EuclideanSpace.single i 1) * b2 i u.toNNReal ω) +
      (1 / 2) * ∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ Fx) (X2 u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H2 i j u.toNNReal ω * H2 i' j u.toNNReal ω = 0 := by
    intro ω hω
    have hAi : ∀ i : Fin 2, Continuous fun u : ℝ =>
        fderiv ℝ Fx (X2 u.toNNReal ω) (EuclideanSpace.single i 1) * b2 i u.toNNReal ω :=
      fun i => ((hD1 i).comp ((hXc ω).comp continuous_real_toNNReal)).mul
        ((hb2c i ω).comp continuous_real_toNNReal)
    have hBi : ∀ (i i' : Fin 2) (j : Fin n), Continuous fun u : ℝ =>
        fderiv ℝ (fderiv ℝ Fx) (X2 u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H2 i j u.toNNReal ω * H2 i' j u.toNNReal ω :=
      fun i i' j => (((hD2 i i').comp ((hXc ω).comp continuous_real_toNNReal)).mul
          ((hH2c i j ω).comp continuous_real_toNNReal)).mul
          ((hH2c i' j ω).comp continuous_real_toNNReal)
    have hA : Continuous fun u : ℝ => ∑ i : Fin 2,
        fderiv ℝ Fx (X2 u.toNNReal ω) (EuclideanSpace.single i 1) * b2 i u.toNNReal ω :=
      continuous_finset_sum _ fun i _ => hAi i
    have hB2 : Continuous fun u : ℝ => (1 / 2 : ℝ) * ∑ i : Fin 2, ∑ i' : Fin 2, ∑ j : Fin n,
        fderiv ℝ (fderiv ℝ Fx) (X2 u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H2 i j u.toNNReal ω * H2 i' j u.toNNReal ω :=
      continuous_const.mul (continuous_finset_sum _ fun i _ => continuous_finset_sum _
        fun i' _ => continuous_finset_sum _ fun j _ => hBi i i' j)
    have s1 : (∑ i : Fin 2, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ Fx (X2 u.toNNReal ω) (EuclideanSpace.single i 1) * b2 i u.toNNReal ω) =
        ∫ u in (0 : ℝ)..t.val, ∑ i : Fin 2,
          fderiv ℝ Fx (X2 u.toNNReal ω) (EuclideanSpace.single i 1) * b2 i u.toNNReal ω :=
      integral_sum_cont (f := fun i u =>
        fderiv ℝ Fx (X2 u.toNNReal ω) (EuclideanSpace.single i 1) * b2 i u.toNNReal ω) _ hAi _ _
    have s2 : (∑ i : Fin 2, ∑ i' : Fin 2, ∑ j : Fin n, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ Fx) (X2 u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H2 i j u.toNNReal ω * H2 i' j u.toNNReal ω) =
        ∫ u in (0 : ℝ)..t.val, ∑ i : Fin 2, ∑ i' : Fin 2, ∑ j : Fin n,
          fderiv ℝ (fderiv ℝ Fx) (X2 u.toNNReal ω) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i' 1) * H2 i j u.toNNReal ω * H2 i' j u.toNNReal ω :=
      integral_sum3 (fun i i' j u => fderiv ℝ (fderiv ℝ Fx) (X2 u.toNNReal ω)
          (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) *
          H2 i j u.toNNReal ω * H2 i' j u.toNNReal ω) hBi _ _
    rw [s1, s2, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hA.intervalIntegrable _ _) (hB2.intervalIntegrable _ _)]
    have hz : ∀ u ∈ Set.uIcc (0 : ℝ) t.val, ((∑ i, fderiv ℝ Fx (X2 u.toNNReal ω)
        (EuclideanSpace.single i 1) * b2 i u.toNNReal ω) + (1 / 2) * ∑ i, ∑ i', ∑ j,
        fderiv ℝ (fderiv ℝ Fx) (X2 u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * H2 i j u.toNNReal ω * H2 i' j u.toNNReal ω) = 0 := by
      intro u hu
      rw [Set.uIcc_of_le t.2] at hu
      refine hpt ω hω _ ?_
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu.1]
      exact hu.2
    rw [intervalIntegral.integral_congr hz, intervalIntegral.integral_zero]
  filter_upwards [hito, ae_all_iff.2 hcan, hY0] with ω hito hcanω hY0ω
  intro hEω
  have hEω' : ω ∈ E := hEω
  have hKsum : ∑ i, ∑ j, K i j t ω = 0 := by
    rw [Fin.sum_univ_two, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j _ => by rw [hcanω j hEω']; ring
  have hfin : Fx (X2 t ω) = Fx (X2 0 ω) := by
    rw [hito, hKsum]; linarith only [hint ω hEω']
  have hY0k : Y 0 ω k = x k := by rw [hY0ω]
  simp only [Fx, hX20, hX21, hZ0, hY0k, neg_zero, Real.exp_zero, mul_one] at hfin
  rw [← hfin, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

/-- `lemma_3_1` clause 3: faces `ℝ^{I,◦}₊` are invariant for all times, almost surely. -/
theorem face_inv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Coeffs n) {B : ℝ≥0 → Ω → SDEState n} (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ faceOpen I) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) :
    ∀ᵐ ω ∂P, ∀ t, Y t ω ∈ faceOpen I := by
  have hrep : ∀ (k : Fin n) (R : ℕ), ∃ Z : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Z t ω) ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂P, (∀ s ≤ t, ∀ i, |Y s ω i| ≤ R) → Y t ω k = x k * Real.exp (Z t ω) :=
    fun k R => face_rep C hB hC hY k (Nat.cast_nonneg R)
  choose Z hZc hZ using hrep
  have hall : ∀ᵐ ω ∂P, ∀ (k : Fin n) (R : ℕ) (q : ℚ),
      (∀ s ≤ (q : ℝ).toNNReal, ∀ i, |Y s ω i| ≤ R) →
        Y ((q : ℝ).toNNReal) ω k = x k * Real.exp (Z k R ((q : ℝ).toNNReal) ω) := by
    rw [ae_all_iff]; intro k
    rw [ae_all_iff]; intro R
    rw [ae_all_iff]; intro q
    exact hZ k R _
  rw [faceOpen, mem_setOf_eq] at hx
  filter_upwards [hall] with ω hω t
  have hkey : ∀ k, ∃ c : ℝ, Y t ω k = x k * Real.exp c := by
    intro k
    set T : ℝ≥0 := t + 1
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hY.2.1 ω).continuousOn
    set R : ℕ := ⌈M⌉₊
    have hbd : ∀ s ≤ T, ∀ i, |Y s ω i| ≤ R := fun s hs i => by
      have h1 : ‖(Y s ω) i‖ ≤ ‖Y s ω‖ := PiLp.norm_apply_le _ _
      rw [Real.norm_eq_abs] at h1
      exact h1.trans ((hM s ⟨by positivity, hs⟩).trans (Nat.le_ceil M))
    have hcl : IsClosed {s : ℝ≥0 | Y s ω k = x k * Real.exp (Z k R s ω)} :=
      isClosed_eq (((continuous_apply k).comp (PiLp.continuous_ofLp 2 _)).comp (hY.2.1 ω))
        (continuous_const.mul (Real.continuous_exp.comp (hZc k R ω)))
    have hsub : Set.Iio T ∩ Set.range (fun q : ℚ => (q : ℝ).toNNReal) ⊆
        {s : ℝ≥0 | Y s ω k = x k * Real.exp (Z k R s ω)} := by
      rintro _ ⟨hs, q, rfl⟩
      exact hω k R q fun s hs' i => hbd s (hs'.trans (le_of_lt hs)) i
    have ht : t ∈ closure (Set.Iio T ∩ Set.range (fun q : ℚ => (q : ℝ).toNNReal)) :=
      denseRange_rat_toNNReal.open_subset_closure_inter isOpen_Iio
        (show t < T from lt_add_one t)
    exact ⟨_, hcl.closure_subset_iff.2 hsub ht⟩
  rw [faceOpen, mem_setOf_eq]
  refine ⟨fun i => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨c, hc⟩ := hkey i; rw [hc]; exact mul_nonneg (hx.1 i) (Real.exp_pos c).le
  · obtain ⟨c, hc⟩ := hkey i; rw [hc, hx.2.1 i hi, zero_mul]
  · obtain ⟨c, hc⟩ := hkey i; rw [hc]; exact mul_pos (hx.2.2 i hi) (Real.exp_pos c)

end QEface

end ItoLib

end FlatM_QE
-- ===== QF =====
section FlatM_QF
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QFgen
/-! Generic test function `F(x,y,a) = e^{-a} G(y)` along `(X, Y, A)`. -/
variable {d : ℕ}

/-- The `y`-block of a packed vector, as a continuous linear map. -/
noncomputable def yOfL : SDEState (d + d + 1) →L[ℝ] SDEState d :=
  haveI : ContinuousSMul ℝ (SDEState (d + d + 1)) := IsBoundedSMul.continuousSMul
  haveI : ContinuousSMul ℝ (SDEState d) := IsBoundedSMul.continuousSMul
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun k => v (iyc k))
      map_add' := fun u v => by ext k; simp
      map_smul' := fun r v => by ext k; simp }

@[simp] theorem yOfL_apply (v : SDEState (d + d + 1)) (k : Fin d) : yOfL v k = v (iyc k) := rfl

theorem yOfL_pack (x y : SDEState d) (a : ℝ) : yOfL (pack x y a) = y := by
  ext k; simp

theorem yOfL_line (x y : SDEState d) (a r : ℝ) (v : SDEState (d + d + 1)) :
    yOfL (pack x y a + r • v) = y + r • yOfL v := by
  rw [map_add, map_smul, yOfL_pack]

theorem iac_line (x y : SDEState d) (a r : ℝ) (v : SDEState (d + d + 1)) :
    (pack x y a + r • v) iac = a + r * v iac := by
  simp

theorem qf_norm_mono {ι : Type*} [Fintype ι] {u w : EuclideanSpace ℝ ι}
    (h : ∀ k, |u k| ≤ |w k|) : ‖u‖ ≤ ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h k) 2

/-- `F(v) = e^{-a} G(y)`. -/
noncomputable def FG (G : SDEState d → ℝ) (v : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-(v iac)) * G (yOfL v)

theorem FG_pack (G : SDEState d → ℝ) (x y : SDEState d) (a : ℝ) :
    FG G (pack x y a) = Real.exp (-a) * G y := by
  simp [FG, yOfL_pack]

theorem FG_contDiff {G : SDEState d → ℝ} (hG : ContDiff ℝ 2 G) : ContDiff ℝ 2 (FG G) := by
  unfold FG
  exact (Real.contDiff_exp.comp (coord_contDiff iac).neg).mul (hG.comp yOfL.contDiff)

theorem FG_fderiv {G : SDEState d → ℝ} (hG : ContDiff ℝ 2 G) (x y : SDEState d) (a : ℝ)
    (v : SDEState (d + d + 1)) :
    fderiv ℝ (FG G) (pack x y a) v =
      Real.exp (-a) * (fderiv ℝ G y (yOfL v) - v iac * G y) := by
  have hGd : Differentiable ℝ G := hG.differentiable two_ne_zero
  refine fderiv_eq_of_line ((FG_contDiff hG).differentiable two_ne_zero) _ _ ?_
  have e : (fun r : ℝ => FG G (pack x y a + r • v)) =
      fun r => Real.exp (-(a + r * v iac)) * G (y + r • yOfL v) := by
    funext r; simp only [FG, yOfL_line, iac_line]
  rw [e]
  have h1 : HasDerivAt (fun r : ℝ => Real.exp (-(a + r * v iac)))
      (Real.exp (-(a + 0 * v iac)) * (-(1 * v iac))) 0 :=
    (((hasDerivAt_id (0 : ℝ)).mul_const (v iac)).const_add a).neg.exp
  have h2 := line_hasDerivAt hGd y (yOfL v) 0
  have h3 : HasDerivAt (fun r : ℝ => Real.exp (-(a + r * v iac)) * G (y + r • yOfL v))
      (Real.exp (-a) * (-(v iac)) * G y + Real.exp (-a) * fderiv ℝ G y (yOfL v)) 0 := by
    have := h1.fun_mul h2
    simpa using this
  convert h3 using 1
  ring

theorem FG_fderiv2 {G : SDEState d → ℝ} (hG : ContDiff ℝ 2 G) (x y : SDEState d) (a : ℝ)
    (v : SDEState (d + d + 1)) (hv : v iac = 0) :
    fderiv ℝ (fderiv ℝ (FG G)) (pack x y a) v v =
      Real.exp (-a) * fderiv ℝ (fderiv ℝ G) y (yOfL v) (yOfL v) := by
  have hGd : Differentiable ℝ G := hG.differentiable two_ne_zero
  have e : (fun r : ℝ => FG G (pack x y a + r • v)) =
      fun r => Real.exp (-a) * G (y + r • yOfL v) := by
    funext r; simp only [FG, yOfL_line, iac_line, hv, mul_zero, add_zero]
  refine fderiv2_eq_of_line (FG_contDiff hG) _ _
    (φ' := fun s => Real.exp (-a) * fderiv ℝ G (y + s • yOfL v) (yOfL v)) (fun s => ?_) ?_
  · rw [e]; exact (line_hasDerivAt hGd y (yOfL v) s).const_mul _
  · exact (line_hasDerivAt2 hG y (yOfL v)).const_mul _

theorem FG_driftGen {G : SDEState d → ℝ} (hG : ContDiff ℝ 2 G) (κ : ℝ) (σx : SDEDiffusion d)
    (bx : SDEState d) (σy : SDEDiffusion d) (by' : SDEState d) (x y : SDEState d) (a : ℝ) :
    driftGen (FG G) κ σx bx σy by' x y a = Real.exp (-a) * (fderiv ℝ G y by' +
      (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ G) y (scol σy j) (scol σy j) - κ * G y) := by
  unfold driftGen
  rw [FG_fderiv hG, yOfL_pack, pack_iac]
  simp only [FG_fderiv2 hG x y a _ (pack_iac _ _ _), yOfL_pack]
  rw [← Finset.mul_sum]; ring

theorem FG_integrand_le {G : SDEState d → ℝ} (hG : ContDiff ℝ 2 G) (x y : SDEState d) {a : ℝ}
    (ha : 0 ≤ a) (i : Fin (d + d + 1)) (u w : SDEState d) :
    |fderiv ℝ (FG G) (pack x y a) (EuclideanSpace.single i 1) * pack u w 0 i| ≤
      ‖fderiv ℝ G y‖ * ‖w‖ := by
  set c : ℝ := pack u w 0 i with hc
  have hs : fderiv ℝ (FG G) (pack x y a) (EuclideanSpace.single i 1) * c =
      fderiv ℝ (FG G) (pack x y a) (EuclideanSpace.single i c) := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul]
    congr 1; ext k; simp [EuclideanSpace.single_apply]
  have hiac : (EuclideanSpace.single i c : SDEState (d + d + 1)) iac = 0 := by
    rw [EuclideanSpace.single_apply]
    split_ifs with h
    · rw [hc, ← h]; simp
    · rfl
  have hy : ‖yOfL (EuclideanSpace.single i c : SDEState (d + d + 1))‖ ≤ ‖w‖ := by
    refine qf_norm_mono fun k => ?_
    rw [yOfL_apply, EuclideanSpace.single_apply]
    split_ifs with h
    · rw [hc, ← h]; simp
    · simp
  rw [hs, FG_fderiv hG, hiac, zero_mul, sub_zero, abs_mul, abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
  calc Real.exp (-a) * |fderiv ℝ G y (yOfL (EuclideanSpace.single i c))|
      ≤ 1 * |fderiv ℝ G y (yOfL (EuclideanSpace.single i c))| :=
        mul_le_mul_of_nonneg_right he (abs_nonneg _)
    _ ≤ ‖fderiv ℝ G y‖ * ‖yOfL (EuclideanSpace.single i c : SDEState (d + d + 1))‖ := by
        rw [one_mul, ← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖fderiv ℝ G y‖ * ‖w‖ := mul_le_mul_of_nonneg_left hy (norm_nonneg _)

/-- Local version of `fderiv2_eq_of_line`. -/
theorem fderiv2_eq_of_line_loc {f : SDEState d → ℝ} (hf : ContDiff ℝ 2 f) (u v : SDEState d)
    {φ' : ℝ → ℝ} {c : ℝ}
    (h1 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (fun r : ℝ => f (u + r • v)) (φ' s) s)
    (h2 : HasDerivAt φ' c 0) :
    fderiv ℝ (fderiv ℝ f) u v v = c := by
  have hdf : Differentiable ℝ f := hf.differentiable two_ne_zero
  have e : (fun r : ℝ => fderiv ℝ f (u + r • v) v) =ᶠ[𝓝 0] φ' :=
    h1.mono fun s hs => (line_hasDerivAt hdf u v s).unique hs
  exact (line_hasDerivAt2 hf u v).unique (h2.congr_of_eventuallyEq e)

theorem deriv_nonneg_of_mono {f : ℝ → ℝ} {f' x : ℝ} (hf : Monotone f) (h : HasDerivAt f f' x) :
    0 ≤ f' := by
  refine ge_of_tendsto (hasDerivAt_iff_tendsto_slope.1 h)
    (eventually_nhdsWithin_of_forall fun y hy => ?_)
  rw [slope_def_field]
  rcases lt_or_gt_of_ne hy with h1 | h1
  · exact div_nonneg_of_nonpos (by linarith [hf h1.le]) (by linarith)
  · exact div_nonneg (by linarith [hf h1.le]) (by linarith)

end QFgen

section QFsat
/-! The concave saturation `h_m(u) = ∫₀ᵘ (1 - st(s - m)) ds`. -/

noncomputable def hsat (m u : ℝ) : ℝ := ∫ s in (0 : ℝ)..u, (1 - Real.smoothTransition (s - m))

theorem hsat_integrand_continuous (m : ℝ) :
    Continuous fun s : ℝ => 1 - Real.smoothTransition (s - m) :=
  continuous_const.sub (Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const))

theorem hsat_hasDerivAt (m u : ℝ) :
    HasDerivAt (hsat m) (1 - Real.smoothTransition (u - m)) u :=
  ((hsat_integrand_continuous m).integral_hasStrictDerivAt 0 u).hasDerivAt

theorem hsat_deriv (m : ℝ) : deriv (hsat m) = fun u => 1 - Real.smoothTransition (u - m) :=
  funext fun u => (hsat_hasDerivAt m u).deriv

theorem hsat_contDiff (m : ℝ) : ContDiff ℝ 2 (hsat m) := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl]
  refine contDiff_succ_iff_deriv.2 ⟨fun u => (hsat_hasDerivAt m u).differentiableAt,
    fun h => by simp at h, ?_⟩
  rw [hsat_deriv]
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem hsat_d2 (m u : ℝ) :
    HasDerivAt (fun v => 1 - Real.smoothTransition (v - m))
      (-(deriv Real.smoothTransition (u - m))) u := by
  have h : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (u - m)) (u - m) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero |>.differentiableAt
      |>.hasDerivAt
  have h2 := (h.comp u ((hasDerivAt_id u).sub_const m)).const_sub 1
  simpa using h2

theorem hsat_d2_nonpos (m u : ℝ) : -(deriv Real.smoothTransition (u - m)) ≤ 0 := by
  have h : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (u - m)) (u - m) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero |>.differentiableAt
      |>.hasDerivAt
  linarith [deriv_nonneg_of_mono Real.smoothTransition.monotone h]

theorem hsat_d1_mem (m u : ℝ) :
    0 ≤ 1 - Real.smoothTransition (u - m) ∧ 1 - Real.smoothTransition (u - m) ≤ 1 :=
  ⟨by linarith [Real.smoothTransition.le_one (u - m)],
    by linarith [Real.smoothTransition.nonneg (u - m)]⟩

theorem hsat_eq_self {m u : ℝ} (hm : 0 ≤ m) (hu : u ≤ m) : hsat m u = u := by
  unfold hsat
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) fun s hs => ?_]
  · simp
  · have : s ≤ m := by
      rcases Set.mem_uIcc.1 hs with h | h
      · linarith [h.2]
      · linarith [h.2]
    simp [Real.smoothTransition.zero_of_nonpos (by linarith : s - m ≤ 0)]

theorem hsat_const {m u : ℝ} (hu : m + 1 ≤ u) : hsat m u = hsat m (m + 1) := by
  unfold hsat
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => 1 - Real.smoothTransition (s - m))
      MeasureTheory.volume a b := fun a b => (hsat_integrand_continuous m).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (m + 1)) (hi (m + 1) u)]
  have h0 : ∫ s in (m + 1)..u, (1 - Real.smoothTransition (s - m)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · simp
    · rw [Set.uIcc_of_le hu] at hs
      simp [Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ s - m)]
  rw [h0, add_zero]

theorem hsat_nonneg (m : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ hsat m u :=
  intervalIntegral.integral_nonneg hu fun s _ => (hsat_d1_mem m s).1

theorem hsat_le_self (m : ℝ) {u : ℝ} (hu : 0 ≤ u) : hsat m u ≤ u := by
  unfold hsat
  calc _ ≤ ∫ _s in (0 : ℝ)..u, (1 : ℝ) :=
        intervalIntegral.integral_mono_on hu ((hsat_integrand_continuous m).intervalIntegrable _ _)
          intervalIntegrable_const fun s _ => (hsat_d1_mem m s).2
    _ = u := by simp

theorem hsat_d1_mul_le (m : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    (1 - Real.smoothTransition (u - m)) * u ≤ hsat m u := by
  unfold hsat
  calc (1 - Real.smoothTransition (u - m)) * u
      = ∫ _s in (0 : ℝ)..u, (1 - Real.smoothTransition (u - m)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
    _ ≤ _ := intervalIntegral.integral_mono_on hu intervalIntegrable_const
          ((hsat_integrand_continuous m).intervalIntegrable _ _) fun s hs => by
            have := Real.smoothTransition.monotone (by linarith [hs.2] : s - m ≤ u - m)
            linarith

end QFsat

section QFell
/-! The logarithm `ℓ = log(1 + cᵀy) - Σ pᵢ log yᵢ` of `V`, its line derivatives, and bounds. -/
variable {n : ℕ}
open StochKolmogorov.Persist

noncomputable def Sf (c y : SDEState n) : ℝ := 1 + ∑ i, c i * y i
noncomputable def ellf (c p y : SDEState n) : ℝ := Real.log (Sf c y) - ∑ i, p i * Real.log (y i)
noncomputable def ell1 (c p y w : SDEState n) : ℝ :=
  (∑ i, c i * w i) / Sf c y - ∑ i, p i * (w i / y i)
noncomputable def ell2 (c p y w : SDEState n) : ℝ :=
  -((∑ i, c i * w i) ^ 2 / Sf c y ^ 2) + ∑ i, p i * (w i ^ 2 / y i ^ 2)

theorem line_apply (y w : SDEState n) (r : ℝ) (i : Fin n) : (y + r • w) i = y i + r * w i := by
  simp

theorem Sf_line (c y w : SDEState n) (r : ℝ) :
    Sf c (y + r • w) = Sf c y + r * ∑ i, c i * w i := by
  simp only [Sf, line_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [add_assoc]; congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

theorem one_le_Sf {c y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ orthant n) :
    1 ≤ Sf c y := by
  unfold Sf
  have : 0 ≤ ∑ i, c i * y i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hy i)
  linarith

theorem openOrthant_sub {y : SDEState n} (hy : y ∈ openOrthant n) : y ∈ orthant n :=
  fun i => (hy i).le

theorem openOrthant_isOpen : IsOpen (openOrthant n) := by
  have : openOrthant n = ⋂ i, {x : SDEState n | 0 < x i} := by ext x; simp [openOrthant]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)

theorem ell_hasDerivAt {c p y w : SDEState n} {s : ℝ} (hS : 0 < Sf c (y + s • w))
    (hy : ∀ i, 0 < (y + s • w) i) :
    HasDerivAt (fun r : ℝ => ellf c p (y + r • w)) (ell1 c p (y + s • w) w) s := by
  have h1 : HasDerivAt (fun r : ℝ => Sf c (y + r • w)) (∑ i, c i * w i) s := by
    simp only [Sf_line]
    simpa using ((hasDerivAt_id s).mul_const (∑ i, c i * w i)).const_add (Sf c y)
  have h2 : ∀ i, HasDerivAt (fun r : ℝ => (y + r • w) i) (w i) s := fun i => by
    simp only [line_apply]
    simpa using ((hasDerivAt_id s).mul_const (w i)).const_add (y i)
  have h3 := (h1.log hS.ne').sub
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ((h2 i).log (hy i).ne').const_mul (p i))
  exact h3

theorem ell1_hasDerivAt {c p y w : SDEState n} {s : ℝ} (hS : 0 < Sf c (y + s • w))
    (hy : ∀ i, 0 < (y + s • w) i) :
    HasDerivAt (fun r : ℝ => ell1 c p (y + r • w) w) (ell2 c p (y + s • w) w) s := by
  have h1 : HasDerivAt (fun r : ℝ => Sf c (y + r • w)) (∑ i, c i * w i) s := by
    simp only [Sf_line]
    simpa using ((hasDerivAt_id s).mul_const (∑ i, c i * w i)).const_add (Sf c y)
  have h2 : ∀ i, HasDerivAt (fun r : ℝ => (y + r • w) i) (w i) s := fun i => by
    simp only [line_apply]
    simpa using ((hasDerivAt_id s).mul_const (w i)).const_add (y i)
  have h3 := ((hasDerivAt_const s (∑ i, c i * w i)).div h1 hS.ne').sub
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ((hasDerivAt_const s (w i)).div (h2 i) (hy i).ne').const_mul (p i))
  refine h3.congr_deriv ?_
  have e : ∀ i ∈ Finset.univ, p i * ((0 * (y + s • w) i - w i * w i) / (y + s • w) i ^ 2) =
      -(p i * (w i ^ 2 / (y + s • w) i ^ 2)) := fun i _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_neg_distrib]
  unfold ell2; ring

/-- `log yᵢ ≤ log S - log cᵢ`. -/
theorem log_coord_le {c y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ openOrthant n)
    (i : Fin n) : Real.log (y i) ≤ Real.log (Sf c y) - Real.log (c i) := by
  have hS := one_le_Sf hc (openOrthant_sub hy)
  have hle : c i * y i ≤ Sf c y := by
    unfold Sf
    have := Finset.single_le_sum (f := fun j => c j * y j)
      (fun j _ => mul_nonneg (hc j).le (hy j).le) (Finset.mem_univ i)
    simp only at this; linarith
  have := Real.log_le_log (mul_pos (hc i) (hy i)) hle
  rw [Real.log_mul (hc i).ne' (hy i).ne'] at this
  linarith

/-- The constant `A = 2 Σ |pᵢ log cᵢ|`. -/
noncomputable def Acst (c p : SDEState n) : ℝ := 2 * ∑ i, |p i * Real.log (c i)|

theorem ellf_ge_S {c p y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ openOrthant n)
    (hp : ∀ i, 0 ≤ p i) :
    (1 - ∑ i, p i) * Real.log (Sf c y) - Acst c p ≤ ellf c p y := by
  have h1 : ∑ i, p i * Real.log (y i) ≤ ∑ i, p i * (Real.log (Sf c y) - Real.log (c i)) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (log_coord_le hc hy i) (hp i)
  have h2 : ∑ i, p i * (Real.log (Sf c y) - Real.log (c i)) =
      (∑ i, p i) * Real.log (Sf c y) - ∑ i, p i * Real.log (c i) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : -(∑ i, p i * Real.log (c i)) ≤ Acst c p := by
    unfold Acst
    have := Finset.abs_sum_le_sum_abs (fun i => p i * Real.log (c i)) Finset.univ
    have h0 : 0 ≤ ∑ i, |p i * Real.log (c i)| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith [neg_abs_le (∑ i, p i * Real.log (c i))]
  unfold ellf; linarith

theorem ellf_ge_coord {c p y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ openOrthant n)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i ≤ 1) (k : Fin n) :
    -(p k * Real.log (y k)) - Acst c p ≤ ellf c p y := by
  have hS0 : 0 ≤ Real.log (Sf c y) := Real.log_nonneg (one_le_Sf hc (openOrthant_sub hy))
  set q : Fin n → ℝ := fun i => p i * (Real.log (Sf c y) - Real.log (c i) - Real.log (y i))
  have hq : ∀ i, 0 ≤ q i := fun i =>
    mul_nonneg (hp i) (by linarith [log_coord_le hc hy i])
  have hqk : q k ≤ ∑ i, q i := Finset.single_le_sum (fun i _ => hq i) (Finset.mem_univ k)
  have hsum : ∑ i, q i = (∑ i, p i) * Real.log (Sf c y) - ∑ i, p i * Real.log (c i)
      - ∑ i, p i * Real.log (y i) := by
    simp only [q, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hA1 : |p k * Real.log (c k)| ≤ ∑ i, |p i * Real.log (c i)| :=
    Finset.single_le_sum (f := fun i => |p i * Real.log (c i)|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ k)
  have hA2 : -(∑ i, p i * Real.log (c i)) ≤ ∑ i, |p i * Real.log (c i)| := by
    have := Finset.abs_sum_le_sum_abs (fun i => p i * Real.log (c i)) Finset.univ
    linarith [neg_abs_le (∑ i, p i * Real.log (c i))]
  have hk1 : p k * Real.log (c k) ≤ |p k * Real.log (c k)| := le_abs_self _
  have hpk : p k ≤ ∑ i, p i := Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ k)
  have hprod : 0 ≤ (1 - ∑ i, p i + p k) * Real.log (Sf c y) :=
    mul_nonneg (by linarith [hp k]) hS0
  have hqk' : q k = p k * (Real.log (Sf c y) - Real.log (c k) - Real.log (y k)) := rfl
  unfold ellf Acst
  linarith

theorem coord_le_Sf {c y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ orthant n) (i : Fin n) :
    c i * y i ≤ Sf c y := by
  unfold Sf
  have := Finset.single_le_sum (f := fun j => c j * y j)
    (fun j _ => mul_nonneg (hc j).le (hy j)) (Finset.mem_univ i)
  simp only at this; linarith

noncomputable def Uf (δ : ℝ) (c p y : SDEState n) : ℝ := Real.exp (δ * ellf c p y)
noncomputable def Lcst (δ m : ℝ) : ℝ := Real.log (m + 1) / δ
noncomputable def etaK (δ m : ℝ) (c p : SDEState n) (i : Fin n) : ℝ :=
  Real.exp (-(Lcst δ m + Acst c p) / p i)
noncomputable def RSK (δ m : ℝ) (c p : SDEState n) : ℝ :=
  Real.exp ((Lcst δ m + Acst c p) / (1 - ∑ i, p i))
def boxK (δ m : ℝ) (c p : SDEState n) : Set (SDEState n) :=
  {z | ∀ i, etaK δ m c p i ≤ z i ∧ z i ≤ RSK δ m c p / c i}

theorem boxK_sub (δ m : ℝ) (c p : SDEState n) : boxK δ m c p ⊆ openOrthant n :=
  fun z hz i => lt_of_lt_of_le (Real.exp_pos _) (hz i).1

theorem boxK_isClosed (δ m : ℝ) (c p : SDEState n) : IsClosed (boxK δ m c p) := by
  have : boxK δ m c p = ⋂ i, ({z : SDEState n | etaK δ m c p i ≤ z i} ∩
      {z : SDEState n | z i ≤ RSK δ m c p / c i}) := by
    ext z; simp [boxK]
  rw [this]
  exact isClosed_iInter fun i => (isClosed_le continuous_const (PiLp.continuous_apply 2 _ i)).inter
    (isClosed_le (PiLp.continuous_apply 2 _ i) continuous_const)

theorem boxK_isCompact (δ m : ℝ) (c p : SDEState n) : IsCompact (boxK δ m c p) := by
  have : boxK δ m c p = (WithLp.toLp 2) ''
      (Set.univ.pi fun i => Set.Icc (etaK δ m c p i) (RSK δ m c p / c i)) := by
    ext z
    refine ⟨fun hz => ⟨WithLp.ofLp z, fun i _ => hz i, by simp⟩, ?_⟩
    rintro ⟨x, hx, rfl⟩ i
    exact hx i (Set.mem_univ i)
  rw [this]
  exact (isCompact_univ_pi fun i => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

theorem U_big_of_out {δ m : ℝ} {c p z : SDEState n} (hδ : 0 < δ) (hm : 0 ≤ m)
    (hc : c ∈ openOrthant n) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1)
    (hz : z ∈ openOrthant n) (hout : z ∉ boxK δ m c p) : m + 1 ≤ Uf δ c p z := by
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hp i).le
  have hL : Lcst δ m ≤ ellf c p z := by
    simp only [boxK, Set.mem_setOf_eq, not_forall, not_and_or, not_le] at hout
    obtain ⟨i, hi | hi⟩ := hout
    · have h1 := Real.log_lt_log (hz i) hi
      simp only [etaK, Real.log_exp] at h1
      have h2 : p i * Real.log (z i) < -(Lcst δ m + Acst c p) := by
        have := mul_lt_mul_of_pos_left h1 (hp i)
        rwa [mul_div_cancel₀ _ (hp i).ne'] at this
      linarith [ellf_ge_coord hc hz hp0 hp1.le i]
    · have hci := hc i
      have h0 : RSK δ m c p < Sf c z := by
        have := coord_le_Sf hc (openOrthant_sub hz) i
        have h3 : RSK δ m c p < c i * z i := by
          rw [div_lt_iff₀ hci] at hi; linarith
        linarith
      have h1 := Real.log_lt_log (Real.exp_pos _) h0
      simp only [RSK, Real.log_exp] at h1
      have hq : 0 < 1 - ∑ i, p i := by linarith
      have h2 : Lcst δ m + Acst c p < (1 - ∑ i, p i) * Real.log (Sf c z) := by
        have := mul_lt_mul_of_pos_left h1 hq
        rwa [mul_div_cancel₀ _ hq.ne'] at this
      linarith [ellf_ge_S hc hz hp0]
  have h1 : Real.log (m + 1) ≤ δ * ellf c p z := by
    have := mul_le_mul_of_nonneg_left hL hδ.le
    rwa [Lcst, mul_div_cancel₀ _ hδ.ne'] at this
  have := Real.exp_le_exp.2 h1
  rwa [Real.exp_log (by linarith)] at this

open scoped Classical in
noncomputable def Gm (δ m : ℝ) (c p y : SDEState n) : ℝ :=
  if y ∈ openOrthant n then hsat m (Uf δ c p y) else hsat m (m + 1)

theorem Gm_out {δ m : ℝ} {c p z : SDEState n} (hδ : 0 < δ) (hm : 0 ≤ m)
    (hc : c ∈ openOrthant n) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1)
    (hout : z ∉ boxK δ m c p) : Gm δ m c p z = hsat m (m + 1) := by
  by_cases hz : z ∈ openOrthant n
  · rw [Gm, if_pos hz]; exact hsat_const (U_big_of_out hδ hm hc hp hp1 hz hout)
  · rw [Gm, if_neg hz]

theorem Gm_nonneg {δ m : ℝ} (hm : 0 ≤ m) (c p z : SDEState n) : 0 ≤ Gm δ m c p z := by
  unfold Gm; split_ifs
  · exact hsat_nonneg m (Real.exp_pos _).le
  · exact hsat_nonneg m (by linarith)

theorem Sf_contDiff (c : SDEState n) : ContDiff ℝ 2 (Sf c) :=
  contDiff_const.add (ContDiff.sum fun i _ => contDiff_const.mul (coord_contDiff i))

theorem Uf_contDiffAt {δ : ℝ} {c p z : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ openOrthant n) : ContDiffAt ℝ 2 (Uf δ c p) z := by
  have hS : ContDiffAt ℝ 2 (fun y => Real.log (Sf c y)) z :=
    (Sf_contDiff c).contDiffAt.log (by linarith [one_le_Sf hc (openOrthant_sub hz)])
  have hl : ContDiffAt ℝ 2 (fun y : SDEState n => ∑ i, p i * Real.log (y i)) z :=
    ContDiffAt.sum fun i _ => contDiffAt_const.mul
      ((coord_contDiff i).contDiffAt.log (hz i).ne')
  exact Real.contDiff_exp.contDiffAt.comp z (contDiffAt_const.mul (hS.sub hl))

theorem Gm_eq_nhds {δ m : ℝ} {c p z : SDEState n} (hz : z ∈ openOrthant n) :
    Gm δ m c p =ᶠ[𝓝 z] fun y => hsat m (Uf δ c p y) :=
  Filter.eventually_of_mem (openOrthant_isOpen.mem_nhds hz) fun y hy => by rw [Gm, if_pos hy]

theorem Gm_const_nhds {δ m : ℝ} {c p z : SDEState n} (hδ : 0 < δ) (hm : 0 ≤ m)
    (hc : c ∈ openOrthant n) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1)
    (hz : z ∉ boxK δ m c p) : Gm δ m c p =ᶠ[𝓝 z] fun _ => hsat m (m + 1) :=
  Filter.eventually_of_mem ((boxK_isClosed δ m c p).isOpen_compl.mem_nhds hz) fun y hy =>
    Gm_out hδ hm hc hp hp1 hy

theorem Gm_contDiff {δ m : ℝ} {c p : SDEState n} (hδ : 0 < δ) (hm : 0 ≤ m)
    (hc : c ∈ openOrthant n) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1) :
    ContDiff ℝ 2 (Gm δ m c p) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ openOrthant n
  · exact ((hsat_contDiff m).contDiffAt.comp z (Uf_contDiffAt hc hz)).congr_of_eventuallyEq
      (Gm_eq_nhds hz)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (Gm_const_nhds hδ hm hc hp hp1 fun h => hz (boxK_sub δ m c p h))

/-- `D G = 0` off the box. -/
theorem Gm_fderiv_out {δ m : ℝ} {c p z : SDEState n} (hδ : 0 < δ) (hm : 0 ≤ m)
    (hc : c ∈ openOrthant n) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1)
    (hz : z ∉ boxK δ m c p) :
    fderiv ℝ (Gm δ m c p) z = 0 ∧ fderiv ℝ (fderiv ℝ (Gm δ m c p)) z = 0 := by
  have h1 : fderiv ℝ (Gm δ m c p) =ᶠ[𝓝 z] fun _ => 0 := by
    have hU : ∀ᶠ y in 𝓝 z, y ∉ boxK δ m c p :=
      (boxK_isClosed δ m c p).isOpen_compl.mem_nhds hz
    refine hU.mono fun y hy => ?_
    rw [(Gm_const_nhds hδ hm hc hp hp1 hy).fderiv_eq]
    exact fderiv_const_apply _
  refine ⟨h1.eq_of_nhds, ?_⟩
  rw [h1.fderiv_eq]
  exact fderiv_const_apply _

theorem line_eventually {z w : SDEState n} (hz : z ∈ openOrthant n) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ r in 𝓝 s, z + r • w ∈ openOrthant n := by
  have ho : IsOpen {s : ℝ | z + s • w ∈ openOrthant n} :=
    openOrthant_isOpen.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : (0 : ℝ) ∈ {s : ℝ | z + s • w ∈ openOrthant n} := by simpa using hz
  exact Filter.eventually_of_mem (ho.mem_nhds h0) fun s hs => ho.mem_nhds hs

noncomputable def G1f (δ m : ℝ) (c p y w : SDEState n) : ℝ :=
  (1 - Real.smoothTransition (Uf δ c p y - m)) * (Uf δ c p y * (δ * ell1 c p y w))

noncomputable def G2f (δ m : ℝ) (c p y w : SDEState n) : ℝ :=
  -(deriv Real.smoothTransition (Uf δ c p y - m)) * (Uf δ c p y * (δ * ell1 c p y w)) *
      (Uf δ c p y * (δ * ell1 c p y w)) +
    (1 - Real.smoothTransition (Uf δ c p y - m)) *
      (Uf δ c p y * (δ * ell1 c p y w) * (δ * ell1 c p y w) + Uf δ c p y * (δ * ell2 c p y w))

theorem Gm_line {δ m : ℝ} {c p z w : SDEState n} (hc : c ∈ openOrthant n) {s : ℝ}
    (hs : ∀ᶠ r in 𝓝 s, z + r • w ∈ openOrthant n) :
    HasDerivAt (fun r : ℝ => Gm δ m c p (z + r • w)) (G1f δ m c p (z + s • w) w) s := by
  have hy : z + s • w ∈ openOrthant n := hs.self_of_nhds
  have hS : 0 < Sf c (z + s • w) := by linarith [one_le_Sf hc (openOrthant_sub hy)]
  have hU := ((ell_hasDerivAt (p := p) hS hy).const_mul δ).exp
  have h := (hsat_hasDerivAt m (Uf δ c p (z + s • w))).comp s hU
  refine HasDerivAt.congr_of_eventuallyEq h (hs.mono fun r hr => ?_)
  show Gm δ m c p (z + r • w) = hsat m (Uf δ c p (z + r • w))
  rw [Gm, if_pos hr]

theorem G1f_line {δ m : ℝ} {c p z w : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ openOrthant n) :
    HasDerivAt (fun s : ℝ => G1f δ m c p (z + s • w) w) (G2f δ m c p z w) 0 := by
  have hy : z + (0 : ℝ) • w ∈ openOrthant n := by simpa using hz
  have hS : 0 < Sf c (z + (0 : ℝ) • w) := by linarith [one_le_Sf hc (openOrthant_sub hy)]
  have hU := ((ell_hasDerivAt (p := p) hS hy).const_mul δ).exp
  have hl1 := ell1_hasDerivAt (p := p) hS hy
  have hA := (hsat_d2 m (Uf δ c p (z + (0 : ℝ) • w))).comp 0 hU
  have hB := hU.fun_mul (hl1.const_mul δ)
  have h := hA.fun_mul hB
  simp only [zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  unfold G2f Uf; simp only [Function.comp_apply, zero_smul, add_zero]
  try ring

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

theorem posPart_self {z : SDEState n} (hz : z ∈ orthant n) : posPart z = z := by
  ext i
  simp only [StochKolmogorov.Persist.posPart, PiLp.toLp_apply]
  exact max_eq_left (hz i)

theorem quad_sig (Γ : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ j, (∑ i, v i * Γ j i) ^ 2 = ∑ i, ∑ i', v i * v i' * (Γ.transpose * Γ) i i' := by
  simp_rw [sq, Finset.sum_mul_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j _ => ?_
  try ring

theorem diag_sig (Γ : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ j, ∑ i, v i * Γ j i ^ 2 = ∑ i, v i * (Γ.transpose * Γ) i i := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `cBracket` in terms of `aᵢ = cᵢ zᵢ / S`. -/
theorem cBracket_form (C : Coeffs n) {c z : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ orthant n) :
    cBracket C c z = ∑ i, c i * z i / Sf c z * C.f i z -
      (1 / 2) * ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) *
        C.sig i i' := by
  have hS : Sf c z ≠ 0 := by linarith [one_le_Sf hc hz]
  unfold cBracket
  have e1 : (∑ i, c i * z i * C.f i z) / (1 + ∑ i, c i * z i) =
      ∑ i, c i * z i / Sf c z * C.f i z := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by show _ / Sf c z = _; ring
  have e2 : (∑ i, ∑ j, C.sig i j * c i * c j * z i * z j * C.g i z * C.g j z) /
      (1 + ∑ i, c i * z i) ^ 2 = ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) *
        (c i' * z i' / Sf c z * C.g i' z) * C.sig i i' := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by show _ / (Sf c z) ^ 2 = _; ring
  rw [e1, mul_div_assoc, e2]
  try ring

theorem a_mem {c z : SDEState n} (hc : c ∈ openOrthant n) (hz : z ∈ orthant n) (i : Fin n) :
    0 ≤ c i * z i / Sf c z ∧ c i * z i / Sf c z ≤ 1 := by
  have hS := one_le_Sf hc hz
  refine ⟨div_nonneg (mul_nonneg (hc i).le (hz i)) (by linarith), ?_⟩
  rw [div_le_one (by linarith)]
  exact coord_le_Sf hc hz i

theorem dsum_le (u : Fin n → ℝ) (sig : Fin n → Fin n → ℝ) (i : Fin n) :
    |u i * u i * sig i i| ≤ ∑ i', |u i * u i' * sig i i'| :=
  Finset.single_le_sum (f := fun i' => |u i * u i' * sig i i'|) (fun _ _ => abs_nonneg _)
    (Finset.mem_univ i)

/-- Lower bound of the bracket used for `δ₀ < 1`. -/
theorem cBracket_ge (C : Coeffs n) {c z : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ orthant n) :
    -(∑ i, |C.f i z|) - (1 / 2) * ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| ≤ cBracket C c z := by
  rw [cBracket_form C hc hz]
  have h1 : -(∑ i, |C.f i z|) ≤ ∑ i, c i * z i / Sf c z * C.f i z := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨h0, h1⟩ := a_mem hc hz i
    have : |c i * z i / Sf c z * C.f i z| ≤ |C.f i z| := by
      rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
    linarith [neg_abs_le (c i * z i / Sf c z * C.f i z)]
  have h2 : ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) *
      C.sig i i' ≤ ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
    obtain ⟨a0, a1⟩ := a_mem hc hz i
    obtain ⟨b0, b1⟩ := a_mem hc hz i'
    have e : (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) * C.sig i i' =
        (c i * z i / Sf c z * (c i' * z i' / Sf c z)) * (C.g i z * C.g i' z * C.sig i i') := by ring
    rw [e]
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_of_nonneg (mul_nonneg a0 b0)]
    exact mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀ a1 b0 b1)
  linarith

/-- `δ₀ < 1`, from Assumption 1.1 at a far point and (3.2). -/
theorem delta0_lt_one (hn : 0 < n) {C : Coeffs n} {c : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) : δ₀ < 1 := by
  obtain ⟨-, -, hc, hγ, ε, hε, R, hR⟩ := hA
  obtain ⟨hδ0, hδγ, hδg⟩ := hδ
  by_contra h1
  push_neg at h1
  set i0 : Fin n := ⟨0, hn⟩
  set x : SDEState n := EuclideanSpace.single i0 (|R| + 1) with hx
  have hxo : x ∈ orthant n := fun j => by
    rw [hx, EuclideanSpace.single_apply]; split_ifs <;> positivity
  have hl : R ≤ l1 x := by
    unfold l1
    rw [Finset.sum_eq_single i0 (fun j _ hj => by simp [hx, EuclideanSpace.single_apply, hj])
      (by simp)]
    rw [show x i0 = |R| + 1 by simp [hx], abs_of_pos (by positivity)]
    linarith [le_abs_self R]
  have hA1 := hR x hxo hl
  have hD := hδg x hxo
  have hcb := cBracket_ge C hc hxo
  set F := ∑ i, |C.f i x|
  set T := ∑ i, ∑ i', |C.g i x * C.g i' x * C.sig i i'|
  set Gs := ∑ i, C.g i x ^ 2
  have hF : 0 ≤ F := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => abs_nonneg _
  have hG : 0 ≤ Gs := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsplit : ∑ i, (|C.f i x| + C.g i x ^ 2) = F + Gs := Finset.sum_add_distrib
  have hT' : 3 * δ₀ * T = 3 * δ₀ * ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| := rfl
  rw [hsplit] at hA1
  have hγ1 : 1 ≤ γb := by linarith
  have p1 : F ≤ γb * F := le_mul_of_one_le_left hF hγ1
  have p2 : T ≤ δ₀ * T := le_mul_of_one_le_left hT h1
  nlinarith

theorem p_le_l1 {p : SDEState n} (hp : p ∈ openOrthant n) (i : Fin n) : p i ≤ l1 p := by
  unfold l1
  have := Finset.single_le_sum (f := fun j => |p j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  simp only at this
  rwa [abs_of_pos (hp i)] at this

theorem sum_p_eq {p : SDEState n} (hp : p ∈ openOrthant n) : ∑ i, p i = l1 p := by
  unfold l1; exact Finset.sum_congr rfl fun i _ => (abs_of_pos (hp i)).symm

/-- The generator inequality for `V^δ₀` (3.5): `ℓ₁(b) + ½ Σⱼ (δ₀ ℓ₁(σⱼ)² + ℓ₂(σⱼ)) ≤ bracket35`. -/
theorem Q_le (C : Coeffs n) {c p z : SDEState n} {γb δ₀ : ℝ} (hc : c ∈ openOrthant n)
    (hz : z ∈ openOrthant n) (hp : p ∈ openOrthant n) (hpl : l1 p ≤ δ₀) (hδ1 : δ₀ < 1)
    (hδ0 : 0 < δ₀) (hγ : 0 < γb) :
    ell1 c p z (drift C (0, z)) + (1 / 2) * ∑ j, (δ₀ * ell1 c p z (scol (diffusion C (0, z)) j) ^ 2
      + ell2 c p z (scol (diffusion C (0, z)) j)) ≤ bracket35 C c γb δ₀ z := by
  have hzo := openOrthant_sub hz
  have hpp : posPart z = z := posPart_self hzo
  have hS : Sf c z ≠ 0 := by linarith [one_le_Sf hc hzo]
  have hb : ∀ i, (drift C (0, z)) i = z i * C.f i z := fun i => by
    simp only [StochKolmogorov.Persist.drift, PiLp.toLp_apply, hpp]
  have hs : ∀ j i, (scol (diffusion C (0, z)) j) i = z i * C.g i z * C.Γ j i := fun j i => by
    simp only [scol, StochKolmogorov.Persist.diffusion, PiLp.toLp_apply, hpp]
  set a : Fin n → ℝ := fun i => c i * z i / Sf c z with ha
  have Q1 : ell1 c p z (drift C (0, z)) = ∑ i, a i * C.f i z - ∑ i, p i * C.f i z := by
    unfold ell1; simp only [hb]
    congr 1
    · rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by simp only [ha]; ring
    · exact Finset.sum_congr rfl fun i _ => by rw [mul_div_cancel_left₀ _ (hz i).ne']
  have Q2 : ∀ j, ell1 c p z (scol (diffusion C (0, z)) j) =
      ∑ i, ((a i - p i) * C.g i z) * C.Γ j i := fun j => by
    unfold ell1; simp only [hs]
    rw [Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hzi := (hz i).ne'
    simp only [ha]; field_simp
    try ring
  have Q3 : ∀ j, ell2 c p z (scol (diffusion C (0, z)) j) =
      -(∑ i, (a i * C.g i z) * C.Γ j i) ^ 2 + ∑ i, (p i * C.g i z ^ 2) * C.Γ j i ^ 2 := fun j => by
    unfold ell2; simp only [hs]
    congr 1
    · rw [← div_pow, Finset.sum_div]
      congr 2
      exact Finset.sum_congr rfl fun i _ => by simp only [ha]; ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hzi := (hz i).ne'
      field_simp
  have hsum : ∑ j, (δ₀ * ell1 c p z (scol (diffusion C (0, z)) j) ^ 2
      + ell2 c p z (scol (diffusion C (0, z)) j)) =
      δ₀ * ∑ i, ∑ i', ((a i - p i) * C.g i z) * ((a i' - p i') * C.g i' z) * C.sig i i' +
      (-(∑ i, ∑ i', (a i * C.g i z) * (a i' * C.g i' z) * C.sig i i') +
        ∑ i, (p i * C.g i z ^ 2) * C.sig i i) := by
    simp only [Q2, Q3]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      quad_sig, quad_sig, diag_sig]
    rfl
  rw [Q1, hsum]
  have hcb := cBracket_form C hc hzo
  have hamem : ∀ i, 0 ≤ a i ∧ a i ≤ 1 := fun i => a_mem hc hzo i
  have hpd : ∀ i, p i ≤ δ₀ := fun i => (p_le_l1 hp i).trans hpl
  -- (i) the `-Σ pF` term
  have t1 : -(∑ i, p i * C.f i z) ≤ δ₀ * ∑ i, |C.f i z| := by
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : -(p i * C.f i z) ≤ p i * |C.f i z| := by
      rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_le_abs _) (hp i).le
    exact h1.trans (mul_le_mul_of_nonneg_right (hpd i) (abs_nonneg _))
  set T := ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => abs_nonneg _
  -- (ii) the diagonal term
  have t2 : ∑ i, (p i * C.g i z ^ 2) * C.sig i i ≤ δ₀ * T := by
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (p i * C.g i z ^ 2) * C.sig i i ≤ δ₀ * |C.g i z * C.g i z * C.sig i i| := by
      have e : (p i * C.g i z ^ 2) * C.sig i i = p i * (C.g i z * C.g i z * C.sig i i) := by ring
      rw [e]
      exact (le_abs_self _).trans (by
        rw [abs_mul, abs_of_pos (hp i)]
        exact mul_le_mul_of_nonneg_right (hpd i) (abs_nonneg _))
    exact h1.trans (mul_le_mul_of_nonneg_left (dsum_le (fun i => C.g i z) C.sig i) hδ0.le)
  -- (iii) the cross term
  have t3 : ∑ i, ∑ i', ((a i - p i) * C.g i z) * ((a i' - p i') * C.g i' z) * C.sig i i' ≤ T := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
    have hai : |a i - p i| ≤ 1 := abs_le.2 ⟨by linarith [(hamem i).1, hpd i], by
      linarith [(hamem i).2, (hp i).le]⟩
    have hai' : |a i' - p i'| ≤ 1 := abs_le.2 ⟨by linarith [(hamem i').1, hpd i'], by
      linarith [(hamem i').2, (hp i').le]⟩
    have e : ((a i - p i) * C.g i z) * ((a i' - p i') * C.g i' z) * C.sig i i' =
        ((a i - p i) * (a i' - p i')) * (C.g i z * C.g i' z * C.sig i i') := by ring
    rw [e]
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (mul_le_one₀ hai (abs_nonneg _) hai')
  have hF0 : 0 ≤ ∑ i, |C.f i z| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hb35 : bracket35 C c γb δ₀ z = cBracket C c z + γb +
      δ₀ * ∑ i, (2 * |C.f i z| + C.g i z ^ 2) + 3 * δ₀ * T := rfl
  have hF2 : ∑ i, |C.f i z| ≤ ∑ i, (2 * |C.f i z| + C.g i z ^ 2) :=
    Finset.sum_le_sum fun i _ => by linarith only [abs_nonneg (C.f i z), sq_nonneg (C.g i z)]
  rw [hb35, hcb]
  have h6 := mul_le_mul_of_nonneg_left hF2 hδ0.le
  have h7 := mul_le_mul_of_nonneg_left t3 hδ0.le
  linarith only [t1, t2, h6, h7, hγ, mul_nonneg hδ0.le hT0]

theorem bracket35_zero (C : Coeffs n) (c : SDEState n) {γb δ₀ : ℝ} (hγ : 0 < γb) (hδ0 : 0 < δ₀) :
    0 ≤ bracket35 C c γb δ₀ 0 := by
  have h0 : cBracket C c 0 = 0 := by simp [cBracket]
  unfold bracket35
  rw [h0]
  have h1 : 0 ≤ ∑ i, (2 * |C.f i 0| + C.g i 0 ^ 2) :=
    Finset.sum_nonneg fun i _ => by nlinarith [abs_nonneg (C.f i 0), sq_nonneg (C.g i 0)]
  have h2 : 0 ≤ ∑ i, ∑ j, |C.g i 0 * C.g j 0 * C.sig i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have := mul_nonneg hδ0.le h1
  have := mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * δ₀) h2
  linarith

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

theorem Hconst_nonneg {C : Coeffs n} {c : SDEState n} {γb δ₀ : ℝ} (hA : Assumption11 C c γb)
    (hδ : IsDelta0 C γb δ₀) : 0 ≤ Hconst C c γb δ₀ :=
  (bracket35_zero C c hA.2.2.2.1 hδ.1).trans
    (le_csSup (bracket35_bddAbove C c γb δ₀ hA hδ) ⟨0, fun i => by simp, rfl⟩)

/-- The drift of `e^{-a} G_m(y)` with clock rate `δ₀ H` is `≤ 0` along (1.1). -/
theorem driftGen_Gm_le (hn : 0 < n) {C : Coeffs n} {c p : SDEState n} {γb δ₀ m : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (hm : 0 ≤ m) (σx : SDEDiffusion n) (bx x z : SDEState n) (a : ℝ) :
    driftGen (FG (Gm δ₀ m c p)) (δ₀ * Hconst C c γb δ₀) σx bx (diffusion C (0, z))
      (drift C (0, z)) x z a ≤ 0 := by
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  have hδ0 : 0 < δ₀ := hδ.1
  have hδ1 : δ₀ < 1 := delta0_lt_one hn hA hδ
  have hp1 : ∑ i, p i < 1 := by rw [sum_p_eq hp]; linarith
  have hpos : ∀ i, 0 < p i := hp
  have hGc := Gm_contDiff hδ0 hm hc hpos hp1
  have hH0 := Hconst_nonneg hA hδ
  rw [FG_driftGen hGc]
  suffices hX : fderiv ℝ (Gm δ₀ m c p) z (drift C (0, z)) + (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ
      (Gm δ₀ m c p)) z (scol (diffusion C (0, z)) j) (scol (diffusion C (0, z)) j) -
      δ₀ * Hconst C c γb δ₀ * Gm δ₀ m c p z ≤ 0 by
    linarith only [mul_le_mul_of_nonneg_left hX (Real.exp_pos (-a)).le]
  by_cases hz : z ∈ openOrthant n
  · have hd1 : ∀ w, fderiv ℝ (Gm δ₀ m c p) z w = G1f δ₀ m c p z w := fun w =>
      fderiv_eq_of_line (hGc.differentiable two_ne_zero) z w (by
        have := Gm_line (δ := δ₀) (m := m) (p := p) (w := w) hc ((line_eventually hz).self_of_nhds)
        rwa [zero_smul, add_zero] at this)
    have hd2 : ∀ w, fderiv ℝ (fderiv ℝ (Gm δ₀ m c p)) z w w = G2f δ₀ m c p z w := fun w =>
      fderiv2_eq_of_line_loc hGc z w ((line_eventually hz).mono fun s hs => Gm_line hc hs)
        (G1f_line hc hz)
    rw [hd1]
    simp only [hd2]
    rw [Gm, if_pos hz]
    set U := Uf δ₀ c p z with hUdef
    have hU : 0 < U := Real.exp_pos _
    have hD : 0 ≤ deriv Real.smoothTransition (U - m) := by linarith [hsat_d2_nonpos m U]
    have hh' := (hsat_d1_mem m U).1
    set h' := 1 - Real.smoothTransition (U - m) with hh'def
    have hG2 : ∀ j, G2f δ₀ m c p z (scol (diffusion C (0, z)) j) ≤
        h' * U * δ₀ * (δ₀ * ell1 c p z (scol (diffusion C (0, z)) j) ^ 2 +
          ell2 c p z (scol (diffusion C (0, z)) j)) := fun j => by
      set X := U * (δ₀ * ell1 c p z (scol (diffusion C (0, z)) j))
      have e : G2f δ₀ m c p z (scol (diffusion C (0, z)) j) =
          -(deriv Real.smoothTransition (U - m) * (X * X)) + h' * U * δ₀ *
            (δ₀ * ell1 c p z (scol (diffusion C (0, z)) j) ^ 2 +
              ell2 c p z (scol (diffusion C (0, z)) j)) := by
        unfold G2f; rw [← hUdef, ← hh'def]; ring
      rw [e]
      linarith only [mul_nonneg hD (mul_self_nonneg X)]
    have hsum : ∑ j, G2f δ₀ m c p z (scol (diffusion C (0, z)) j) ≤ h' * U * δ₀ *
        ∑ j, (δ₀ * ell1 c p z (scol (diffusion C (0, z)) j) ^ 2 +
          ell2 c p z (scol (diffusion C (0, z)) j)) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun j _ => hG2 j
    have hQ := (Q_le C hc hz hp hpl hδ1 hδ0 hγ).trans
      (le_csSup (bracket35_bddAbove C c γb δ₀ hA hδ) ⟨z, openOrthant_sub hz, rfl⟩)
    have hQ' : ell1 c p z (drift C (0, z)) + (1 / 2) * ∑ j, (δ₀ * ell1 c p z
        (scol (diffusion C (0, z)) j) ^ 2 + ell2 c p z (scol (diffusion C (0, z)) j)) ≤
        Hconst C c γb δ₀ := hQ
    have k1 := mul_le_mul_of_nonneg_left hQ' (by positivity : 0 ≤ h' * U * δ₀)
    have k2 : δ₀ * Hconst C c γb δ₀ * (h' * U) ≤ δ₀ * Hconst C c γb δ₀ * hsat m U :=
      mul_le_mul_of_nonneg_left (hsat_d1_mul_le m hU.le)
      (by positivity : 0 ≤ δ₀ * Hconst C c γb δ₀)
    have e1 : G1f δ₀ m c p z (drift C (0, z)) = h' * (U * (δ₀ * ell1 c p z (drift C (0, z)))) := by
      unfold G1f; rw [← hUdef, ← hh'def]
    rw [e1]
    linarith only [k1, k2, hsum]
  · have hzb : z ∉ boxK δ₀ m c p := fun h => hz (boxK_sub _ _ _ _ h)
    obtain ⟨h0, h2⟩ := Gm_fderiv_out hδ0 hm hc hpos hp1 hzb
    simp only [h0, h2, ContinuousLinearMap.zero_apply, Finset.sum_const_zero, mul_zero, zero_add]
    have h3 := mul_nonneg (mul_nonneg hδ0.le hH0) (Gm_nonneg (δ := δ₀) hm c p z)
    linarith only [h3]

end QFgenL

end ItoLib

end FlatM_QF
-- ===== QG =====
section FlatM_QG
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section QG
/-! Clause 4b (3.6) of Lemma 3.1: `E V^δ₀(X_t) ≤ e^{δ₀ H t} V^δ₀(x)`. -/
variable {n : ℕ}

/-- The integrand of the martingale part is bounded for the test function `FG (Gm ..)`. -/
theorem Gm_integrand_bound {δ m : ℝ} {c p : SDEState n} (hδ : 0 < δ) (hm : 0 ≤ m)
    (hc : c ∈ openOrthant n) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1)
    {σ : SDEState n → SDEDiffusion n} (hσ : Continuous σ) (j : Fin n) :
    ∃ K, ∀ y, ‖fderiv ℝ (Gm δ m c p) y‖ * ‖scol (σ y) j‖ ≤ K := by
  have hGc := Gm_contDiff hδ hm hc hp hp1
  have hg : Continuous fun y => ‖fderiv ℝ (Gm δ m c p) y‖ * ‖scol (σ y) j‖ :=
    (hGc.continuous_fderiv (by norm_num)).norm.mul (scol_continuous hσ j).norm
  obtain ⟨K, hK⟩ := (boxK_isCompact δ m c p).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max K 0, fun y => ?_⟩
  by_cases hy : y ∈ boxK δ m c p
  · have := hK y hy
    rw [Real.norm_eq_abs] at this
    exact ((le_abs_self _).trans this).trans (le_max_left _ _)
  · rw [(Gm_fderiv_out hδ hm hc hp hp1 hy).1]
    simp

set_option maxHeartbeats 1000000 in
/-- Ito step: `E[e^{-δ₀ H t} G_m(Y_t)] ≤ G_m(x)`. -/
theorem lintegral_Gm_le (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B) {c p : SDEState n} {γb δ₀ m : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (hm : 0 ≤ m) {x : SDEState n} {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (-(δ₀ * Hconst C c γb δ₀ * t)) * Gm δ₀ m c p (Y t ω)) ∂P ≤
      ENNReal.ofReal (Gm δ₀ m c p x) := by
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hδ0 : 0 < δ₀ := hδ.1
  have hδ1 : δ₀ < 1 := delta0_lt_one hn hA hδ
  have hp1 : ∑ i, p i < 1 := by rw [sum_p_eq hp]; linarith
  have hpos : ∀ i, 0 < p i := hp
  have hGc := Gm_contDiff hδ0 hm hc hpos hp1
  have hH0 := Hconst_nonneg hA hδ
  obtain ⟨hσ, hb, -⟩ := kolm_trunc C hA.2.1
  have hY' : SolvesBrownianSDE P (fun q => (fun z => diffusion C (0, z)) q.2)
      (fun q => (fun z => drift C (0, z)) q.2) B (fun _ => x) Y := hY
  obtain ⟨hXm, hXc, hXa, hX0, JX, -, -, hJX, -, hXeq⟩ := hY'
  have hX0' : ∀ᵐ ω ∂P, Y 0 ω = x := by filter_upwards [hX0] with ω h using h
  set κ0 : ℝ := δ₀ * Hconst C c γb δ₀ with hκ0
  have hκn : 0 ≤ κ0 := mul_nonneg hδ0.le hH0
  have hFb : ∀ (i : Fin (n + n + 1)) (j : Fin n), ∃ K, ∀ s ω (a : ℝ), 0 ≤ a →
      |fderiv ℝ (FG (Gm δ₀ m c p)) (pack (Y s ω) (Y s ω) a) (EuclideanSpace.single i 1) *
        pack (scol (diffusion C (0, Y s ω)) j) (scol (diffusion C (0, Y s ω)) j) 0 i| ≤ K := by
    intro i j
    obtain ⟨K, hK⟩ := Gm_integrand_bound hδ0 hm hc hpos hp1 hσ j
    exact ⟨K, fun s ω a ha => (FG_integrand_le hGc _ _ ha i _ _).trans (hK _)⟩
  obtain ⟨Z, hZi, hZ0, hZeq⟩ := ito_coupled_F hB x (X := Y) (Y := Y)
    (HX := fun s ω => diffusion C (0, Y s ω)) (HY := fun s ω => diffusion C (0, Y s ω))
    (JX := JX) (JY := JX)
    (bX := fun s ω => drift C (0, Y s ω)) (bY := fun s ω => drift C (0, Y s ω)) hXm hXm hXc hXc
    hXa hXa
    (fun s => hσ.measurable.comp (hXa s)) (fun s => hσ.measurable.comp (hXa s))
    (fun ω => hσ.comp (hXc ω)) (fun ω => hσ.comp (hXc ω))
    (fun s => hb.measurable.comp (hXa s)) (fun s => hb.measurable.comp (hXa s))
    (fun ω => hb.comp (hXc ω)) (fun ω => hb.comp (hXc ω)) hJX hJX hXeq hXeq
    hX0' hX0' (κ := fun _ _ => κ0) continuous_const (fun _ _ => hκn) (FG_contDiff hGc) hFb t
  have h := lintegral_le_of_ito (E := fun _ => (0 : ℝ)) (β := 0)
    (ae_of_all _ fun ω => ?_) hZi hZ0 hZeq (ae_of_all _ fun ω => ?_) (integrable_const _)
  · have e1 : ∀ ω, FG (Gm δ₀ m c p) (pack (Y t ω) (Y t ω) (∫ _ in (0 : ℝ)..t.val, κ0)) =
        Real.exp (-(κ0 * t)) * Gm δ₀ m c p (Y t ω) := by
      intro ω
      rw [FG_pack, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm (t.val) κ0]
      rfl
    simp only [e1, FG_pack, neg_zero, Real.exp_zero, one_mul, add_zero,
      integral_const, smul_zero] at h
    exact h
  · rw [FG_pack]
    exact mul_nonneg (Real.exp_pos _).le (Gm_nonneg hm _ _ _)
  · rw [zero_add]
    have : ∀ u : ℝ, driftGen (FG (Gm δ₀ m c p)) κ0 (diffusion C (0, Y u.toNNReal ω))
        (drift C (0, Y u.toNNReal ω)) (diffusion C (0, Y u.toNNReal ω))
        (drift C (0, Y u.toNNReal ω)) (Y u.toNNReal ω) (Y u.toNNReal ω)
        (∫ _ in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), κ0) ≤ 0 := fun u =>
      driftGen_Gm_le hn hA hδ hp hpl hm _ _ _ _ _
    have h2 := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) t.2
      (fun u _ => neg_nonneg.2 (this u))
    rw [intervalIntegral.integral_neg] at h2
    linarith

/-- `V^δ = U_δ` on the open orthant. -/
theorem Vfun_rpow_eq {δ : ℝ} {c p y : SDEState n} (hc : c ∈ openOrthant n)
    (hy : y ∈ openOrthant n) : Vfun c p y ^ δ = Uf δ c p y := by
  have hS : 0 < Sf c y := lt_of_lt_of_le one_pos (one_le_Sf hc (openOrthant_sub hy))
  have hP : 0 < ∏ i, y i ^ p i := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hy i) _
  have hVe : Vfun c p y = Sf c y / ∏ i, y i ^ p i := rfl
  have hV : 0 < Vfun c p y := by rw [hVe]; exact div_pos hS hP
  rw [Real.rpow_def_of_pos hV, Uf]
  congr 1
  rw [hVe, Real.log_div hS.ne' hP.ne',
    Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hy i) _).ne'), ellf]
  simp only [Real.log_rpow (hy _)]
  ring

/-- (3.6): `E V^δ₀(Y_t) ≤ e^{δ₀ H t} V^δ₀(x)` for `x` in the open orthant. -/
theorem moment_36 (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B) {c p : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) {x : SDEState n} (hx : x ∈ openOrthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) ∂P ≤
      ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c p x ^ δ₀) := by
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hδ0 : 0 < δ₀ := hδ.1
  have hδ1 : δ₀ < 1 := delta0_lt_one hn hA hδ
  have hp1 : ∑ i, p i < 1 := by rw [sum_p_eq hp]; linarith
  have hpos : ∀ i, 0 < p i := hp
  set k : ℝ := δ₀ * Hconst C c γb δ₀ * t with hk
  have hxf : x ∈ faceOpen (Finset.univ : Finset (Fin n)) :=
    ⟨openOrthant_sub hx, fun i hi => absurd (Finset.mem_univ i) hi, fun i _ => hx i⟩
  have hinv := face_inv C hB hA.2.1 hxf hY
  have hpos_t : ∀ᵐ ω ∂P, Y t ω ∈ openOrthant n := by
    filter_upwards [hinv] with ω h using fun i => (h t).2.2 i (Finset.mem_univ i)
  set f : ℕ → Ω → ℝ≥0∞ := fun m ω =>
    ENNReal.ofReal (Real.exp (-k) * Gm δ₀ (m : ℝ) c p (Y t ω)) with hf
  have hfm : ∀ m : ℕ, Measurable (f m) := fun m =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((Gm_contDiff hδ0 (Nat.cast_nonneg m) hc hpos hp1).continuous.measurable.comp (hY.1 t)))
  have hlim : ∀ᵐ ω ∂P, liminf (fun m : ℕ => f m ω) atTop =
      ENNReal.ofReal (Real.exp (-k) * Uf δ₀ c p (Y t ω)) := by
    filter_upwards [hpos_t] with ω hω
    apply Tendsto.liminf_eq
    apply tendsto_atTop_of_eventually_const (i₀ := ⌈Uf δ₀ c p (Y t ω)⌉₊)
    intro m hm
    simp only [hf]
    rw [Gm, if_pos hω, hsat_eq_self (Nat.cast_nonneg m)
      ((Nat.le_ceil _).trans (Nat.cast_le.2 hm))]
  have hbd : ∀ m : ℕ, ∫⁻ ω, f m ω ∂P ≤ ENNReal.ofReal (Uf δ₀ c p x) := fun m =>
    (lintegral_Gm_le hn hB hA hδ hp hpl (Nat.cast_nonneg m) hY t).trans
      (ENNReal.ofReal_le_ofReal (by
        rw [Gm, if_pos hx]; exact hsat_le_self _ (Real.exp_pos _).le))
  have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (-k) * Uf δ₀ c p (Y t ω)) ∂P ≤
      ENNReal.ofReal (Uf δ₀ c p x) := by
    rw [← lintegral_congr_ae hlim]
    exact (lintegral_liminf_le hfm).trans
      (Filter.liminf_le_of_frequently_le' (Frequently.of_forall hbd))
  have h2 : ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) ∂P = ENNReal.ofReal (Real.exp k) *
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-k) * Uf δ₀ c p (Y t ω)) ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_congr_ae
    filter_upwards [hpos_t] with ω hω
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, one_mul, Vfun_rpow_eq hc hω]
  rw [h2, Vfun_rpow_eq hc hx, ENNReal.ofReal_mul (Real.exp_pos _).le]
  gcongr

end QG

end ItoLib

end FlatM_QG
-- ===== QH =====
section FlatM_QH
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QH
/-! Clause 1 toolkit (E1): the Ito isometry as an upper bound, `E J_t² ≤ E ∫₀ᵗ H²`. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QH

end ItoLib

end FlatM_QH
-- ===== QI =====
section FlatM_QI
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QI
/-! Clause 1 toolkit (E3): weak maximal inequality for continuous versions of Ito integrals. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QI
end ItoLib

end FlatM_QI
-- ===== QJ =====
section FlatM_QJ
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QJan
/-! Clause 1 toolkit (E4, part 1): analysis helpers. -/

end QJan

section QJ
/-! Clause 1 toolkit (E4, part 1): the continuous Ito integral as a function, and the Picard map. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QJ
end ItoLib

end FlatM_QJ
-- ===== QK =====
section FlatM_QK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QKan

end QKan

section QK
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QK
end ItoLib

end FlatM_QK
-- ===== QL =====
section FlatM_QL
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QL
/-! Clause 1 toolkit (E4, part 3): initial bound and the Picard moment bound. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QL
end ItoLib

end FlatM_QL
-- ===== QM =====
section FlatM_QM
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QM
/-! Clause 1 toolkit (E4, part 4): Borel–Cantelli for the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QM
end ItoLib

end FlatM_QM
-- ===== QN =====
section FlatM_QN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Nat
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QN
/-! Clause 1 toolkit (E4, part 5): almost-sure geometric convergence of the Picard iterates. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QN
end ItoLib

end FlatM_QN
-- ===== QO =====
section FlatM_QO
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QO
/-! Clause 1 toolkit (E4, part 6): the Picard limit process. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QO
end ItoLib

end FlatM_QO
-- ===== QP =====
section FlatM_QP
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QP
/-! Clause 1 toolkit (E4, part 7): the Picard limit solves the SDE (bounded Lipschitz case). -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QP
end ItoLib

end FlatM_QP
-- ===== QZ4 =====
section FlatM_QZ4
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section QZ4
/-! Clause 1 toolkit (E4, final): strong existence for bounded globally Lipschitz coefficients. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end QZ4
end ItoLib

end FlatM_QZ4
-- ===== E5A =====
section FlatM_E5A
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5A
/-! Clause 1 toolkit (E5, part 1): two solutions from the same point, of SDEs whose bounded
coefficients agree on a ball, coincide as long as the first stays in a smaller ball. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5A

end ItoLib

end FlatM_E5A
-- ===== E5B =====
section FlatM_E5B
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E5B
/-! Clause 1 toolkit (E5, part 2): gluing a consistent, non-exploding family of truncated
solutions into a global strong solution. -/
variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

end E5B

end ItoLib

end FlatM_E5B
-- ===== E6F =====
section FlatM_E6F
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6F
/-! Clause 1 toolkit (E6, part 1): `face_rep` for a solution of an SDE whose coefficients only
agree with the Kolmogorov coefficients on a box (truncated systems). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6F

end ItoLib

end FlatM_E6F
-- ===== E6P =====
section FlatM_E6P
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6P
/-! Clause 1 toolkit (E6, part 1): `face_rep` for a solution of an SDE whose coefficients only
agree with the Kolmogorov coefficients on a box (truncated systems). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6P

end ItoLib

end FlatM_E6P
-- ===== E6Q =====
section FlatM_E6Q
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6Q
/-! Clause 1 toolkit (E6, part 2): a solution of a Kolmogorov-structured SDE started in the
orthant stays in the orthant for all times, almost surely. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6Q

end ItoLib

end FlatM_E6Q
-- ===== E6T =====
section FlatM_E6T
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6T
/-! Clause 1 toolkit (E6, part 3): a Kolmogorov-structured truncation of the coefficients:
evaluate the true coefficients at the box projection `boxP (-R) R y`. It is bounded, globally
Lipschitz, equal to the true coefficients on the box, and of the form `y_k * (bounded)`. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end E6T

end ItoLib

end FlatM_E6T
-- ===== V =====
section FlatM_V
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11c
/-! M11c: the orthant test-function machinery of Q.lean/R.lean with a general family of C²
nonnegative coordinate functions `φ k` in place of `(v⁻)³`. -/

variable {Ω : Type*} {d : ℕ}

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

end M11c

end ItoLib

end FlatM_V
-- ===== W =====
section FlatM_W
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M11d
/-! M11d (lemma_3_1 clause 3, interior part): a solution started with `x_k > 0` has `X_t k ≠ 0`
almost surely at every fixed time. Test function `φ_δ(v) = 1/(v² + δ)`, with
`|φ_δ'(v) v| ≤ 2 φ_δ(v)` and `φ_δ''(v) v² ≤ 8 φ_δ(v)`. -/
open StochKolmogorov.Persist

variable {δ : ℝ}

variable {n : ℕ}

end M11d

end ItoLib

end FlatM_W
-- ===== Y =====
section FlatM_Y
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12a
/-! M12a: the test-function machinery of V.lean for a single C² nonnegative function `ψ` of a
linear form `ℓ(x) = Σ_k cv_k x_k`, `Φ(x) = ψ(ℓ x)` (used with `ψ ≈ log(1+·)`). -/

variable {Ω : Type*} {d : ℕ}

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

end M12a


section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

end M12b

end ItoLib

end FlatM_Y
-- ===== E6L =====
section FlatM_E6L
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6L
/-! Clause 1 toolkit (E6, part 4): the saturated Lyapunov profile `lyS m = hsat m ∘ psiK`,
derivatives of `y ↦ ψ(cᵀy)`, and the time-slot test function
`F(x,y,a) = e^{-a} (Φ(y) + K (T - x_{i0}) - λ) + λ` with its generator. -/
open StochKolmogorov.Persist

variable {n : ℕ}

end E6L

section E6Lb
variable {d : ℕ}

end E6Lb

end ItoLib

end FlatM_E6L
-- ===== E6M =====
section FlatM_E6M
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6M
/-! Clause 1 toolkit (E6, part 5): a maximal inequality without martingale theory. Along a
solution `Y` that stays in a set `D` on which the generator of `Φ ≥ 0` is at most `K`, the
probability that `Φ(Y_s) > λ` for some `s < t` is at most `(Φ(x) + K t) / (λ (1 - e⁻¹))`.
Proof: the Ito formula for `F = e^{-a}(Φ(y) + K (T - s) - λ) + λ`, where the clock `a` runs at
rate `M (Φ(Y) + K (T - s) - λ)⁺` (the time `s` is carried in the `X` slot), and `M → ∞`. -/
variable {n : ℕ}

end E6M

end ItoLib

end FlatM_E6M
-- ===== X41 =====
section FlatM_X41
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! X41 (eq_4_1, finite-`M` part): the minimax step of [SBA11, Lemma 4] for finitely many
boundary ergodic measures, by strict separation of a polytope from the closed negative orthant. -/

end ItoLib

end FlatM_X41
-- ===== E6A =====
section FlatM_E6A
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section E6A
/-! Clause 1 (E6, assembly): non-explosion of the truncated Kolmogorov systems via the saturated
Lyapunov function `lyS m (cᵀy)` and `exceed_prob_le`, then `glue_solution`. -/

open StochKolmogorov.Persist

variable {n : ℕ}

end E6A

end ItoLib

end FlatM_E6A
-- ===== L31 =====
section FlatM_L31
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz StochKolmogorov.Persist

end ItoLib


end FlatM_L31

open StochKolmogorov.Persist in
open EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B) {c p : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) {x : SDEState n} (hx : x ∈ openOrthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) ∂P ≤
      ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c p x ^ δ₀) := by
  exact ItoLib.moment_36 hn hB hA hδ hp hpl hx hY t
