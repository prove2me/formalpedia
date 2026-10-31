-- Prove2me | solution 1 for StochKolmogorov.Persist.kolmogorov_sde_face_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T05:32:12.314993+00:00
-- url     : https://prove2.me/submissions/8cdb639d-630c-4b31-be22-8ea10cc66f71

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
    rw [div_le_iff₀ ht]; nlinarith [hu.2]
  have hc1 : 0 < ⌈u * 2 ^ n / t.val⌉₊ := Nat.ceil_pos.2 hx0
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = ⌈u * 2 ^ n / t.val⌉₊ := ⟨⌈u * 2 ^ n / t.val⌉₊ - 1, by omega⟩
  have hkR : (k : ℝ) + 1 = ⌈u * 2 ^ n / t.val⌉₊ := by exact_mod_cast hk
  have hlt : (k : ℝ) < u * 2 ^ n / t.val := by
    have := Nat.ceil_lt_add_one hx0.le; linarith
  have hge : u * 2 ^ n / t.val ≤ (k : ℝ) + 1 := by rw [hkR]; exact Nat.le_ceil _
  have hk2 : k < 2 ^ n := by
    have : ⌈u * 2 ^ n / t.val⌉₊ ≤ 2 ^ n := Nat.ceil_le.2 (by exact_mod_cast hxle)
    omega
  have hlo : (k : ℝ) * t.val / 2 ^ n < u := by
    rw [div_lt_iff₀ h2]; rw [lt_div_iff₀ ht] at hlt; linarith
  have hhi : u ≤ ((k : ℝ) + 1) * t.val / 2 ^ n := by
    rw [le_div_iff₀ h2]; rw [div_le_iff₀ ht] at hge; linarith
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
      linarith
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith
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
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht)
      (by positivity)
  have hs_ge : ∀ m, (dyTime t n k : ℝ) ≤ (s m : ℝ) := fun m => by
    have hkm : ((k * 2 ^ m : ℕ) : ℝ) ≤ y m := by
      push_cast
      simp only [hy]
      rw [le_div_iff₀ hpos, pow_add]
      rw [div_le_iff₀ (by positivity)] at hlo
      nlinarith [pow_pos (two_pos (α := ℝ)) m]
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
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hs_ge m])]
      have : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by ring
      have := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith
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
  nlinarith [mul_nonneg hε.le ht]

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

theorem coord_contDiff {e : ℕ} (i : Fin e) {n : ℕ∞} :
    ContDiff ℝ n (fun u : SDEState e => u i) :=
  (EuclideanSpace.proj i : SDEState e →L[ℝ] ℝ).contDiff

end M9cF


section M9c2
/-! Packing `(x, y, a)` into `SDEState (d + d + 1)` and the structure of `Ff`. -/

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

end M9d


section M9d2
/-! Global bounds for the generator and the integrands (compact support of `Ff` in (x, y)). -/

end M9d2



section M9e1
/-! Zero integral, measurability of time integrals, the exponential primitive identity, and the
pointwise generator bound with the localizing rate `kap`. -/

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

theorem norm_le_card_mul {M : ℝ} {x : SDEState d} (hx : ∀ i, |x i| ≤ M) : ‖x‖ ≤ d * M := by
  calc ‖x‖ ≤ ∑ i, |x i| := euc_norm_le_sum' x
    _ ≤ ∑ _i : Fin d, M := Finset.sum_le_sum fun i _ => hx i
    _ = d * M := by simp

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

end M10i

section M10j
open StochKolmogorov.Persist
variable {n : ℕ}

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
    rw [hito, hKsum]; linarith [hint ω hEω']
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

end QFgen

section QFsat
/-! The concave saturation `h_m(u) = ∫₀ᵘ (1 - st(s - m)) ds`. -/

end QFsat

section QFell
/-! The logarithm `ℓ = log(1 + cᵀy) - Σ pᵢ log yᵢ` of `V`, its line derivatives, and bounds. -/
variable {n : ℕ}
open StochKolmogorov.Persist

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

end QFalg

section QFgenL
variable {n : ℕ}
open StochKolmogorov.Persist

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
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (C : Coeffs n) {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ faceOpen I) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) :
    ∀ᵐ ω ∂P, ∀ t, Y t ω ∈ faceOpen I := by
  exact ItoLib.face_inv C hB hC hx hY
