-- Prove2me | solution 1 for StochKolmogorov.Persist.coord_ne_zero_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-30T19:38:31.922775+00:00
-- url     : https://prove2.me/submissions/ebb6cc69-106a-4fc5-843a-f9430adcbc88

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula

set_option linter.all false

-- ===== ItoM1 =====

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
    have hnδ := mul_lt_mul_of_pos_right h2n hδ
    linarith only [hn, hnδ]
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  exact absurd hp4 (not_lt.2 this.le)

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
    rw [div_le_iff₀ ht, mul_comm (2 ^ n : ℝ)]; exact mul_le_mul_of_nonneg_right hu.2 h2.le
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
      linarith only [h1', this, hlo]
    · have hl' : (k : ℝ) + 1 ≤ l := by exact_mod_cast hl
      have : ((k : ℝ) + 1) * t.val / 2 ^ n ≤ (l : ℝ) * t.val / 2 ^ n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl' ht.le) h2.le
      linarith only [h1, this, hhi]
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
      have h2m := mul_le_mul_of_nonneg_left hlo (pow_pos (two_pos (α := ℝ)) m).le
      linarith only [h2m]
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
      rw [abs_sub_comm, abs_of_nonneg (by linarith only [hs_ge m])]
      have hcell : ((k : ℝ) + 1) * t.val / 2 ^ n - (k : ℝ) * t.val / 2 ^ n = t.val / 2 ^ n := by
        ring
      have hsm := hs_le m
      rw [hdk]
      show (s m : ℝ) - (k : ℝ) * t.val / 2 ^ n ≤ t.val / 2 ^ n
      linarith only [hcell, hsm, hhi]
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

end M8a

section M8b
variable [MeasurableSpace Ω]

end M8b

section M8c
variable [MeasurableSpace Ω]

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
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hT) h2.le
  have hbT : ((k : ℝ) + 1) * t.val / (2 : ℝ) ^ n ≤ t.val := by
    rw [div_le_iff₀ h2]
    have := mul_le_mul_of_nonneg_right hk' hT
    linarith only [this]
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
  linarith only [mul_nonneg hε.le ht, hε]

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

/-- Smooth cutoff: `1` on `(-∞, r]`, `0` on `[r+1, ∞)`, values in `[0,1]`. -/
noncomputable def cutoff (r : ℝ) (x : ℝ) : ℝ := Real.smoothTransition (r + 1 - x)

theorem cutoff_contDiff (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (cutoff r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

theorem cutoff_eq_one {r x : ℝ} (h : x ≤ r) : cutoff r x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_eq_zero {r x : ℝ} (h : r + 1 ≤ x) : cutoff r x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_nonneg (r x : ℝ) : 0 ≤ cutoff r x := Real.smoothTransition.nonneg _

theorem cutoff_le_one (r x : ℝ) : cutoff r x ≤ 1 := Real.smoothTransition.le_one _

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

theorem fderiv12_congr_nhds {f g : E → ℝ} {u : E} (h : f =ᶠ[𝓝 u] g) :
    fderiv ℝ f u = fderiv ℝ g u ∧ fderiv ℝ (fderiv ℝ f) u = fderiv ℝ (fderiv ℝ g) u :=
  ⟨h.fderiv_eq, h.fderiv.fderiv_eq⟩

/-- Derivatives of a function that scales under a translation. -/
theorem fderiv12_translate {f : E → ℝ} (hf : ContDiff ℝ 2 f) (z : E) (k : ℝ)
    (hfz : ∀ w, f (w + z) = k * f w) (u : E) :
    fderiv ℝ f (u + z) = k • fderiv ℝ f u ∧
      fderiv ℝ (fderiv ℝ f) (u + z) = k • fderiv ℝ (fderiv ℝ f) u := by
  have hd : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h1 : ∀ w, fderiv ℝ f (w + z) = k • fderiv ℝ f w := fun w => by
    rw [← fderiv_comp_add_right]
    have : (fun x => f (x + z)) = fun x => k * f x := funext hfz
    rw [this, fderiv_const_mul (hd w)]
  refine ⟨h1 u, ?_⟩
  rw [← fderiv_comp_add_right]
  have : (fun x => fderiv ℝ f (x + z)) = fun x => k • fderiv ℝ f x := funext h1
  rw [this]
  exact ((hd2 u).hasFDerivAt.const_smul k).fderiv

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

theorem pack_ext {u w : SDEState (d + d + 1)} (hx : ∀ k, u (ixc k) = w (ixc k))
    (hy : ∀ k, u (iyc k) = w (iyc k)) (ha : u iac = w iac) : u = w := by
  refine PiLp.ext fun i => ?_
  induction i using Fin.lastCases with
  | last => exact ha
  | cast j =>
    induction j using Fin.addCases with
    | left k => exact hx k
    | right k => exact hy k

/-- The `a`-direction. -/
noncomputable def eac : SDEState (d + d + 1) := pack 0 0 1

theorem pack_add_eac (x y : SDEState d) (a c : ℝ) :
    pack x y a + c • (eac (d := d)) = pack x y (a + c) :=
  pack_ext (fun k => by simp [eac]) (fun k => by simp [eac]) (by simp [eac])

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

/-- `∫_0^t e^{-A(u)} g(u) du = 1 - e^{-A(t)}` for `A(u) = ∫_0^u g`. -/
theorem integral_exp_neg_primitive {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    ∫ u in (0 : ℝ)..t, Real.exp (-(∫ v in (0 : ℝ)..u, g v)) * g u =
      1 - Real.exp (-(∫ v in (0 : ℝ)..t, g v)) := by
  have h1 : ∀ u, HasDerivAt (fun u => ∫ v in (0 : ℝ)..u, g v) (g u) u := fun u =>
    (hg.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hd : ∀ u, HasDerivAt (fun u => -Real.exp (-(∫ v in (0 : ℝ)..u, g v)))
      (Real.exp (-(∫ v in (0 : ℝ)..u, g v)) * g u) u := by
    intro u
    have h2 := ((h1 u).neg.exp).neg
    exact h2.congr_deriv (by simp only [Pi.neg_apply]; ring)
  have hpc : Continuous fun u => ∫ v in (0 : ℝ)..u, g v :=
    continuous_iff_continuousAt.2 fun u => (h1 u).continuousAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    (((Real.continuous_exp.comp hpc.neg).mul hg).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_same, neg_zero, Real.exp_zero]
  ring

/-- Distance of `x` from the closed ball of radius `R`. -/
noncomputable def distB (R : ℝ) (x : SDEState d) : ℝ := max 0 (‖x‖ - R)

theorem distB_continuous (R : ℝ) : Continuous (distB (d := d) R) :=
  continuous_const.max (continuous_norm.sub continuous_const)

theorem distB_nonneg (R : ℝ) (x : SDEState d) : 0 ≤ distB R x := le_max_left _ _

theorem distB_eq_zero {R : ℝ} {x : SDEState d} (h : ‖x‖ ≤ R) : distB R x = 0 :=
  max_eq_left (by linarith)

end M9e1

section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

end M9e2

end ItoLib

-- ===== E =====
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

theorem abs_packcol_le (σx σy : SDEDiffusion d) (j : Fin d) (i : Fin (d + d + 1)) :
    |pack (scol σx j) (scol σy j) 0 i| ≤ ‖σx‖ + ‖σy‖ := by
  have h1 := norm_nonneg σx
  have h2 := norm_nonneg σy
  induction i using Fin.lastCases with
  | last => rw [show pack (scol σx j) (scol σy j) 0 (Fin.last _) = 0 from pack_iac _ _ _]; simp; linarith
  | cast i' =>
    induction i' using Fin.addCases with
    | left k =>
      rw [show pack (scol σx j) (scol σy j) 0 (Fin.castSucc (Fin.castAdd d k)) = σx (k, j) from
        pack_ixc _ _ _ k]
      have := PiLp.norm_apply_le σx (k, j)
      rw [Real.norm_eq_abs] at this
      linarith
    | right k =>
      rw [show pack (scol σx j) (scol σy j) 0 (Fin.castSucc (Fin.natAdd d k)) = σy (k, j) from
        pack_iyc _ _ _ k]
      have := PiLp.norm_apply_le σy (k, j)
      rw [Real.norm_eq_abs] at this
      linarith

end M10b4a

section M10b4b
/-! M10b-4 (b): pathwise bounds for the generator `driftG` when `X` has coefficients
`σ₀(X), b₀(X)` and `Y` has arbitrary coefficients `σy, by'`. -/

theorem abs_pack0_le (u v : SDEState d) (i : Fin (d + d + 1)) :
    |pack u v 0 i| ≤ ‖u‖ + ‖v‖ := by
  have h1 := norm_nonneg u
  have h2 := norm_nonneg v
  induction i using Fin.lastCases with
  | last => rw [show pack u v 0 (Fin.last _) = 0 from pack_iac _ _ _]; simp; linarith
  | cast i' =>
    induction i' using Fin.addCases with
    | left k =>
      rw [show pack u v 0 (Fin.castSucc (Fin.castAdd d k)) = u k from pack_ixc _ _ _ k]
      have := PiLp.norm_apply_le u k
      rw [Real.norm_eq_abs] at this
      linarith
    | right k =>
      rw [show pack u v 0 (Fin.castSucc (Fin.natAdd d k)) = v k from pack_iyc _ _ _ k]
      have := PiLp.norm_apply_le v k
      rw [Real.norm_eq_abs] at this
      linarith

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

-- ===== F =====
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

/-- `|x|²` read off the `x`-block. -/
noncomputable def Nxf (u : SDEState (d + d + 1)) : ℝ := ∑ k, u (ixc k) ^ 2

theorem Nxf_contDiff {n : ℕ∞} : ContDiff ℝ n (Nxf (d := d)) := by
  unfold Nxf
  exact ContDiff.sum fun k _ => (coord_contDiff _).pow 2

theorem Nxf_pack (x y : SDEState d) (a : ℝ) : Nxf (pack x y a) = ‖x‖ ^ 2 := by
  simp only [Nxf, pack_ixc, EuclideanSpace.real_norm_sq_eq]

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

theorem pack_split (x y : SDEState d) : pack x y 0 = pack x 0 0 + pack 0 y 0 :=
  pack_ext (fun k => by simp) (fun k => by simp) (by simp)

end M10c3

end ItoLib

-- ===== G =====
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
    hpk.measurable.comp ((hXm s).prodMk ((hYm s).prodMk (hAm s)))
  have hUa : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (U s) := fun s =>
    hpk.measurable.comp ((hXa s).prodMk ((hYa s).prodMk (hAa s)))
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
    fun i j s => (hcol i j).measurable.comp (hHHa s)
  have hHc : ∀ i j ω, Continuous fun s => HU i j s ω := fun i j ω => (hcol i j).comp (hHH ω)
  have hbm : ∀ i s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bU i s) :=
    fun i s => (hbf i).measurable.comp (hBBa s)
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
    fun i j s => (hKf i j).measurable.comp
      (((hXa s).prodMk ((hYa s).prodMk (hAa s))).prodMk (hHHa s))
  have hKc : ∀ i j ω, Continuous
      (fun s => fderiv ℝ F (U s ω) (EuclideanSpace.single i 1) * HU i j s ω) :=
    fun i j ω => (hKf i j).comp (((hXc ω).prodMk ((hYc ω).prodMk (hAc ω))).prodMk (hHH ω))
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

/-- Clock rate penalising only `X` outside `B_R`. -/
noncomputable def kapX (c M R : ℝ) (x : SDEState d) : ℝ := c + M * distB R x

theorem kapX_nonneg {c M R : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (x : SDEState d) :
    0 ≤ kapX c M R x :=
  add_nonneg hc (mul_nonneg hM (distB_nonneg R x))

theorem kapX_comp_continuous (c M R : ℝ) {α : Type*} [TopologicalSpace α] {x : α → SDEState d}
    (hx : Continuous x) : Continuous fun v => kapX c M R (x v) :=
  continuous_const.add (continuous_const.mul ((distB_continuous R).comp hx))

end M10c4

section M10c5
/-! M10c-5: expectation bound for `Gf r` along `(X, Y, A)`, `X` the SDE solution, `Y` a general
Ito process with globally bounded coefficients, clock rate `kapX` (penalising only `X`). -/

end M10c5

section M10c5s
/-! s33 STAB: stability in probability of an SDE solution against Ito processes whose
coefficients are close (in mean integrated square, inside `B̄_{R+3}`) to the SDE coefficients. -/

end M10c5s

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

-- ===== H =====
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

-- ===== I =====
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

-- ===== J =====
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

-- ===== K =====
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

-- ===== L =====
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

-- ===== M =====
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

-- ===== N =====
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

-- ===== O =====
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

-- ===== P =====
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

end M10j

end ItoLib

-- ===== Q =====
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

theorem scol_apply' (s : SDEDiffusion d) (j k : Fin d) : scol s j k = s (k, j) := rfl

theorem norm_pack0_le (u v : SDEState d) : ‖pack u v 0‖ ≤ ((d : ℝ) + d + 1) * (‖u‖ + ‖v‖) := by
  calc ‖pack u v 0‖ ≤ ∑ i, |pack u v 0 i| := euc_norm_le_sum' _
    _ ≤ ∑ _i : Fin (d + d + 1), (‖u‖ + ‖v‖) := Finset.sum_le_sum fun i _ => abs_pack0_le u v i
    _ = ((d : ℝ) + d + 1) * (‖u‖ + ‖v‖) := by simp [mul_add]

theorem norm_packcol_le (σx σy : SDEDiffusion d) (j : Fin d) :
    ‖pack (scol σx j) (scol σy j) 0‖ ≤ ((d : ℝ) + d + 1) * (‖σx‖ + ‖σy‖) := by
  calc ‖pack (scol σx j) (scol σy j) 0‖ ≤ ∑ i, |pack (scol σx j) (scol σy j) 0 i| :=
        euc_norm_le_sum' _
    _ ≤ ∑ _i : Fin (d + d + 1), (‖σx‖ + ‖σy‖) :=
        Finset.sum_le_sum fun i _ => abs_packcol_le σx σy j i
    _ = ((d : ℝ) + d + 1) * (‖σx‖ + ‖σy‖) := by simp [mul_add]

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

end M10m

end ItoLib

-- ===== R =====
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

-- ===== S =====
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

-- ===== V =====
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

noncomputable def PhifG (φ : Fin d → ℝ → ℝ) (u : SDEState (d + d + 1)) : ℝ := ∑ k, (φ k) (u (ixc k))

/-- Inner orthant test function `e^{-a} Φ`. -/
noncomputable def H0fG (φ : Fin d → ℝ → ℝ) (u : SDEState (d + d + 1)) : ℝ := Real.exp (-u iac) * PhifG φ u

/-- Orthant test function `e^{-a} χ_r(|x|²) Φ`. -/
noncomputable def HfG (φ : Fin d → ℝ → ℝ) (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * (cutoff r (Nxf u) * PhifG φ u)

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

theorem phiG_hasDeriv (k : Fin d) (v : ℝ) : HasDerivAt (φ k) (deriv (φ k) v) v :=
  (((hφ.out k).differentiable (by norm_num)) v).hasDerivAt

theorem phiG_hasDeriv2 (k : Fin d) (v : ℝ) :
    HasDerivAt (deriv (φ k)) (deriv (deriv (φ k)) v) v := by
  have h2 : ContDiff ℝ (1 + 1) (φ k) := (hφ.out k).of_le (by norm_num)
  have h1 : ContDiff ℝ 1 (deriv (φ k)) := (contDiff_succ_iff_deriv.1 h2).2.2
  exact ((h1.differentiable (by norm_num)) v).hasDerivAt

theorem PhifG_contDiff : ContDiff ℝ 2 (PhifG φ (d := d)) := by
  unfold PhifG
  exact ContDiff.sum fun k _ => (hφ.out k).comp (coord_contDiff _)

theorem PhifG_nonneg (u : SDEState (d + d + 1)) : 0 ≤ (PhifG φ) u :=
  Finset.sum_nonneg fun k _ => hφ0.out k _

theorem H0fG_contDiff : ContDiff ℝ 2 (H0fG φ (d := d)) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul (PhifG_contDiff (φ := φ))

theorem HfG_contDiff (r : ℝ) : ContDiff ℝ 2 (HfG φ (d := d) r) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul
    (((cutoff_contDiff r).comp Nxf_contDiff).mul (PhifG_contDiff (φ := φ)))

theorem HfG_nonneg (r : ℝ) (u : SDEState (d + d + 1)) : 0 ≤ (HfG φ) r u :=
  mul_nonneg (Real.exp_pos _).le (mul_nonneg (cutoff_nonneg _ _) (PhifG_nonneg (φ := φ) u))

theorem HfG_eq_H0fG_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : Nxf u < r) :
    (HfG φ) r =ᶠ[𝓝 u] (H0fG φ) := by
  have hc : ContinuousAt (Nxf (d := d)) u := (Nxf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (gt_mem_nhds hu)] with w hw
  simp only [HfG, H0fG, cutoff_eq_one hw.le, one_mul]

theorem HfG_zero_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nxf u) :
    (HfG φ) r =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
  have hc : ContinuousAt (Nxf (d := d)) u := (Nxf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hu)] with w hw
  simp only [HfG, cutoff_eq_zero hw.le, zero_mul, mul_zero]

theorem HfG_fderiv_zero {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nxf u) :
    fderiv ℝ ((HfG φ) r) u = 0 ∧ fderiv ℝ (fderiv ℝ ((HfG φ) r)) u = 0 := by
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (HfG_zero_nhds (φ := φ) hu)
  refine ⟨h1.trans (fderiv_const_apply _), h2.trans ?_⟩
  rw [show (fderiv ℝ fun _ : SDEState (d + d + 1) => (0 : ℝ)) = fun _ => 0 from
    funext fun w => fderiv_const_apply _]
  exact fderiv_const_apply _

theorem HfG_translate (r c : ℝ) (w : SDEState (d + d + 1)) :
    (HfG φ) r (w + c • (eac (d := d))) = Real.exp (-c) * (HfG φ) r w := by
  have hx : ∀ k, (w + c • (eac (d := d))) (ixc k) = w (ixc k) := fun k => by
    have : (eac (d := d)) (ixc k) = 0 := by simp [eac]
    simp [this]
  have ha : (w + c • (eac (d := d))) iac = w iac + c := by
    have : (eac (d := d)) iac = 1 := by simp [eac]
    simp [this]
  simp only [HfG, Nxf, PhifG, hx, ha]
  rw [show -(w iac + c) = -c + -w iac by ring, Real.exp_add]
  ring

/-- `(HfG φ)` does not see the `y` block. -/
theorem HfG_translate_y (r : ℝ) (c : SDEState d) (w : SDEState (d + d + 1)) :
    (HfG φ) r (w + pack 0 c 0) = 1 * (HfG φ) r w := by
  have hx : ∀ k, (w + pack 0 c 0) (ixc k) = w (ixc k) := fun k => by simp
  have ha : (w + pack 0 c 0) iac = w iac := by simp
  simp only [HfG, Nxf, PhifG, hx, ha, one_mul]

theorem HfG_fderiv_pack (r : ℝ) (x y : SDEState d) (a : ℝ) :
    fderiv ℝ ((HfG φ) r) (pack x y a) = Real.exp (-a) • fderiv ℝ ((HfG φ) r) (pack x 0 0) ∧
      fderiv ℝ (fderiv ℝ ((HfG φ) r)) (pack x y a) =
        Real.exp (-a) • fderiv ℝ (fderiv ℝ ((HfG φ) r)) (pack x 0 0) := by
  have h := fderiv12_translate (HfG_contDiff (φ := φ) r) (a • (eac (d := d))) (Real.exp (-a))
    (fun w => HfG_translate (φ := φ) r a w) (pack x y 0)
  have h' := fderiv12_translate (HfG_contDiff (φ := φ) r) (pack 0 y 0) 1
    (fun w => HfG_translate_y (φ := φ) r y w) (pack x 0 0)
  have e1 : pack x y 0 + a • (eac (d := d)) = pack x y a := by rw [pack_add_eac, zero_add]
  have e2 : pack x 0 0 + pack 0 y 0 = pack x y 0 := (pack_split x y).symm
  rw [e1] at h; rw [e2, one_smul, one_smul] at h'
  rw [h.1, h.2, h'.1, h'.2]
  exact ⟨rfl, rfl⟩

theorem HfG_fderiv_eac (r : ℝ) (u : SDEState (d + d + 1)) :
    fderiv ℝ ((HfG φ) r) u (eac (d := d)) = -(HfG φ) r u := by
  refine fderiv_eq_of_line ((HfG_contDiff (φ := φ) r).differentiable (by norm_num)) u _ ?_
  have e : (fun s : ℝ => (HfG φ) r (u + s • (eac (d := d)))) = fun s => Real.exp (-s) * (HfG φ) r u :=
    funext fun s => HfG_translate (φ := φ) r s u
  rw [e]
  have := ((hasDerivAt_id (0 : ℝ)).neg.exp).mul_const ((HfG φ) r u)
  simpa using this

/-- `D H0(u) v = e^{-a} (Σ φ'(x_k) v_k - v_a Φ)`. -/
theorem H0fG_fderiv (u v : SDEState (d + d + 1)) :
    fderiv ℝ (H0fG φ) u v = Real.exp (-u iac) *
      ((∑ k, deriv (φ k) (u (ixc k)) * v (ixc k)) - v iac * (PhifG φ) u) := by
  refine fderiv_eq_of_line ((H0fG_contDiff (φ := φ)).differentiable (by norm_num)) u v ?_
  have he := (((hasDerivAt_mul_const (v iac)).const_add (u iac)).neg (x := (0 : ℝ))).exp
  have hs : HasDerivAt (fun s : ℝ => ∑ k, (φ k) (u (ixc k) + s * v (ixc k)))
      (∑ k, deriv (φ k) (u (ixc k)) * v (ixc k)) 0 := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (v (ixc k))).const_add (u (ixc k))
    have h2 := (phiG_hasDeriv (φ := φ) k (u (ixc k) + id 0 * v (ixc k))).comp (0 : ℝ) h1
    refine h2.congr_deriv ?_
    simp only [id, zero_mul, add_zero, one_mul]
  have e : (fun s : ℝ => (H0fG φ) (u + s • v)) =
      fun s => Real.exp (-(u iac + s * v iac)) * ∑ k, (φ k) (u (ixc k) + s * v (ixc k)) := by
    funext s; simp [H0fG, PhifG]
  rw [e]
  refine (he.mul hs).congr_deriv ?_
  simp only [PhifG, Pi.neg_apply, zero_mul, add_zero, mul_zero]
  ring

/-- `D² H0(u)(v,v) = e^{-a} Σ φ''(x_k) v_k²` when `v_a = 0`. -/
theorem H0fG_fderiv2 (u v : SDEState (d + d + 1)) (hv : v iac = 0) :
    fderiv ℝ (fderiv ℝ (H0fG φ)) u v v = Real.exp (-u iac) *
      ∑ k, deriv (deriv (φ k)) (u (ixc k)) * v (ixc k) ^ 2 := by
  refine fderiv2_eq_of_line (H0fG_contDiff (φ := φ)) u v
    (φ' := fun s => Real.exp (-u iac) * ∑ k, deriv (φ k) (u (ixc k) + s * v (ixc k)) *
      v (ixc k)) (fun s => ?_) ?_
  · have e : (fun r : ℝ => (H0fG φ) (u + r • v)) =
        fun r => Real.exp (-u iac) * ∑ k, (φ k) (u (ixc k) + r * v (ixc k)) := by
      funext r; simp [H0fG, PhifG, hv]
    rw [e]
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun k _ => ?_)
    have h1 := ((hasDerivAt_id s).mul_const (v (ixc k))).const_add (u (ixc k))
    have h2 := (phiG_hasDeriv (φ := φ) k (u (ixc k) + id s * v (ixc k))).comp s h1
    exact h2.congr_deriv (by simp only [id, one_mul])
  · refine HasDerivAt.const_mul _ ?_
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (v (ixc k))).const_add (u (ixc k))
    have h2 := ((phiG_hasDeriv2 (φ := φ) k (u (ixc k) + 0 * v (ixc k))).comp (0 : ℝ) h1).mul_const
      (v (ixc k))
    refine h2.congr_deriv ?_
    simp only [Function.comp_apply, zero_mul, add_zero, id, one_mul]
    ring

theorem PhifG_pack (x y : SDEState d) (a : ℝ) : (PhifG φ) (pack x y a) = ∑ k, (φ k) (x k) := by
  simp [PhifG]

theorem HfG_drift_inside {r κ : ℝ} (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) (hx : ‖x‖ ^ 2 < r) :
    driftGen ((HfG φ) r) κ σx bx σy by' x y a = Real.exp (-a) * ((∑ k, deriv (φ k) (x k) * bx k) -
      κ * (∑ k, (φ k) (x k)) + (1 / 2) * ∑ j, ∑ k, deriv (deriv (φ k)) (x k) * σx (k, j) ^ 2) := by
  have hN : Nxf (pack x y a) < r := by rw [Nxf_pack]; exact hx
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (HfG_eq_H0fG_nhds (φ := φ) hN)
  unfold driftGen
  rw [h1, h2, H0fG_fderiv (φ := φ), Finset.sum_congr rfl (fun j _ => H0fG_fderiv2 (φ := φ) _ _ (by simp))]
  simp only [pack_ixc, pack_iac, PhifG_pack (φ := φ), scol_apply']
  rw [← Finset.mul_sum]
  ring

theorem HfG_drift_inside_le {r κ c₀ : ℝ} (σx : SDEDiffusion d) (bx : SDEState d)
    (σy : SDEDiffusion d) (by' : SDEState d) (x y : SDEState d) (a : ℝ) (hx : ‖x‖ ^ 2 < r)
    (hk : ∀ k, deriv (φ k) (x k) * bx k + (1 / 2) * ∑ j, deriv (deriv (φ k)) (x k) * σx (k, j) ^ 2
      ≤ c₀ * (φ k) (x k)) :
    driftGen ((HfG φ) r) κ σx bx σy by' x y a ≤ Real.exp (-a) * ((c₀ - κ) * ∑ k, (φ k) (x k)) := by
  rw [HfG_drift_inside (φ := φ) σx bx σy by' x y a hx]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hc : ∑ j, ∑ k, deriv (deriv (φ k)) (x k) * σx (k, j) ^ 2 =
      ∑ k, ∑ j, deriv (deriv (φ k)) (x k) * σx (k, j) ^ 2 := Finset.sum_comm
  have h2 : (1 / 2 : ℝ) * ∑ k, ∑ j, deriv (deriv (φ k)) (x k) * σx (k, j) ^ 2 =
      ∑ k, (1 / 2) * ∑ j, deriv (deriv (φ k)) (x k) * σx (k, j) ^ 2 := Finset.mul_sum _ _ _
  have hsum : ∑ k, (deriv (φ k) (x k) * bx k +
      (1 / 2) * ∑ j, deriv (deriv (φ k)) (x k) * σx (k, j) ^ 2) ≤ ∑ k, c₀ * (φ k) (x k) :=
    Finset.sum_le_sum fun k _ => hk k
  rw [Finset.sum_add_distrib] at hsum
  have h3 : ∑ k, c₀ * (φ k) (x k) = c₀ * ∑ k, (φ k) (x k) := (Finset.mul_sum _ _ _).symm
  rw [hc, h2]
  nlinarith

theorem HfG_deriv_bound (r : ℝ) : ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧ ∀ x : SDEState d,
    ‖fderiv ℝ ((HfG φ) r) (pack x 0 0)‖ ≤ B1 ∧ ∀ i i' : Fin (d + d + 1),
      |fderiv ℝ (fderiv ℝ ((HfG φ) r)) (pack x 0 0) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1)| ≤ B2 := by
  set ρ : ℝ := |r| + 2 with hρ
  have hD1 : Continuous (fderiv ℝ (HfG φ (d := d) r)) :=
    (HfG_contDiff (φ := φ) r).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (HfG φ (d := d) r))) :=
    ((HfG_contDiff (φ := φ) r).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hp1 : Continuous fun x : SDEState d => pack x (0 : SDEState d) 0 :=
    pack_continuous continuous_id continuous_const continuous_const
  have K2 := isCompact_closedBall (0 : SDEState d) ρ
  obtain ⟨B1, hB1⟩ := K2.exists_bound_of_continuousOn (hD1.comp hp1).continuousOn
  have hB2e : ∀ i i' : Fin (d + d + 1), ∃ B, ∀ x ∈ Metric.closedBall (0 : SDEState d) ρ,
      ‖fderiv ℝ (fderiv ℝ ((HfG φ) r)) (pack x 0 0) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1)‖ ≤ B := fun i i' =>
    K2.exists_bound_of_continuousOn
      (f := fun x : SDEState d => fderiv ℝ (fderiv ℝ ((HfG φ) r)) (pack x 0 0)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1))
      (((hD2.comp hp1).clm_apply continuous_const).clm_apply continuous_const).continuousOn
  choose Bc hBc using hB2e
  set B2 : ℝ := ∑ i, ∑ i', max (Bc i i') 0 with hB2def
  have hB20 : 0 ≤ B2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => le_max_right _ _
  have hBc2 : ∀ i i', max (Bc i i') 0 ≤ B2 := fun i i' =>
    (Finset.single_le_sum (f := fun i' => max (Bc i i') 0)
      (fun _ _ => le_max_right _ _) (Finset.mem_univ i')).trans
    (Finset.single_le_sum (f := fun i => ∑ i', max (Bc i i') 0)
      (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i))
  refine ⟨max B1 0, B2, le_max_right _ _, hB20, fun x => ?_⟩
  by_cases hN : r + 1 < ‖x‖ ^ 2
  · obtain ⟨h1, h2⟩ := HfG_fderiv_zero (φ := φ) (r := r) (u := pack x 0 0) (by rw [Nxf_pack]; exact hN)
    rw [h1, h2]
    exact ⟨by rw [norm_zero]; exact le_max_right _ _, fun i i' => by simpa using hB20⟩
  · have hxρ : ‖x‖ ≤ ρ := by
      by_contra hc
      replace hc := not_le.1 hc
      have hr0 := abs_nonneg r
      have hr1 := le_abs_self r
      have hxn := norm_nonneg x
      nlinarith
    have hmem : x ∈ Metric.closedBall (0 : SDEState d) ρ := mem_closedBall_zero_iff.2 hxρ
    refine ⟨(hB1 x hmem).trans (le_max_left _ _), fun i i' => ?_⟩
    have := hBc i i' x hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (hBc2 i i'))

/-- Global bound of the generator of `(HfG φ) r` (the clock term only helps). -/
theorem HfG_drift_bound (r S : ℝ) (hS : 0 ≤ S) : ∃ B : ℝ, 0 ≤ B ∧ ∀ κ : ℝ, 0 ≤ κ →
    ∀ (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d) (by' : SDEState d)
      (x y : SDEState d) (a : ℝ),
      (‖x‖ ^ 2 ≤ r + 1 → ‖σx‖ ≤ S ∧ ‖bx‖ ≤ S ∧ ‖σy‖ ≤ S ∧ ‖by'‖ ≤ S) →
      driftGen ((HfG φ) r) κ σx bx σy by' x y a ≤ Real.exp (-a) * B := by
  obtain ⟨B1, B2, hB1, hB2, hB⟩ := HfG_deriv_bound (φ := φ) (d := d) r
  set D : ℝ := ((d : ℝ) + d + 1) * (S + S) with hD
  have hD0 : 0 ≤ D := by positivity
  refine ⟨B1 * D + (1 / 2) * (d * (B2 * D ^ 2)), by positivity, fun κ hκ σx bx σy by' x y a hS' => ?_⟩
  have hea := Real.exp_pos (-a)
  by_cases hN : r + 1 < ‖x‖ ^ 2
  · obtain ⟨h1, h2⟩ := HfG_fderiv_zero (φ := φ) (r := r) (u := pack x y a) (by rw [Nxf_pack]; exact hN)
    unfold driftGen
    rw [h1, h2]
    simp only [ContinuousLinearMap.zero_apply, Finset.sum_const_zero, mul_zero, add_zero]
    positivity
  · obtain ⟨hσx, hbx, hσy, hby⟩ := hS' (not_lt.1 hN)
    obtain ⟨hL1, hL2⟩ := hB x
    obtain ⟨e1, e2⟩ := HfG_fderiv_pack (φ := φ) r x y a
    unfold driftGen
    have hsplit : pack bx by' κ = pack bx by' 0 + κ • (eac (d := d)) := by
      rw [pack_add_eac, zero_add]
    have hk : fderiv ℝ ((HfG φ) r) (pack x y a) (κ • (eac (d := d))) ≤ 0 := by
      rw [map_smul, HfG_fderiv_eac (φ := φ), smul_eq_mul]
      have := HfG_nonneg (φ := φ) r (pack x y a)
      nlinarith
    rw [hsplit, map_add]
    have t1 : fderiv ℝ ((HfG φ) r) (pack x y a) (pack bx by' 0) ≤ Real.exp (-a) * (B1 * D) := by
      rw [e1, ContinuousLinearMap.smul_apply, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ hea.le
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      refine mul_le_mul hL1 ((norm_pack0_le _ _).trans ?_) (norm_nonneg _) hB1
      exact mul_le_mul_of_nonneg_left (add_le_add hbx hby) (by positivity)
    have t2 : ∀ j, fderiv ℝ (fderiv ℝ ((HfG φ) r)) (pack x y a) (pack (scol σx j) (scol σy j) 0)
        (pack (scol σx j) (scol σy j) 0) ≤ Real.exp (-a) * (B2 * D ^ 2) := by
      intro j
      rw [e2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ hea.le
      have hc : ‖pack (scol σx j) (scol σy j) 0‖ ≤ D :=
        (norm_packcol_le _ _ _).trans (mul_le_mul_of_nonneg_left (add_le_add hσx hσy) (by positivity))
      set c := pack (scol σx j) (scol σy j) 0 with hcdef
      have hcs : ∑ i, |c i| ≤ D := by
        calc ∑ i, |c i| ≤ ∑ _i : Fin (d + d + 1), (‖σx‖ + ‖σy‖) :=
              Finset.sum_le_sum fun i _ => abs_packcol_le σx σy j i
          _ = ((d : ℝ) + d + 1) * (‖σx‖ + ‖σy‖) := by simp [mul_add]
          _ ≤ D := mul_le_mul_of_nonneg_left (add_le_add hσx hσy) (by positivity)
      have hcs0 : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      rw [clm2_coord]
      calc ∑ i, ∑ i', c i * c i' * fderiv ℝ (fderiv ℝ ((HfG φ) r)) (pack x 0 0)
            (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1)
          ≤ ∑ i, ∑ i', |c i| * |c i'| * B2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
            refine (le_abs_self _).trans ?_
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (hL2 i i') (by positivity)
        _ = B2 * (∑ i, |c i|) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i' _ => by ring
        _ ≤ B2 * D ^ 2 := by gcongr
    have t3 : ∑ j, fderiv ℝ (fderiv ℝ ((HfG φ) r)) (pack x y a) (pack (scol σx j) (scol σy j) 0)
        (pack (scol σx j) (scol σy j) 0) ≤ d * (Real.exp (-a) * (B2 * D ^ 2)) := by
      calc _ ≤ ∑ _j : Fin d, Real.exp (-a) * (B2 * D ^ 2) := Finset.sum_le_sum fun j _ => t2 j
        _ = _ := by simp
    nlinarith

theorem HfG_integrand_ok (r : ℝ) {X Y : ℝ≥0 → Ω → SDEState d} {HX HY : ℝ≥0 → Ω → SDEDiffusion d}
    (hHb : ∃ C, ∀ s ω, ‖X s ω‖ ^ 2 ≤ r + 1 → ‖HX s ω‖ ≤ C ∧ ‖HY s ω‖ ≤ C) :
    ∀ (i : Fin (d + d + 1)) (j : Fin d), ∃ C, ∀ s ω (a : ℝ), 0 ≤ a →
      |fderiv ℝ ((HfG φ) r) (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1) *
        pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i| ≤ C := by
  intro i j
  obtain ⟨B, B2', hB0, -, hB⟩ := HfG_deriv_bound (φ := φ) (d := d) r
  obtain ⟨C₀, hC₀⟩ := hHb
  refine ⟨B * (2 * |C₀|), fun s ω a ha => ?_⟩
  by_cases hN : r + 1 < ‖X s ω‖ ^ 2
  · have h0 := (HfG_fderiv_zero (φ := φ) (r := r) (u := pack (X s ω) (Y s ω) a)
      (by rw [Nxf_pack]; exact hN)).1
    rw [h0]
    simp only [ContinuousLinearMap.zero_apply, zero_mul, abs_zero]
    exact mul_nonneg hB0 (by positivity)
  · obtain ⟨h1, h2⟩ := hC₀ s ω (not_lt.1 hN)
    have hea := Real.exp_pos (-a)
    have he := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
    have hd' : |fderiv ℝ ((HfG φ) r) (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1)| ≤ B := by
      rw [(HfG_fderiv_pack (φ := φ) r (X s ω) (Y s ω) a).1]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hea]
      refine (mul_le_of_le_one_left (abs_nonneg _) he).trans ?_
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [EuclideanSpace.norm_single, norm_one, mul_one]
      exact (hB (X s ω)).1
    have hc := abs_packcol_le (HX s ω) (HY s ω) j i
    have hc' : |pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i| ≤ 2 * |C₀| := by
      have := le_abs_self C₀
      linarith
    rw [abs_mul]
    exact mul_le_mul hd' hc' (abs_nonneg _) hB0

theorem HfG_drift_continuous (r : ℝ) {α : Type*} [TopologicalSpace α] {κ a : α → ℝ}
    {σx σy : α → SDEDiffusion d} {bx by' x y : α → SDEState d}
    (hκ : Continuous κ) (hσx : Continuous σx) (hbx : Continuous bx) (hσy : Continuous σy)
    (hby : Continuous by') (hx : Continuous x) (hy : Continuous y) (ha : Continuous a) :
    Continuous fun p => driftGen ((HfG φ) r) (κ p) (σx p) (bx p) (σy p) (by' p) (x p) (y p) (a p) := by
  have hD1 : Continuous (fderiv ℝ (HfG φ (d := d) r)) :=
    (HfG_contDiff (φ := φ) r).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (HfG φ (d := d) r))) :=
    ((HfG_contDiff (φ := φ) r).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hpk := pack_continuous hx hy ha
  unfold driftGen
  refine ((hD1.comp hpk).clm_apply (pack_continuous hbx hby hκ)).add
    (continuous_const.mul (continuous_finsetSum _ fun j _ => ?_))
  have hv := pack_continuous (scol_continuous hσx j) (scol_continuous hσy j)
    (continuous_const (y := (0 : ℝ)))
  exact ((hD2.comp hpk).clm_apply hv).clm_apply hv

/-- Pointwise: inside the ball the drift is `≤ 0`, outside the clock rate is `≥ M`. -/
theorem HfG_drift_le_kap {r c R B M : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hR : 0 ≤ R) (hc : 0 ≤ c) (hM : 0 < M) (hB : 0 ≤ B)
    (hr : r = (R + 1) ^ 2 + 1)
    (hk : ∀ x : SDEState d, ‖x‖ ^ 2 < r → ∀ k, deriv (φ k) (x k) * b₀ x k +
      (1 / 2) * ∑ j, deriv (deriv (φ k)) (x k) * σ₀ x (k, j) ^ 2 ≤ c * (φ k) (x k))
    {x y : SDEState d} {σy : SDEDiffusion d} {by' : SDEState d} (a : ℝ)
    (hBd : ∀ κ, 0 ≤ κ → driftGen ((HfG φ) r) κ (σ₀ x) (b₀ x) σy by' x y a ≤ Real.exp (-a) * B) :
    driftGen ((HfG φ) r) (kapX c M R x) (σ₀ x) (b₀ x) σy by' x y a ≤
      B * (1 / M) * (Real.exp (-a) * kapX c M R x) := by
  have hk0 : 0 ≤ kapX c M R x := kapX_nonneg hc hM.le x
  have hea := Real.exp_pos (-a)
  have hfirst : 0 ≤ B * (1 / M) * (Real.exp (-a) * kapX c M R x) :=
    mul_nonneg (mul_nonneg hB (one_div_nonneg.2 hM.le)) (mul_nonneg hea.le hk0)
  by_cases hin : ‖x‖ ^ 2 < r
  · refine (HfG_drift_inside_le (φ := φ) (c₀ := c) _ _ _ _ x y a hin (hk x hin)).trans (le_trans ?_ hfirst)
    have hkc : c ≤ kapX c M R x := by
      unfold kapX; have := mul_nonneg hM.le (distB_nonneg R x); linarith
    have hΦ : 0 ≤ ∑ k, (φ k) (x k) := Finset.sum_nonneg fun k _ => hφ0.out k _
    have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hkc) hΦ
    nlinarith
  · have hx1 : R + 1 < ‖x‖ := by
      have h1 : (R + 1) ^ 2 < ‖x‖ ^ 2 := by rw [hr] at hin; linarith [not_lt.1 hin]
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg x) h1
    have hdist : 1 ≤ distB R x := by unfold distB; exact le_max_of_le_right (by linarith)
    have hkM : M ≤ kapX c M R x := by
      unfold kapX; have := mul_le_mul_of_nonneg_left hdist hM.le; linarith
    refine (hBd _ hk0).trans ?_
    have : B ≤ B * (1 / M) * kapX c M R x := by
      have h1 : 1 ≤ kapX c M R x / M := (one_le_div hM).2 hkM
      rw [show B * (1 / M) * kapX c M R x = B * (kapX c M R x / M) by ring]
      nlinarith
    calc Real.exp (-a) * B ≤ Real.exp (-a) * (B * (1 / M) * kapX c M R x) :=
          mul_le_mul_of_nonneg_left this hea.le
      _ = _ := by ring

/-- Pathwise: the `(HfG φ)`-generator integral is at most `B / M`. -/
theorem HfG_drift_integral_le {r c R B M : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hσ : Continuous σ₀) (hb : Continuous b₀)
    (hR : 0 ≤ R) (hc : 0 ≤ c) (hM : 0 < M) (hB : 0 ≤ B) (hr : r = (R + 1) ^ 2 + 1)
    (hk : ∀ x : SDEState d, ‖x‖ ^ 2 < r → ∀ k, deriv (φ k) (x k) * b₀ x k +
      (1 / 2) * ∑ j, deriv (deriv (φ k)) (x k) * σ₀ x (k, j) ^ 2 ≤ c * (φ k) (x k))
    {x : ℝ → SDEState d} (hx : Continuous x)
    (hBd : ∀ u κ, 0 ≤ κ → ∀ a, driftGen ((HfG φ) r) κ (σ₀ (x u)) (b₀ (x u)) (σ₀ (x u)) (b₀ (x u))
      (x u) (x u) a ≤ Real.exp (-a) * B)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, driftGen ((HfG φ) r) (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u)) (σ₀ (x u))
        (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kapX c M R (x v)) ≤
      B * (1 / M) := by
  have hgc : Continuous fun v => kapX c M R (x v) := kapX_comp_continuous c M R hx
  have hpc : Continuous fun u => ∫ v in (0 : ℝ)..u, kapX c M R (x v) :=
    continuous_iff_continuousAt.2 fun u => (hgc.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hcongr : ∫ u in (0 : ℝ)..t, driftGen ((HfG φ) r) (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
        (σ₀ (x u)) (b₀ (x u)) (x u) (x u)
        (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kapX c M R (x v)) =
      ∫ u in (0 : ℝ)..t, driftGen ((HfG φ) r) (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
        (σ₀ (x u)) (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..u, kapX c M R (x v)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by rw [Set.uIcc_of_le ht] at hu; exact hu.1
    simp only [Real.coe_toNNReal _ hu0]
  rw [hcongr]
  have hLc : Continuous fun u => driftGen ((HfG φ) r) (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
      (σ₀ (x u)) (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..u, kapX c M R (x v)) :=
    HfG_drift_continuous (φ := φ) r hgc (hσ.comp hx) (hb.comp hx) (hσ.comp hx) (hb.comp hx) hx hx hpc
  have hRc : Continuous fun u => B * (1 / M) *
      (Real.exp (-(∫ v in (0 : ℝ)..u, kapX c M R (x v))) * kapX c M R (x u)) :=
    continuous_const.mul ((Real.continuous_exp.comp hpc.neg).mul hgc)
  calc _ ≤ ∫ u in (0 : ℝ)..t, (B * (1 / M) *
        (Real.exp (-(∫ v in (0 : ℝ)..u, kapX c M R (x v))) * kapX c M R (x u))) :=
        intervalIntegral.integral_mono_on ht (hLc.intervalIntegrable _ _)
          (hRc.intervalIntegrable _ _) fun u _ =>
          HfG_drift_le_kap (φ := φ) hR hc hM hB hr hk _ (fun κ hκ => hBd u κ hκ _)
    _ = B * (1 / M) * (1 - Real.exp (-(∫ v in (0 : ℝ)..t, kapX c M R (x v)))) := by
        rw [intervalIntegral.integral_const_mul, integral_exp_neg_primitive hgc]
    _ ≤ B * (1 / M) := by
        have h1 := Real.exp_pos (-(∫ v in (0 : ℝ)..t, kapX c M R (x v)))
        have h2 : 0 ≤ B * (1 / M) := mul_nonneg hB (one_div_nonneg.2 hM.le)
        nlinarith

set_option maxHeartbeats 1000000 in
theorem lintegral_HfG_le [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {r c R B M S : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c) (hM : 0 < M) (hr : r = (R + 1) ^ 2 + 1)
    (hk : ∀ x : SDEState d, ‖x‖ ^ 2 < r → ∀ k, deriv (φ k) (x k) * b₀ x k +
      (1 / 2) * ∑ j, deriv (deriv (φ k)) (x k) * σ₀ x (k, j) ^ 2 ≤ c * (φ k) (x k))
    (hS0 : ∀ x : SDEState d, ‖x‖ ^ 2 ≤ r + 1 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (hB : 0 ≤ B) (hBd : ∀ κ, 0 ≤ κ → ∀ (σx : SDEDiffusion d) (bx : SDEState d)
      (σy : SDEDiffusion d) (by' : SDEState d) (x y : SDEState d) (a : ℝ),
      (‖x‖ ^ 2 ≤ r + 1 → ‖σx‖ ≤ S ∧ ‖bx‖ ≤ S ∧ ‖σy‖ ≤ S ∧ ‖by'‖ ≤ S) →
      driftGen ((HfG φ) r) κ σx bx σy by' x y a ≤ Real.exp (-a) * B)
    (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal ((HfG φ) r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω)))) ∂P ≤
      ENNReal.ofReal ((HfG φ) r (pack x₀ x₀ 0) + B * (1 / M)) := by
  obtain ⟨hXm, hXc, hXa, hX0, JX, -, -, hJX, -, hXeq⟩ := hX
  have hFb := HfG_integrand_ok (φ := φ) (Ω := Ω) r (X := X) (Y := X) (HX := fun s ω => σ₀ (X s ω))
    (HY := fun s ω => σ₀ (X s ω))
    ⟨S, fun s ω h => ⟨(hS0 _ h).1, (hS0 _ h).1⟩⟩
  have hX0' : ∀ᵐ ω ∂P, X 0 ω = x₀ := by filter_upwards [hX0] with ω h using h
  obtain ⟨Z, hZi, hZ0, hZeq⟩ := ito_coupled_F hW x₀ (X := X) (Y := X)
    (HX := fun s ω => σ₀ (X s ω)) (HY := fun s ω => σ₀ (X s ω)) (JX := JX) (JY := JX)
    (bX := fun s ω => b₀ (X s ω)) (bY := fun s ω => b₀ (X s ω)) hXm hXm hXc hXc hXa hXa
    (fun s => hσ.measurable.comp (hXa s)) (fun s => hσ.measurable.comp (hXa s))
    (fun ω => hσ.comp (hXc ω)) (fun ω => hσ.comp (hXc ω))
    (fun s => hb.measurable.comp (hXa s)) (fun s => hb.measurable.comp (hXa s))
    (fun ω => hb.comp (hXc ω)) (fun ω => hb.comp (hXc ω)) hJX hJX hXeq hXeq
    hX0' hX0' (κ := fun x _ => kapX c M R x) (kapX_comp_continuous c M R continuous_fst)
    (fun x _ => kapX_nonneg hc hM.le x) (HfG_contDiff (φ := φ) r) hFb t
  have h := lintegral_le_of_ito (E := fun _ => (0 : ℝ)) (β := B * (1 / M))
    (ae_of_all _ fun ω => HfG_nonneg (φ := φ) _ _) hZi hZ0 hZeq
    (ae_of_all _ fun ω => ?_) (integrable_const _)
  · simpa using h
  · rw [add_zero]
    exact HfG_drift_integral_le (φ := φ) hσ hb hR hc hM hB hr hk
      (x := fun u => X u.toNNReal ω) ((hXc ω).comp continuous_real_toNNReal)
      (fun u κ hκ a => hBd κ hκ _ _ _ _ _ _ a
        (fun h => ⟨(hS0 _ h).1, (hS0 _ h).2, (hS0 _ h).1, (hS0 _ h).2⟩)) t.val t.2

theorem measurable_HfG_path [MeasurableSpace Ω] {X : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hXc : ∀ ω, Continuous fun s => X s ω) (r c M R : ℝ)
    (t : ℝ≥0) :
    Measurable fun ω => (HfG φ) r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω))) := by
  have hA : Measurable fun ω => ∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω) :=
    measurable_intervalIntegral_of_continuous _ t
      (fun s _ => (kapX_comp_continuous c M R continuous_id).measurable.comp (hXm s))
      (fun ω => kapX_comp_continuous c M R (hXc ω))
  exact (HfG_contDiff (φ := φ) (d := d) r).continuous.measurable.comp
    ((pack_continuous continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).measurable.comp
      ((hXm t).prodMk ((hXm t).prodMk hA)))

/-- Markov step for the orthant functional `Φ(x) = Σ_k (x_k⁻)³`. -/
theorem prob_negG_le [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hXc : ∀ ω, Continuous fun s => X s ω)
    {r c M R K ε : ℝ} (hr : r = (R + 1) ^ 2 + 1) (hR : 0 ≤ R) (hε : 0 < ε) (t : ℝ≥0)
    (hI : ∫⁻ ω, ENNReal.ofReal ((HfG φ) r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω)))) ∂P ≤ ENNReal.ofReal K) :
    P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, (φ k) (X t ω k)} ≤
      ENNReal.ofReal (K / (Real.exp (-(c * t.val)) * ε)) := by
  set δ : ℝ := Real.exp (-(c * t.val)) * ε with hδ
  have hδ0 : 0 < δ := mul_pos (Real.exp_pos _) hε
  have hsub : {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, (φ k) (X t ω k)} ⊆
      {ω | ENNReal.ofReal δ ≤ ENNReal.ofReal ((HfG φ) r (pack (X t ω) (X t ω)
        (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω))))} := by
    intro ω ⟨hS, hQ⟩
    refine ENNReal.ofReal_le_ofReal ?_
    have hA : ∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω) = t.val * c := by
      have : ∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω) =
          ∫ _u in (0 : ℝ)..t.val, c := by
        refine intervalIntegral.integral_congr fun u hu => ?_
        rw [Set.uIcc_of_le t.2] at hu
        have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
        simp only [kapX, distB_eq_zero (hS _ hut), mul_zero, add_zero]
      rw [this, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    rw [hA]
    have hXt : ‖X t ω‖ ^ 2 ≤ r := by
      have := pow_le_pow_left₀ (norm_nonneg _) (hS t le_rfl) 2
      rw [hr]; nlinarith
    simp only [HfG, Nxf_pack, pack_iac, cutoff_eq_one hXt, one_mul, PhifG_pack (φ := φ)]
    rw [hδ, show t.val * c = c * t.val by ring]
    exact mul_le_mul_of_nonneg_left hQ.le (Real.exp_pos _).le
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal ((HfG φ) r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω))))) P :=
    (ENNReal.measurable_ofReal.comp (measurable_HfG_path (φ := φ) hXm hXc r c M R t)).aemeasurable
  have h1 : ENNReal.ofReal δ * P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, (φ k) (X t ω k)} ≤
      ENNReal.ofReal K :=
    ((mul_le_mul' le_rfl (measure_mono hsub)).trans
      (mul_meas_ge_le_lintegral₀ hmeas _)).trans hI
  have hne : ENNReal.ofReal δ ≠ 0 := by simpa using hδ0
  calc P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, (φ k) (X t ω k)}
      = (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ *
          P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, (φ k) (X t ω k)}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal K := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (K / δ) := by
        rw [ENNReal.ofReal_div_of_pos hδ0, ENNReal.div_eq_inv_mul]

end M11c

end ItoLib

-- ===== W =====
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

/-- `φ_δ(v) = (v² + δ)⁻¹`. -/
noncomputable def phiD (δ : ℝ) (v : ℝ) : ℝ := (v ^ 2 + δ)⁻¹

variable {δ : ℝ}

theorem phiD_den_pos (hδ : 0 < δ) (v : ℝ) : 0 < v ^ 2 + δ := by positivity

theorem phiD_nonneg (hδ : 0 < δ) (v : ℝ) : 0 ≤ phiD δ v :=
  (inv_pos.2 (phiD_den_pos hδ v)).le

theorem phiD_contDiff (hδ : 0 < δ) : ContDiff ℝ 2 (phiD δ) := by
  unfold phiD
  exact ((contDiff_id.pow 2).add contDiff_const).inv fun v => (phiD_den_pos hδ v).ne'

theorem hasDerivAt_phiD (hδ : 0 < δ) (v : ℝ) :
    HasDerivAt (phiD δ) (-(2 * v) / (v ^ 2 + δ) ^ 2) v := by
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2 + δ) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).add_const δ
  exact h1.inv (phiD_den_pos hδ v).ne'

theorem deriv_phiD (hδ : 0 < δ) : deriv (phiD δ) = fun v => -(2 * v) / (v ^ 2 + δ) ^ 2 :=
  funext fun v => (hasDerivAt_phiD hδ v).deriv

theorem deriv2_phiD (hδ : 0 < δ) (v : ℝ) :
    deriv (deriv (phiD δ)) v = (8 * v ^ 2 - 2 * (v ^ 2 + δ)) / (v ^ 2 + δ) ^ 3 := by
  rw [deriv_phiD hδ]
  have hq := phiD_den_pos hδ v
  have h1 : HasDerivAt (fun w : ℝ => w ^ 2 + δ) (2 * v) v := by
    simpa using (hasDerivAt_pow 2 v).add_const δ
  have h2 := h1.pow 2
  have h3 := ((hasDerivAt_id v).const_mul (2 : ℝ)).neg
  have h4 := h3.div h2 (by simpa using (pow_pos hq 2).ne')
  have h5 : HasDerivAt (fun w : ℝ => -(2 * w) / (w ^ 2 + δ) ^ 2)
      ((-(2 * 1) * ((v ^ 2 + δ) ^ 2) - -(2 * id v) * (↑2 * (v ^ 2 + δ) ^ (2 - 1) * (2 * v))) /
        ((v ^ 2 + δ) ^ 2) ^ 2) v := by
    refine (h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => by simp)).congr_deriv ?_
    simp
  rw [h5.deriv]
  simp only [id]
  field_simp
  ring

theorem phiD_d1_le (hδ : 0 < δ) (v F : ℝ) :
    deriv (phiD δ) v * (v * F) ≤ 2 * |F| * phiD δ v := by
  rw [deriv_phiD hδ]
  have hq := phiD_den_pos hδ v
  simp only [phiD]
  have hv : v ^ 2 ≤ v ^ 2 + δ := by linarith
  have e : -(2 * v) / (v ^ 2 + δ) ^ 2 * (v * F) = -(2 * F) * (v ^ 2 / (v ^ 2 + δ)) * (v ^ 2 + δ)⁻¹ := by
    field_simp
  rw [e]
  have hr0 : 0 ≤ v ^ 2 / (v ^ 2 + δ) := by positivity
  have hr1 : v ^ 2 / (v ^ 2 + δ) ≤ 1 := (div_le_one hq).2 hv
  have hi : 0 < (v ^ 2 + δ)⁻¹ := inv_pos.2 hq
  have hF : -(2 * F) ≤ 2 * |F| := by have := neg_abs_le F; linarith
  have hF0 : 0 ≤ 2 * |F| := by positivity
  have : -(2 * F) * (v ^ 2 / (v ^ 2 + δ)) ≤ 2 * |F| := by
    rcases le_or_gt 0 (-(2 * F)) with h | h
    · nlinarith
    · nlinarith
  exact mul_le_mul_of_nonneg_right this hi.le

theorem phiD_d2_le (hδ : 0 < δ) (v : ℝ) :
    deriv (deriv (phiD δ)) v * v ^ 2 ≤ 8 * phiD δ v := by
  rw [deriv2_phiD hδ]
  have hq := phiD_den_pos hδ v
  simp only [phiD]
  have hv : v ^ 2 ≤ v ^ 2 + δ := by linarith
  rw [div_mul_eq_mul_div, div_le_iff₀ (pow_pos hq 3)]
  have e : 8 * (v ^ 2 + δ)⁻¹ * (v ^ 2 + δ) ^ 3 = 8 * (v ^ 2 + δ) ^ 2 := by
    field_simp
  rw [e]
  have h2 : v ^ 2 * v ^ 2 ≤ (v ^ 2 + δ) * (v ^ 2 + δ) :=
    mul_le_mul hv hv (sq_nonneg v) hq.le
  nlinarith [sq_nonneg v]

/-- The Kolmogorov form of the coefficient condition for `φ_δ`. -/
theorem phiD_coef_le {d : ℕ} (hδ : 0 < δ) (v F G : ℝ) (Γc : Fin d → ℝ) {c₀ : ℝ}
    (hc : 3 * |F| + 4 * G ^ 2 * ∑ j, Γc j ^ 2 ≤ c₀) :
    deriv (phiD δ) v * (v * F) + (1 / 2) * ∑ j, deriv (deriv (phiD δ)) v * (v * G * Γc j) ^ 2
      ≤ c₀ * phiD δ v := by
  have h1 := phiD_d1_le hδ v F
  have hφ := phiD_nonneg hδ v
  have e2 : ∀ j, deriv (deriv (phiD δ)) v * (v * G * Γc j) ^ 2 ≤
      8 * phiD δ v * (G ^ 2 * Γc j ^ 2) := by
    intro j
    rw [show deriv (deriv (phiD δ)) v * (v * G * Γc j) ^ 2 =
      (deriv (deriv (phiD δ)) v * v ^ 2) * (G ^ 2 * Γc j ^ 2) by ring]
    exact mul_le_mul_of_nonneg_right (phiD_d2_le hδ v) (by positivity)
  have hs : ∑ j, deriv (deriv (phiD δ)) v * (v * G * Γc j) ^ 2 ≤
      ∑ j, 8 * phiD δ v * (G ^ 2 * Γc j ^ 2) := Finset.sum_le_sum fun j _ => e2 j
  have hR : ∑ j, 8 * phiD δ v * (G ^ 2 * Γc j ^ 2) = 8 * phiD δ v * (G ^ 2 * ∑ j, Γc j ^ 2) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [hR] at hs
  have h5 := mul_le_mul_of_nonneg_left hc hφ
  have hS : 0 ≤ G ^ 2 * ∑ j, Γc j ^ 2 := by positivity
  have hA : 0 ≤ |F| := abs_nonneg F
  nlinarith

/-- The coordinate family `φ j = φ_δ` for `j = k`, `0` otherwise. -/
noncomputable def famD {n : ℕ} (k : Fin n) (δ : ℝ) : Fin n → ℝ → ℝ :=
  fun j => if j = k then phiD δ else fun _ => 0

theorem famD_contDiff {n : ℕ} (k : Fin n) (hδ : 0 < δ) : ∀ j, ContDiff ℝ 2 (famD k δ j) := by
  intro j
  unfold famD
  split_ifs
  · exact phiD_contDiff hδ
  · exact contDiff_const

theorem famD_nonneg {n : ℕ} (k : Fin n) (hδ : 0 < δ) : ∀ j v, 0 ≤ famD k δ j v := by
  intro j v
  unfold famD
  split_ifs
  · exact phiD_nonneg hδ v
  · exact le_rfl

variable {n : ℕ}

/-- The Kolmogorov coefficient condition for the family `famD k δ` on the ball `‖x‖² < r`,
with a constant independent of `δ`. -/
theorem kolm_famD_coef (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {r : ℝ} (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (k : Fin n) (δ : ℝ), 0 < δ → ∀ x : SDEState n, ‖x‖ ^ 2 < r → ∀ j,
      deriv (famD k δ j) (x j) * drift C (0, x) j +
        (1 / 2) * ∑ i, deriv (deriv (famD k δ j)) (x j) * diffusion C (0, x) (j, i) ^ 2 ≤
          c * famD k δ j (x j) := by
  have hr0 : 0 ≤ r := by linarith
  choose Lf Gf hLf hGf hf using fun k => locLip_posPart_box (hC k).1 hr0
  choose Lg Gg hLg hGg hg using fun k => locLip_posPart_box (hC k).2 hr0
  set T : Fin n → ℝ := fun k => 3 * Gf k + 4 * Gg k ^ 2 * ∑ j, C.Γ j k ^ 2 with hT
  have hT0 : ∀ k, 0 ≤ T k := fun k => by
    simp only [hT]; have := hGf k; positivity
  refine ⟨∑ k, T k, Finset.sum_nonneg fun k _ => hT0 k, fun k δ hδ x hx j => ?_⟩
  by_cases hjk : j = k
  swap
  · have e : famD k δ j = fun _ => 0 := by unfold famD; rw [if_neg hjk]
    simp [e]
  rw [show famD k δ j = phiD δ by unfold famD; rw [if_pos hjk]]
  have hxr : ‖x‖ ≤ r := by nlinarith [norm_nonneg x]
  have hbox : ∀ i, |x i| ≤ r := fun i => by
    have := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at this
    linarith
  have hF := (hf j x x hbox hbox).2
  have hG := (hg j x x hbox hbox).2
  have hG2 : C.g j (posPart x) ^ 2 ≤ Gg j ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hG 2
  have hS : 0 ≤ ∑ i, C.Γ i j ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hck : 3 * |C.f j (posPart x)| + 4 * C.g j (posPart x) ^ 2 * ∑ i, C.Γ i j ^ 2 ≤
      ∑ k, T k := by
    refine le_trans ?_ (Finset.single_le_sum (fun k _ => hT0 k) (Finset.mem_univ j))
    simp only [hT]
    have := mul_le_mul_of_nonneg_right hG2 hS
    nlinarith
  exact phiD_coef_le hδ (x j) (C.f j (posPart x)) (C.g j (posPart x)) (fun i => C.Γ i j) hck

theorem famD_sum {k : Fin n} (v : SDEState n) : ∑ j, famD k δ j (v j) = phiD δ (v k) := by
  rw [Finset.sum_eq_single k]
  · simp [famD]
  · intro j _ hj; simp [famD, hj]
  · simp

theorem phiD_le_inv_sq (hδ : 0 < δ) {v : ℝ} (hv : v ≠ 0) : phiD δ v ≤ 1 / v ^ 2 := by
  rw [one_div]
  exact inv_anti₀ (by positivity) (by linarith)

/-- lemma_3_1 clause 3 (interior coordinates, fixed time): `x_k > 0` gives `X_t k ≠ 0` a.s. -/
theorem coord_ne_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (k : Fin n) (hk : 0 < x₀ k) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω k ≠ 0 := by
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  have hX' : SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => x₀) Y := hY
  have hXm : ∀ s, Measurable (Y s) := hX'.1
  have hXc : ∀ ω, Continuous fun s => Y s ω := hX'.2.1
  set K0 : ℝ := 1 / x₀ k ^ 2 + 1 with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hnull : ∀ R : ℕ, P {ω | (∀ s ≤ t, ‖Y s ω‖ ≤ (R : ℝ)) ∧ Y t ω k = 0} = 0 := by
    intro R
    set r : ℝ := ((R : ℝ) + 1) ^ 2 + 1 with hr
    have hr2 : 2 ≤ r := by have : (0 : ℝ) ≤ R := R.cast_nonneg; nlinarith
    obtain ⟨c, hc0, hkc⟩ := kolm_famD_coef C hC hr2
    obtain ⟨Cσ, hCσ⟩ := (isCompact_closedBall (0 : SDEState n) (r + 1)).exists_bound_of_continuousOn
      hσc.continuousOn
    obtain ⟨Cb, hCb⟩ := (isCompact_closedBall (0 : SDEState n) (r + 1)).exists_bound_of_continuousOn
      hbc.continuousOn
    set S : ℝ := max (max Cσ Cb) 0 with hSdef
    have hS : 0 ≤ S := le_max_right _ _
    have hS0 : ∀ x : SDEState n, ‖x‖ ^ 2 ≤ r + 1 →
        ‖diffusion C (0, x)‖ ≤ S ∧ ‖drift C (0, x)‖ ≤ S := by
      intro x hx
      have hxb : x ∈ Metric.closedBall (0 : SDEState n) (r + 1) := by
        rw [mem_closedBall_zero_iff]; nlinarith [norm_nonneg x]
      exact ⟨(hCσ x hxb).trans ((le_max_left _ _).trans (le_max_left _ _)),
        (hCb x hxb).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
    set A : ℝ := 2 * K0 / Real.exp (-(c * t.val)) with hA
    have hbound : ∀ N : ℕ, P {ω | (∀ s ≤ t, ‖Y s ω‖ ≤ (R : ℝ)) ∧ Y t ω k = 0} ≤
        ENNReal.ofReal (A * (1 / ((N : ℝ) + 1))) := by
      intro N
      set δ' : ℝ := 1 / ((N : ℝ) + 1) with hδ'
      have hδ : 0 < δ' := Nat.one_div_pos_of_nat
      have : Fact (∀ j, ContDiff ℝ 2 (famD k δ' j)) := ⟨famD_contDiff k hδ⟩
      have : Fact (∀ j v, 0 ≤ famD k δ' j v) := ⟨famD_nonneg k hδ⟩
      obtain ⟨Bc, hBc0, hBd⟩ := HfG_drift_bound (φ := famD k δ') (d := n) r S hS
      have hM : (0 : ℝ) < Bc + 1 := by linarith
      have hI := lintegral_HfG_le (φ := famD k δ') hB x₀ hσc hbc hX' (R := (R : ℝ))
        (M := Bc + 1) R.cast_nonneg hc0 hM hr (fun x hx j => hkc k δ' hδ x hx j) hS0 hBc0
        (fun κ hκ σx bx σy by' x y a h => hBd κ hκ σx bx σy by' x y a h) t
      have hε : (0 : ℝ) < 1 / (2 * δ') := by positivity
      have h := prob_negG_le (φ := famD k δ') hXm hXc hr R.cast_nonneg hε t hI
      have hH : HfG (famD k δ') r (pack x₀ x₀ 0) ≤ 1 / x₀ k ^ 2 := by
        simp only [HfG, PhifG_pack (φ := famD k δ'), famD_sum, pack_iac, neg_zero,
          Real.exp_zero, one_mul]
        exact (mul_le_of_le_one_left (phiD_nonneg hδ _) (cutoff_le_one _ _)).trans
          (phiD_le_inv_sq hδ hk.ne')
      have hB1 : Bc * (1 / (Bc + 1)) ≤ 1 := by
        rw [mul_one_div, div_le_one hM]; linarith
      have hKle : HfG (famD k δ') r (pack x₀ x₀ 0) + Bc * (1 / (Bc + 1)) ≤ K0 := by
        rw [hK0]; linarith
      have hsub : {ω | (∀ s ≤ t, ‖Y s ω‖ ≤ (R : ℝ)) ∧ Y t ω k = 0} ⊆
          {ω | (∀ s ≤ t, ‖Y s ω‖ ≤ (R : ℝ)) ∧ 1 / (2 * δ') < ∑ j, famD k δ' j (Y t ω j)} := by
        rintro ω ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [famD_sum, h2]
        simp only [phiD]
        rw [show (0 : ℝ) ^ 2 + δ' = δ' by ring, one_div]
        exact inv_strictAnti₀ hδ (by linarith)
      have he : 0 < Real.exp (-(c * t.val)) := Real.exp_pos _
      refine (measure_mono hsub).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
      calc (HfG (famD k δ') r (pack x₀ x₀ 0) + Bc * (1 / (Bc + 1))) /
            (Real.exp (-(c * t.val)) * (1 / (2 * δ')))
          ≤ K0 / (Real.exp (-(c * t.val)) * (1 / (2 * δ'))) :=
            div_le_div_of_nonneg_right hKle (by positivity)
        _ = A * δ' := by rw [hA]; field_simp
    have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (A * (1 / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul A)
      rw [mul_zero] at this
      simpa using (ENNReal.tendsto_ofReal this)
    exact le_antisymm (ge_of_tendsto' hlim hbound) zero_le
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null fun R => hnull R)
  intro ω hω
  simp only [Set.mem_setOf_eq, not_not] at hω
  obtain ⟨Cp, hCp⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hXc ω).continuousOn
  obtain ⟨R, hR⟩ := exists_nat_ge Cp
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨R, fun s hs => (hCp s ⟨zero_le, hs⟩).trans hR, hω⟩

end M11d

end ItoLib

-- ===== TA =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TA
/-! TA (s31): universe-polymorphic Markov statement (Ω : Type*), for the theorem_1_1 glue. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end TA

end ItoLib

-- ===== TC =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TC
/-! TC (s31): the new child `StochKolmogorov.Persist.markov_property` of the theorem_1_1 reduction. -/
open StochKolmogorov.Persist
variable {n : ℕ}

end TC

end ItoLib

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open StochKolmogorov.Persist in
open EthierKurtz in
set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (k : Fin n) (hk : 0 < x₀ k) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω k ≠ 0 := by
  exact ItoLib.coord_ne_zero P C B hB hC k hk hY t
