-- Prove2me | solution 1 for StochKolmogorov.Persist.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T07:31:37.282518+00:00
-- url     : https://prove2.me/submissions/254e7f15-bcbb-4ed6-b0d4-1c1c91c92cff

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_TotalVariationDist
import Theorems.Thm_EthierKurtz_brownian_ito_integral_and_formula
import Theorems.Thm_EthierKurtz_sde_markov_property_lipschitz
import Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed

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

theorem markov_core [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀)
    (s₁ : ℕ → SDEState d → SDEDiffusion d) (b₁ : ℕ → SDEState d → SDEState d) (S L : ℕ → ℝ)
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL : ∀ R, 0 ≤ L R)
    (hSg : ∀ R x, ‖s₁ R x‖ ≤ S R ∧ ‖b₁ R x‖ ≤ S R)
    (hLg : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L R * ‖x - y‖)
    (hag : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {D : Set (SDEState d)} {X : SDEState d → ℝ≥0 → Ω → SDEState d}
    (hX : ∀ y ∈ D, SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) (X y))
    (t : ℝ≥0) {f : SDEState d → ℝ} (hf : Measurable f) {K Lf : ℝ} (hfK : ∀ x, |f x| ≤ K)
    (hLf : 0 ≤ Lf) (hfL : ∀ x x', |f x - f x'| ≤ Lf * ‖x - x'‖) :
    ∃ g : SDEState d → ℝ, Measurable g ∧ (∀ y, |g y| ≤ K) ∧
      (∀ y ∈ D, g y = ∫ ω, f (X y t ω) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) →
        ∫ ω, f (X x (s + t) ω) ∂P = ∫ ω, g (X x s ω) ∂P := by
  exact EthierKurtz.sde_markov_property_lipschitz hW hσ hb s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX t hf hfK hLf hfL
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

theorem thick_props {δ : ℝ} (hδ : 0 < δ) (F : Set (SDEState d)) :
    Measurable (fun y => (thickenedIndicator hδ F y : ℝ)) ∧
      (∀ y, |(thickenedIndicator hδ F y : ℝ)| ≤ 1) ∧
      ∀ y y', |(thickenedIndicator hδ F y : ℝ) - thickenedIndicator hδ F y'| ≤ δ⁻¹ * ‖y - y'‖ := by
  refine ⟨(NNReal.continuous_coe.comp (thickenedIndicator hδ F).continuous).measurable,
    fun y => ?_, fun y y' => ?_⟩
  · rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    exact_mod_cast thickenedIndicator_le_one hδ F y
  · have := (lipschitzWith_thickenedIndicator hδ F).dist_le_mul y y'
    rw [NNReal.dist_eq, dist_eq_norm] at this
    simpa [Real.coe_toNNReal _ hδ.le] using this

variable [MeasurableSpace Ω] {P : Measure Ω}

theorem lint_thick [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) (F : Set (SDEState d))
    {V : Ω → SDEState d} (hV : Measurable V) :
    ∫⁻ y, (thickenedIndicator hδ F y : ℝ≥0∞) ∂(P.map V) =
      ENNReal.ofReal (∫ ω, (thickenedIndicator hδ F (V ω) : ℝ) ∂P) := by
  obtain ⟨hm, hb, -⟩ := thick_props hδ F
  have hmE : Measurable fun y => (thickenedIndicator hδ F y : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp (thickenedIndicator hδ F).continuous).measurable
  rw [lintegral_map hmE hV,
    ofReal_integral_eq_lintegral_ofReal (f := fun ω => (thickenedIndicator hδ F (V ω) : ℝ))
      (memLp_one_iff_integrable.1 (MemLp.of_bound (hm.comp hV).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hb _)))
      (ae_of_all _ fun ω => NNReal.coe_nonneg _)]
  simp

theorem markov_of_core [IsProbabilityMeasure P] {D : Set (SDEState d)} (hDm : MeasurableSet D)
    {X : SDEState d → ℝ≥0 → Ω → SDEState d} (hXm : ∀ y ∈ D, ∀ t, Measurable (X y t)) (t : ℝ≥0)
    (Hc : ∀ (F : Set (SDEState d)), IsClosed F → ∀ n : ℕ, ∃ g : SDEState d → ℝ, Measurable g ∧
      (∀ y ∈ D, g y = ∫ ω, (thickenedIndicator (Nat.one_div_pos_of_nat (n := n)) F (X y t ω) : ℝ) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) →
        ∫ ω, (thickenedIndicator (Nat.one_div_pos_of_nat (n := n)) F (X x (s + t) ω) : ℝ) ∂P =
          ∫ ω, g (X x s ω) ∂P) :
    ∃ κ : Kernel (SDEState d) (SDEState d), IsMarkovKernel κ ∧ (∀ x ∈ D, κ x = P.map (X x t)) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, (∀ᵐ ω ∂P, X x s ω ∈ D) → ∀ A, MeasurableSet A →
        P.map (X x (s + t)) A = ∫⁻ y, P.map (X y t) A ∂(P.map (X x s)) := by
  classical
  choose g hgm hgD hgck using Hc
  set κ0 : SDEState d → Measure (SDEState d) :=
    fun x => if x ∈ D then P.map (X x t) else Measure.dirac x with hκ0
  have hprob : ∀ x, IsProbabilityMeasure (κ0 x) := fun x => by
    by_cases hx : x ∈ D
    · simp only [hκ0, if_pos hx]; exact Measure.isProbabilityMeasure_map (hXm x hx t).aemeasurable
    · simp only [hκ0, if_neg hx]; infer_instance
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : ∀ F (hF : IsClosed F), ∀ x ∈ D,
      Tendsto (fun n => ENNReal.ofReal (g F hF n x)) atTop (𝓝 (κ0 x F)) := by
    intro F hF x hx
    have := tendsto_lintegral_thickenedIndicator_of_isClosed (P.map (X x t)) hF
      (fun n => Nat.one_div_pos_of_nat) hδ
    simp only [hκ0, if_pos hx]
    refine this.congr fun n => ?_
    rw [lint_thick _ _ (hXm x hx t), hgD F hF n x hx]
  have hmeasF : ∀ F, IsClosed F → Measurable fun x => κ0 x F := by
    intro F hF
    refine measurable_of_tendsto_metrizable (f := fun n => D.piecewise
      (fun x => ENNReal.ofReal (g F hF n x)) (fun x => Measure.dirac x F)) (fun n => ?_) ?_
    · refine Measurable.piecewise hDm (ENNReal.measurable_ofReal.comp (hgm F hF n)) ?_
      have : (fun x => Measure.dirac x F) = F.indicator 1 := funext fun x =>
        Measure.dirac_apply' x hF.measurableSet
      rw [this]; exact measurable_one.indicator hF.measurableSet
    · rw [tendsto_pi_nhds]
      intro x
      by_cases hx : x ∈ D
      · have e : ∀ n : ℕ, D.piecewise (fun x => ENNReal.ofReal (g F hF n x))
            (fun x => Measure.dirac x F) x = ENNReal.ofReal (g F hF n x) := fun n =>
          Set.piecewise_eq_of_mem _ _ _ hx
        simp only [e]; exact hlim F hF x hx
      · have e : ∀ n : ℕ, D.piecewise (fun x => ENNReal.ofReal (g F hF n x))
            (fun x => Measure.dirac x F) x = Measure.dirac x F := fun n =>
          Set.piecewise_eq_of_notMem _ _ _ hx
        simp only [e, hκ0, if_neg hx]; exact tendsto_const_nhds
  have hgen : (inferInstance : MeasurableSpace (SDEState d)) =
      MeasurableSpace.generateFrom {s | IsClosed s} :=
    (BorelSpace.measurable_eq (α := SDEState d)).trans borel_eq_generateFrom_isClosed
  haveI := hprob
  have hκm : Measurable κ0 := Measurable.measure_of_isPiSystem_of_isProbabilityMeasure hgen
    isPiSystem_isClosed fun F hF => hmeasF F hF
  refine ⟨⟨κ0, hκm⟩, ⟨fun x => hprob x⟩, fun x hx => by
    show κ0 x = _; simp only [hκ0, if_pos hx], ?_⟩
  intro x hx s hD A hA
  have hXs := hXm x hx s
  have hDmap : ∀ᵐ y ∂(P.map (X x s)), y ∈ D := (ae_map_iff hXs.aemeasurable hDm).2 hD
  haveI : IsProbabilityMeasure (P.map (X x (s + t))) :=
    Measure.isProbabilityMeasure_map (hXm x hx (s + t)).aemeasurable
  haveI : IsProbabilityMeasure (P.map (X x s)) := Measure.isProbabilityMeasure_map hXs.aemeasurable
  have hbind_univ : (P.map (X x s)).bind κ0 Set.univ = 1 := by
    rw [Measure.bind_apply MeasurableSet.univ hκm.aemeasurable]
    simp [fun y => (hprob y).measure_univ]
  have hbind : P.map (X x (s + t)) = (P.map (X x s)).bind κ0 := by
    refine ext_of_generate_finite _ hgen isPiSystem_isClosed (fun F hF => ?_) (by
      rw [hbind_univ, measure_univ])
    haveI : IsFiniteMeasure ((P.map (X x s)).bind κ0) := ⟨by rw [hbind_univ]; exact ENNReal.one_lt_top⟩
    have h1 := tendsto_lintegral_thickenedIndicator_of_isClosed (P.map (X x (s + t))) hF
      (fun n => Nat.one_div_pos_of_nat) hδ
    have h2 := tendsto_lintegral_thickenedIndicator_of_isClosed ((P.map (X x s)).bind κ0) hF
      (fun n => Nat.one_div_pos_of_nat) hδ
    refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
    obtain ⟨hm, hb, -⟩ := thick_props (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F
    have hgnn : ∀ y ∈ D, 0 ≤ g F hF n y := fun y hy => by
      rw [hgD F hF n y hy]; exact integral_nonneg fun ω => NNReal.coe_nonneg _
    have hgb : ∀ y ∈ D, |g F hF n y| ≤ 1 := fun y hy => by
      rw [hgD F hF n y hy, abs_of_nonneg (integral_nonneg fun ω => NNReal.coe_nonneg _)]
      refine (integral_mono_of_nonneg (ae_of_all _ fun ω => NNReal.coe_nonneg _)
        (integrable_const (1 : ℝ)) (ae_of_all _ fun ω => ?_)).trans (by simp)
      exact (le_abs_self _).trans (hb _)
    have hmE : Measurable fun y => (thickenedIndicator (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F y : ℝ≥0∞) :=
      (ENNReal.continuous_coe.comp (thickenedIndicator _ F).continuous).measurable
    rw [Measure.lintegral_bind hκm.aemeasurable hmE.aemeasurable,
      lint_thick _ _ (hXm x hx (s + t)), hgck F hF n x hx s hD,
      lintegral_map' ?_ hXs.aemeasurable]
    · rw [ofReal_integral_eq_lintegral_ofReal]
      · refine lintegral_congr_ae (hD.mono fun ω hω => ?_)
        simp only [hκ0, if_pos hω]
        rw [lint_thick _ _ (hXm _ hω t), hgD F hF n _ hω]
      · exact memLp_one_iff_integrable.1 (MemLp.of_bound ((hgm F hF n).comp hXs).aestronglyMeasurable 1
          (hD.mono fun ω hω => by rw [Real.norm_eq_abs]; exact hgb _ hω))
      · exact hD.mono fun ω hω => hgnn _ hω
    · exact ((Measure.measurable_lintegral hmE).comp hκm).aemeasurable
  rw [hbind, Measure.bind_apply hA hκm.aemeasurable]
  refine lintegral_congr_ae (hDmap.mono fun y hy => ?_)
  simp only [hκ0, if_pos hy]

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
    refine ⟨Lm + max C 0 / δ, add_nonneg Lm.coe_nonneg (div_nonneg (le_max_right _ _) hδpos.le),
      fun x hx y hy => ?_⟩
    by_cases hxy : dist x y < δ
    · obtain ⟨z, hzT, hxz⟩ : ∃ z ∈ T, x ∈ Metric.ball (z : α) (r z / 2) := by
        have := hT hx; simp only [Set.mem_iUnion] at this
        obtain ⟨z, hz, h⟩ := this; exact ⟨z, hz, h⟩
      have hδz : δ ≤ r z / 2 := Finset.inf'_le _ hzT
      have hx' : x ∈ Metric.ball (z : α) (r z) ∩ s :=
        ⟨Metric.ball_subset_ball (by linarith only [hr z]) hxz, hKs hx⟩
      have hy' : y ∈ Metric.ball (z : α) (r z) ∩ s := by
        refine ⟨?_, hKs hy⟩
        rw [Metric.mem_ball] at hxz ⊢
        calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
          _ < δ + r z / 2 := by rw [dist_comm]; exact add_lt_add hxy hxz
          _ ≤ r z := by linarith only [hδz]
      have h1 := (hL z).dist_le_mul x hx' y hy'
      have h2 : (L z : ℝ) ≤ Lm := by exact_mod_cast Finset.le_sup (f := L) hzT
      have h3 : 0 ≤ max C 0 / δ * dist x y :=
        mul_nonneg (div_nonneg (le_max_right _ _) hδpos.le) dist_nonneg
      have h4 := mul_le_mul_of_nonneg_right h2 (dist_nonneg (x := x) (y := y))
      linarith only [h1, h3, h4]
    · replace hxy := not_lt.1 hxy
      have h1 : dist (f x) (f y) ≤ max C 0 :=
        (hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (le_max_left _ _)
      have h2 : max C 0 ≤ max C 0 / δ * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      have h3 : 0 ≤ (Lm : ℝ) * dist x y := mul_nonneg Lm.coe_nonneg dist_nonneg
      linarith only [h1, h2, h3]
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
  refine (abs_max_sub_max_le_max (-M) (min M a) (-M) (min M b)).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
  refine (abs_min_sub_min_le_max M a M b).trans ?_
  rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]

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

variable {φ : Fin d → ℝ → ℝ} [hφ : Fact (∀ k, ContDiff ℝ 2 (φ k))]
  [hφ0 : Fact (∀ k v, 0 ≤ φ k v)]

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

variable {δ : ℝ}

variable {n : ℕ}

/-- `orthant_inv` for one solution (no solution family needed). -/
theorem orthant_inv1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Y t ω ∈ orthant n := by
  exact StochKolmogorov.Persist.orthant_invariance_closed P C B hB hC hx₀ hY t
end M11d

end ItoLib

-- ===== U =====
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

-- ===== Y =====
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

noncomputable def PhifL (ψ : ℝ → ℝ) (cv : SDEState d) (u : SDEState (d + d + 1)) : ℝ :=
  ψ (∑ k, cv k * u (ixc k))

noncomputable def H0fL (ψ : ℝ → ℝ) (cv : SDEState d) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * PhifL ψ cv u

noncomputable def HfL (ψ : ℝ → ℝ) (cv : SDEState d) (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * (cutoff r (Nxf u) * PhifL ψ cv u)

variable {ψ : ℝ → ℝ} {cv : SDEState d} [hψ : Fact (ContDiff ℝ 2 ψ)] [hψ0 : Fact (∀ v, 0 ≤ ψ v)]

theorem psiL_hasDeriv (v : ℝ) : HasDerivAt ψ (deriv ψ v) v :=
  ((hψ.out.differentiable (by norm_num)) v).hasDerivAt

theorem psiL_hasDeriv2 (v : ℝ) : HasDerivAt (deriv ψ) (deriv (deriv ψ) v) v := by
  have h2 : ContDiff ℝ (1 + 1) ψ := hψ.out.of_le (by norm_num)
  have h1 : ContDiff ℝ 1 (deriv ψ) := (contDiff_succ_iff_deriv.1 h2).2.2
  exact ((h1.differentiable (by norm_num)) v).hasDerivAt

theorem PhifL_contDiff : ContDiff ℝ 2 (PhifL ψ cv (d := d)) := by
  unfold PhifL
  exact hψ.out.comp (ContDiff.sum fun k _ => contDiff_const.mul (coord_contDiff _))

theorem PhifL_nonneg (u : SDEState (d + d + 1)) : 0 ≤ (PhifL ψ cv) u := hψ0.out _

theorem ellL_line (u v : SDEState (d + d + 1)) (s : ℝ) :
    ∑ k, cv k * (u + s • v) (ixc k) = (∑ k, cv k * u (ixc k)) + s * ∑ k, cv k * v (ixc k) := by
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem H0fL_contDiff : ContDiff ℝ 2 (H0fL ψ cv (d := d)) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul (PhifL_contDiff (ψ := ψ) (cv := cv))

theorem HfL_contDiff (r : ℝ) : ContDiff ℝ 2 (HfL ψ cv (d := d) r) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul
    (((cutoff_contDiff r).comp Nxf_contDiff).mul (PhifL_contDiff (ψ := ψ) (cv := cv)))

theorem HfL_nonneg (r : ℝ) (u : SDEState (d + d + 1)) : 0 ≤ (HfL ψ cv) r u :=
  mul_nonneg (Real.exp_pos _).le (mul_nonneg (cutoff_nonneg _ _) (PhifL_nonneg (ψ := ψ) (cv := cv) u))

theorem HfL_eq_H0fL_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : Nxf u < r) :
    (HfL ψ cv) r =ᶠ[𝓝 u] (H0fL ψ cv) := by
  have hc : ContinuousAt (Nxf (d := d)) u := (Nxf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (gt_mem_nhds hu)] with w hw
  simp only [HfL, H0fL, cutoff_eq_one hw.le, one_mul]

theorem HfL_zero_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nxf u) :
    (HfL ψ cv) r =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
  have hc : ContinuousAt (Nxf (d := d)) u := (Nxf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hu)] with w hw
  simp only [HfL, cutoff_eq_zero hw.le, zero_mul, mul_zero]

theorem HfL_fderiv_zero {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nxf u) :
    fderiv ℝ ((HfL ψ cv) r) u = 0 ∧ fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) u = 0 := by
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (HfL_zero_nhds (ψ := ψ) (cv := cv) hu)
  refine ⟨h1.trans (fderiv_const_apply _), h2.trans ?_⟩
  rw [show (fderiv ℝ fun _ : SDEState (d + d + 1) => (0 : ℝ)) = fun _ => 0 from
    funext fun w => fderiv_const_apply _]
  exact fderiv_const_apply _

theorem HfL_translate (r c : ℝ) (w : SDEState (d + d + 1)) :
    (HfL ψ cv) r (w + c • (eac (d := d))) = Real.exp (-c) * (HfL ψ cv) r w := by
  have hx : ∀ k, (w + c • (eac (d := d))) (ixc k) = w (ixc k) := fun k => by
    have : (eac (d := d)) (ixc k) = 0 := by simp [eac]
    simp [this]
  have ha : (w + c • (eac (d := d))) iac = w iac + c := by
    have : (eac (d := d)) iac = 1 := by simp [eac]
    simp [this]
  simp only [HfL, Nxf, PhifL, hx, ha]
  rw [show -(w iac + c) = -c + -w iac by ring, Real.exp_add]
  ring

/-- `(HfL ψ cv)` does not see the `y` block. -/
theorem HfL_translate_y (r : ℝ) (c : SDEState d) (w : SDEState (d + d + 1)) :
    (HfL ψ cv) r (w + pack 0 c 0) = 1 * (HfL ψ cv) r w := by
  have hx : ∀ k, (w + pack 0 c 0) (ixc k) = w (ixc k) := fun k => by simp
  have ha : (w + pack 0 c 0) iac = w iac := by simp
  simp only [HfL, Nxf, PhifL, hx, ha, one_mul]

theorem HfL_fderiv_pack (r : ℝ) (x y : SDEState d) (a : ℝ) :
    fderiv ℝ ((HfL ψ cv) r) (pack x y a) = Real.exp (-a) • fderiv ℝ ((HfL ψ cv) r) (pack x 0 0) ∧
      fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x y a) =
        Real.exp (-a) • fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x 0 0) := by
  have h := fderiv12_translate (HfL_contDiff (ψ := ψ) (cv := cv) r) (a • (eac (d := d))) (Real.exp (-a))
    (fun w => HfL_translate (ψ := ψ) (cv := cv) r a w) (pack x y 0)
  have h' := fderiv12_translate (HfL_contDiff (ψ := ψ) (cv := cv) r) (pack 0 y 0) 1
    (fun w => HfL_translate_y (ψ := ψ) (cv := cv) r y w) (pack x 0 0)
  have e1 : pack x y 0 + a • (eac (d := d)) = pack x y a := by rw [pack_add_eac, zero_add]
  have e2 : pack x 0 0 + pack 0 y 0 = pack x y 0 := (pack_split x y).symm
  have k1 := congrArg (fderiv ℝ ((HfL ψ cv) r)) e1
  have k1' := congrArg (fderiv ℝ (fderiv ℝ ((HfL ψ cv) r))) e1
  have k2 := congrArg (fderiv ℝ ((HfL ψ cv) r)) e2
  have k2' := congrArg (fderiv ℝ (fderiv ℝ ((HfL ψ cv) r))) e2
  exact ⟨k1.symm.trans (h.1.trans (congrArg (Real.exp (-a) • ·)
      (k2.symm.trans (h'.1.trans (one_smul ℝ _))))),
    k1'.symm.trans (h.2.trans (congrArg (Real.exp (-a) • ·)
      (k2'.symm.trans (h'.2.trans (one_smul ℝ _)))))⟩

theorem HfL_fderiv_eac (r : ℝ) (u : SDEState (d + d + 1)) :
    fderiv ℝ ((HfL ψ cv) r) u (eac (d := d)) = -(HfL ψ cv) r u := by
  refine fderiv_eq_of_line ((HfL_contDiff (ψ := ψ) (cv := cv) r).differentiable (by norm_num)) u _ ?_
  have e : (fun s : ℝ => (HfL ψ cv) r (u + s • (eac (d := d)))) = fun s => Real.exp (-s) * (HfL ψ cv) r u :=
    funext fun s => HfL_translate (ψ := ψ) (cv := cv) r s u
  rw [e]
  have := ((hasDerivAt_id (0 : ℝ)).neg.exp).mul_const ((HfL ψ cv) r u)
  simpa using this

/-- `D H0(u) v = e^{-a} (ψ'(ℓu) ℓv - v_a Φ)`. -/
theorem H0fL_fderiv (u v : SDEState (d + d + 1)) :
    fderiv ℝ (H0fL ψ cv) u v = Real.exp (-u iac) *
      (deriv ψ (∑ k, cv k * u (ixc k)) * (∑ k, cv k * v (ixc k)) - v iac * (PhifL ψ cv) u) := by
  refine fderiv_eq_of_line ((H0fL_contDiff (ψ := ψ) (cv := cv)).differentiable (by norm_num)) u v ?_
  have he := (((hasDerivAt_mul_const (v iac)).const_add (u iac)).neg (x := (0 : ℝ))).exp
  have hs : HasDerivAt (fun s : ℝ => ψ ((∑ k, cv k * u (ixc k)) + s * ∑ k, cv k * v (ixc k)))
      (deriv ψ (∑ k, cv k * u (ixc k)) * (∑ k, cv k * v (ixc k))) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (∑ k, cv k * v (ixc k))).const_add
      (∑ k, cv k * u (ixc k))
    have h2 := (psiL_hasDeriv (ψ := ψ) ((∑ k, cv k * u (ixc k)) + id 0 * ∑ k, cv k * v (ixc k))).comp
      (0 : ℝ) h1
    refine h2.congr_deriv ?_
    simp only [id, zero_mul, add_zero, one_mul]
  have e : (fun s : ℝ => (H0fL ψ cv) (u + s • v)) =
      fun s => Real.exp (-(u iac + s * v iac)) *
        ψ ((∑ k, cv k * u (ixc k)) + s * ∑ k, cv k * v (ixc k)) := by
    funext s
    simp only [H0fL, PhifL, ellL_line]
    simp
  rw [e]
  refine (he.mul hs).congr_deriv ?_
  simp only [PhifL, Pi.neg_apply, zero_mul, add_zero, mul_zero]
  ring

/-- `D² H0(u)(v,v) = e^{-a} ψ''(ℓu) (ℓv)²` when `v_a = 0`. -/
theorem H0fL_fderiv2 (u v : SDEState (d + d + 1)) (hv : v iac = 0) :
    fderiv ℝ (fderiv ℝ (H0fL ψ cv)) u v v = Real.exp (-u iac) *
      (deriv (deriv ψ) (∑ k, cv k * u (ixc k)) * (∑ k, cv k * v (ixc k)) ^ 2) := by
  refine fderiv2_eq_of_line (H0fL_contDiff (ψ := ψ) (cv := cv)) u v
    (φ' := fun s => Real.exp (-u iac) * (deriv ψ ((∑ k, cv k * u (ixc k)) + s * ∑ k, cv k * v (ixc k)) *
      ∑ k, cv k * v (ixc k))) (fun s => ?_) ?_
  · have e : (fun r : ℝ => (H0fL ψ cv) (u + r • v)) =
        fun r => Real.exp (-u iac) * ψ ((∑ k, cv k * u (ixc k)) + r * ∑ k, cv k * v (ixc k)) := by
      funext r
      simp only [H0fL, PhifL, ellL_line]
      simp [hv]
    rw [e]
    refine HasDerivAt.const_mul _ ?_
    have h1 := ((hasDerivAt_id s).mul_const (∑ k, cv k * v (ixc k))).const_add (∑ k, cv k * u (ixc k))
    have h2 := (psiL_hasDeriv (ψ := ψ) ((∑ k, cv k * u (ixc k)) + id s * ∑ k, cv k * v (ixc k))).comp s h1
    exact h2.congr_deriv (by simp only [id, one_mul])
  · refine HasDerivAt.const_mul _ ?_
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (∑ k, cv k * v (ixc k))).const_add
      (∑ k, cv k * u (ixc k))
    have h2 := ((psiL_hasDeriv2 (ψ := ψ) ((∑ k, cv k * u (ixc k)) + 0 * ∑ k, cv k * v (ixc k))).comp
      (0 : ℝ) h1).mul_const (∑ k, cv k * v (ixc k))
    refine h2.congr_deriv ?_
    simp only [id, zero_mul, add_zero, one_mul]
    ring

theorem PhifL_pack (x y : SDEState d) (a : ℝ) :
    (PhifL ψ cv) (pack x y a) = ψ (∑ k, cv k * x k) := by
  simp [PhifL]

/-- Generator of `Φ = ψ ∘ ℓ` at `x` with coefficients `σx, bx`. -/
noncomputable def genL (ψ : ℝ → ℝ) (cv : SDEState d) (σx : SDEDiffusion d) (bx x : SDEState d) : ℝ :=
  deriv ψ (∑ k, cv k * x k) * (∑ k, cv k * bx k) +
    (1 / 2) * ∑ j, deriv (deriv ψ) (∑ k, cv k * x k) * (∑ k, cv k * σx (k, j)) ^ 2

theorem HfL_drift_inside {r κ : ℝ} (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) (hx : ‖x‖ ^ 2 < r) :
    driftGen ((HfL ψ cv) r) κ σx bx σy by' x y a =
      Real.exp (-a) * (genL ψ cv σx bx x - κ * ψ (∑ k, cv k * x k)) := by
  have hN : Nxf (pack x y a) < r := by rw [Nxf_pack]; exact hx
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (HfL_eq_H0fL_nhds (ψ := ψ) (cv := cv) hN)
  unfold driftGen genL
  rw [h1, h2, H0fL_fderiv (ψ := ψ) (cv := cv),
    Finset.sum_congr rfl (fun j _ => H0fL_fderiv2 (ψ := ψ) (cv := cv) _ _ (by simp))]
  simp only [pack_ixc, pack_iac, PhifL_pack (ψ := ψ) (cv := cv), scol_apply']
  rw [← Finset.mul_sum]
  ring

theorem HfL_deriv_bound (r : ℝ) : ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧ ∀ x : SDEState d,
    ‖fderiv ℝ ((HfL ψ cv) r) (pack x 0 0)‖ ≤ B1 ∧ ∀ i i' : Fin (d + d + 1),
      |fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x 0 0) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1)| ≤ B2 := by
  set ρ : ℝ := |r| + 2 with hρ
  have hD1 : Continuous (fderiv ℝ (HfL ψ cv (d := d) r)) :=
    (HfL_contDiff (ψ := ψ) (cv := cv) r).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (HfL ψ cv (d := d) r))) :=
    ((HfL_contDiff (ψ := ψ) (cv := cv) r).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hp1 : Continuous fun x : SDEState d => pack x (0 : SDEState d) 0 :=
    pack_continuous continuous_id continuous_const continuous_const
  have K2 := isCompact_closedBall (0 : SDEState d) ρ
  obtain ⟨B1, hB1⟩ := K2.exists_bound_of_continuousOn (hD1.comp hp1).continuousOn
  have hB2e : ∀ i i' : Fin (d + d + 1), ∃ B, ∀ x ∈ Metric.closedBall (0 : SDEState d) ρ,
      ‖fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x 0 0) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1)‖ ≤ B := fun i i' =>
    K2.exists_bound_of_continuousOn
      (f := fun x : SDEState d => fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x 0 0)
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
  · obtain ⟨h1, h2⟩ := HfL_fderiv_zero (ψ := ψ) (cv := cv) (r := r) (u := pack x 0 0) (by rw [Nxf_pack]; exact hN)
    rw [h1, h2]
    exact ⟨by rw [norm_zero]; exact le_max_right _ _, fun i i' => by simpa using hB20⟩
  · have hxρ : ‖x‖ ≤ ρ := by
      by_contra hc
      replace hc := not_le.1 hc
      have hr0 := abs_nonneg r
      have hr1 := le_abs_self r
      have h1 : (|r| + 2) * (|r| + 2) < ‖x‖ * ‖x‖ := mul_self_lt_mul_self (add_nonneg hr0 zero_le_two) hc
      linarith only [h1, hr0, hr1, not_lt.1 hN, sq_nonneg |r|]
    have hmem : x ∈ Metric.closedBall (0 : SDEState d) ρ := mem_closedBall_zero_iff.2 hxρ
    refine ⟨(hB1 x hmem).trans (le_max_left _ _), fun i i' => ?_⟩
    have := hBc i i' x hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (hBc2 i i'))

/-- Global bound of the generator of `(HfL ψ cv) r` (the clock term only helps). -/
theorem HfL_drift_bound (r S : ℝ) (hS : 0 ≤ S) : ∃ B : ℝ, 0 ≤ B ∧ ∀ κ : ℝ, 0 ≤ κ →
    ∀ (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d) (by' : SDEState d)
      (x y : SDEState d) (a : ℝ),
      (‖x‖ ^ 2 ≤ r + 1 → ‖σx‖ ≤ S ∧ ‖bx‖ ≤ S ∧ ‖σy‖ ≤ S ∧ ‖by'‖ ≤ S) →
      driftGen ((HfL ψ cv) r) κ σx bx σy by' x y a ≤ Real.exp (-a) * B := by
  obtain ⟨B1, B2, hB1, hB2, hB⟩ := HfL_deriv_bound (ψ := ψ) (cv := cv) (d := d) r
  set D : ℝ := ((d : ℝ) + d + 1) * (S + S) with hD
  have hD0 : 0 ≤ D := by positivity
  have hd1 : (0 : ℝ) ≤ (d : ℝ) + d + 1 := by positivity
  have hBB : 0 ≤ B1 * D + (1 / 2) * (d * (B2 * D ^ 2)) :=
    add_nonneg (mul_nonneg hB1 hD0) (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg d)
      (mul_nonneg hB2 (sq_nonneg D))))
  refine ⟨B1 * D + (1 / 2) * (d * (B2 * D ^ 2)), hBB, fun κ hκ σx bx σy by' x y a hS' => ?_⟩
  have hea := Real.exp_pos (-a)
  by_cases hN : r + 1 < ‖x‖ ^ 2
  · obtain ⟨h1, h2⟩ := HfL_fderiv_zero (ψ := ψ) (cv := cv) (r := r) (u := pack x y a) (by rw [Nxf_pack]; exact hN)
    unfold driftGen
    rw [h1, h2]
    simp only [ContinuousLinearMap.zero_apply, Finset.sum_const_zero, mul_zero, add_zero]
    exact mul_nonneg hea.le hBB
  · obtain ⟨hσx, hbx, hσy, hby⟩ := hS' (not_lt.1 hN)
    obtain ⟨hL1, hL2⟩ := hB x
    obtain ⟨e1, e2⟩ := HfL_fderiv_pack (ψ := ψ) (cv := cv) r x y a
    unfold driftGen
    have hsplit : pack bx by' κ = pack bx by' 0 + κ • (eac (d := d)) := by
      rw [pack_add_eac, zero_add]
    have hk : fderiv ℝ ((HfL ψ cv) r) (pack x y a) (κ • (eac (d := d))) ≤ 0 := by
      rw [map_smul, HfL_fderiv_eac (ψ := ψ) (cv := cv), smul_eq_mul]
      have := HfL_nonneg (ψ := ψ) (cv := cv) r (pack x y a)
      exact mul_nonpos_of_nonneg_of_nonpos hκ (neg_nonpos.2 this)
    rw [hsplit, map_add]
    have t1 : fderiv ℝ ((HfL ψ cv) r) (pack x y a) (pack bx by' 0) ≤ Real.exp (-a) * (B1 * D) := by
      rw [e1, ContinuousLinearMap.smul_apply, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ hea.le
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      refine mul_le_mul hL1 ((norm_pack0_le _ _).trans ?_) (norm_nonneg _) hB1
      exact mul_le_mul_of_nonneg_left (add_le_add hbx hby) hd1
    have t2 : ∀ j, fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x y a) (pack (scol σx j) (scol σy j) 0)
        (pack (scol σx j) (scol σy j) 0) ≤ Real.exp (-a) * (B2 * D ^ 2) := by
      intro j
      rw [e2, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ hea.le
      have hc : ‖pack (scol σx j) (scol σy j) 0‖ ≤ D :=
        (norm_packcol_le _ _ _).trans (mul_le_mul_of_nonneg_left (add_le_add hσx hσy) hd1)
      set c := pack (scol σx j) (scol σy j) 0 with hcdef
      have hcs : ∑ i, |c i| ≤ D := by
        calc ∑ i, |c i| ≤ ∑ _i : Fin (d + d + 1), (‖σx‖ + ‖σy‖) :=
              Finset.sum_le_sum fun i _ => abs_packcol_le σx σy j i
          _ = ((d : ℝ) + d + 1) * (‖σx‖ + ‖σy‖) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                Nat.cast_add, Nat.cast_one]
          _ ≤ D := mul_le_mul_of_nonneg_left (add_le_add hσx hσy) hd1
      have hcs0 : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      rw [clm2_coord]
      calc ∑ i, ∑ i', c i * c i' * fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x 0 0)
            (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1)
          ≤ ∑ i, ∑ i', |c i| * |c i'| * B2 := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun i' _ => ?_
            refine (le_abs_self _).trans ?_
            rw [abs_mul, abs_mul]
            exact mul_le_mul_of_nonneg_left (hL2 i i') (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = B2 * (∑ i, |c i|) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i' _ => by ring
        _ ≤ B2 * D ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcs0 hcs 2) hB2
    have t3 : ∑ j, fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x y a) (pack (scol σx j) (scol σy j) 0)
        (pack (scol σx j) (scol σy j) 0) ≤ d * (Real.exp (-a) * (B2 * D ^ 2)) := by
      calc _ ≤ ∑ _j : Fin d, Real.exp (-a) * (B2 * D ^ 2) := Finset.sum_le_sum fun j _ => t2 j
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith only [t1, hk, t3]

theorem HfL_integrand_ok (r : ℝ) {X Y : ℝ≥0 → Ω → SDEState d} {HX HY : ℝ≥0 → Ω → SDEDiffusion d}
    (hHb : ∃ C, ∀ s ω, ‖X s ω‖ ^ 2 ≤ r + 1 → ‖HX s ω‖ ≤ C ∧ ‖HY s ω‖ ≤ C) :
    ∀ (i : Fin (d + d + 1)) (j : Fin d), ∃ C, ∀ s ω (a : ℝ), 0 ≤ a →
      |fderiv ℝ ((HfL ψ cv) r) (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1) *
        pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i| ≤ C := by
  intro i j
  obtain ⟨B, B2', hB0, -, hB⟩ := HfL_deriv_bound (ψ := ψ) (cv := cv) (d := d) r
  obtain ⟨C₀, hC₀⟩ := hHb
  refine ⟨B * (2 * |C₀|), fun s ω a ha => ?_⟩
  by_cases hN : r + 1 < ‖X s ω‖ ^ 2
  · have h0 := (HfL_fderiv_zero (ψ := ψ) (cv := cv) (r := r) (u := pack (X s ω) (Y s ω) a)
      (by rw [Nxf_pack]; exact hN)).1
    rw [h0]
    simp only [ContinuousLinearMap.zero_apply, zero_mul, abs_zero]
    exact mul_nonneg hB0 (by positivity)
  · obtain ⟨h1, h2⟩ := hC₀ s ω (not_lt.1 hN)
    have hea := Real.exp_pos (-a)
    have he := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
    have hd' : |fderiv ℝ ((HfL ψ cv) r) (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1)| ≤ B := by
      rw [(HfL_fderiv_pack (ψ := ψ) (cv := cv) r (X s ω) (Y s ω) a).1]
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

theorem HfL_drift_continuous (r : ℝ) {α : Type*} [TopologicalSpace α] {κ a : α → ℝ}
    {σx σy : α → SDEDiffusion d} {bx by' x y : α → SDEState d}
    (hκ : Continuous κ) (hσx : Continuous σx) (hbx : Continuous bx) (hσy : Continuous σy)
    (hby : Continuous by') (hx : Continuous x) (hy : Continuous y) (ha : Continuous a) :
    Continuous fun p => driftGen ((HfL ψ cv) r) (κ p) (σx p) (bx p) (σy p) (by' p) (x p) (y p) (a p) := by
  have hD1 : Continuous (fderiv ℝ (HfL ψ cv (d := d) r)) :=
    (HfL_contDiff (ψ := ψ) (cv := cv) r).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (HfL ψ cv (d := d) r))) :=
    ((HfL_contDiff (ψ := ψ) (cv := cv) r).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hpk := pack_continuous hx hy ha
  unfold driftGen
  refine ((hD1.comp hpk).clm_apply (pack_continuous hbx hby hκ)).add
    (continuous_const.mul (continuous_finsetSum _ fun j _ => ?_))
  have hv := pack_continuous (scol_continuous hσx j) (scol_continuous hσy j)
    (continuous_const (y := (0 : ℝ)))
  exact ((hD2.comp hpk).clm_apply hv).clm_apply hv

/-- Continuous weight `= 1` on the ball `R`, `= 0` outside the ball `R + 1`. -/
noncomputable def cutR (R : ℝ) (x : SDEState d) : ℝ := max 0 (1 - distB R x)

theorem cutR_nonneg (R : ℝ) (x : SDEState d) : 0 ≤ cutR R x := le_max_left _ _

theorem cutR_le_one (R : ℝ) (x : SDEState d) : cutR R x ≤ 1 :=
  max_le zero_le_one (by have := distB_nonneg R x; linarith)

theorem cutR_eq_one {R : ℝ} {x : SDEState d} (h : ‖x‖ ≤ R) : cutR R x = 1 := by
  simp [cutR, distB_eq_zero h]

theorem cutR_continuous (R : ℝ) : Continuous (cutR (d := d) R) :=
  continuous_const.max (continuous_const.sub (distB_continuous R))

/-- Pointwise: inside, the generator is `≤ K - w`; in the annulus the clock pays for `B`. -/
theorem HfL_drift_le_w {r R B M K wv : ℝ} {σx : SDEDiffusion d} {bx : SDEState d}
    {σy : SDEDiffusion d} {by' : SDEState d} {x y : SDEState d} (a : ℝ)
    (hR : 0 ≤ R) (hM : 0 < M) (hB : 0 ≤ B) (hK : 0 ≤ K) (hr : r = (R + 1) ^ 2 + 1) (hw : 0 ≤ wv)
    (hin : ‖x‖ ^ 2 < r → genL ψ cv σx bx x ≤ K - wv)
    (hBd : ∀ κ, 0 ≤ κ → driftGen ((HfL ψ cv) r) κ σx bx σy by' x y a ≤ Real.exp (-a) * B) :
    driftGen ((HfL ψ cv) r) (kapX 0 M R x) σx bx σy by' x y a ≤
      Real.exp (-a) * (K + B * (1 / M) * kapX 0 M R x) - Real.exp (-a) * (wv * cutR R x) := by
  have hk0 : 0 ≤ kapX 0 M R x := kapX_nonneg le_rfl hM.le x
  have hea := Real.exp_pos (-a)
  have hc0 := cutR_nonneg R x
  have hc1 := cutR_le_one R x
  have hBk : 0 ≤ B * (1 / M) * kapX 0 M R x :=
    mul_nonneg (mul_nonneg hB (one_div_nonneg.2 hM.le)) hk0
  by_cases hin' : ‖x‖ ^ 2 < r
  · rw [HfL_drift_inside (ψ := ψ) (cv := cv) σx bx σy by' x y a hin', ← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ hea.le
    have h1 := hin hin'
    have hψx := hψ0.out (∑ k, cv k * x k)
    have h2 : 0 ≤ kapX 0 M R x * ψ (∑ k, cv k * x k) := mul_nonneg hk0 hψx
    have h3 : wv * cutR R x ≤ wv := mul_le_of_le_one_right hw hc1
    linarith only [h1, h2, h3, hBk]
  · have hx1 : R + 1 < ‖x‖ := by
      have h1 : (R + 1) ^ 2 < ‖x‖ ^ 2 := by rw [hr] at hin'; linarith only [not_lt.1 hin']
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg x) h1
    have hdist : 1 ≤ distB R x := by unfold distB; exact le_max_of_le_right (by linarith only [hx1])
    have hcut : cutR R x = 0 := by unfold cutR; exact max_eq_left (by linarith only [hdist])
    have hkM : M ≤ kapX 0 M R x := by
      unfold kapX; have := mul_le_mul_of_nonneg_left hdist hM.le; linarith only [this]
    refine (hBd _ hk0).trans ?_
    have : B ≤ B * (1 / M) * kapX 0 M R x := by
      have h1 : 1 ≤ kapX 0 M R x / M := (one_le_div hM).2 hkM
      rw [show B * (1 / M) * kapX 0 M R x = B * (kapX 0 M R x / M) by ring]
      exact (mul_one B).symm.le.trans (mul_le_mul_of_nonneg_left h1 hB)
    rw [hcut, mul_zero, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left (by linarith only [this, hK]) hea.le

/-- Pathwise: the generator integral is at most `K t + B / M - ∫ e^{-A} w cutR`. -/
theorem HfL_drift_integral_le_w {r R B M K : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} {w : SDEState d → ℝ} (hσ : Continuous σ₀) (hb : Continuous b₀)
    (hwc : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    (hR : 0 ≤ R) (hM : 0 < M) (hB : 0 ≤ B) (hK : 0 ≤ K) (hr : r = (R + 1) ^ 2 + 1)
    {x : ℝ → SDEState d} (hx : Continuous x)
    (hin : ∀ u, ‖x u‖ ^ 2 < r → genL ψ cv (σ₀ (x u)) (b₀ (x u)) (x u) ≤ K - w (x u))
    (hBd : ∀ u κ, 0 ≤ κ → ∀ a, driftGen ((HfL ψ cv) r) κ (σ₀ (x u)) (b₀ (x u)) (σ₀ (x u)) (b₀ (x u))
      (x u) (x u) a ≤ Real.exp (-a) * B)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, driftGen ((HfL ψ cv) r) (kapX 0 M R (x u)) (σ₀ (x u)) (b₀ (x u)) (σ₀ (x u))
        (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kapX 0 M R (x v)) ≤
      K * t + B * (1 / M) - ∫ u in (0 : ℝ)..t,
        Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * (w (x u) * cutR R (x u)) := by
  have hgc : Continuous fun v => kapX 0 M R (x v) := kapX_comp_continuous 0 M R hx
  have hpc : Continuous fun u => ∫ v in (0 : ℝ)..u, kapX 0 M R (x v) :=
    continuous_iff_continuousAt.2 fun u => (hgc.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hcongr : ∫ u in (0 : ℝ)..t, driftGen ((HfL ψ cv) r) (kapX 0 M R (x u)) (σ₀ (x u)) (b₀ (x u))
        (σ₀ (x u)) (b₀ (x u)) (x u) (x u)
        (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kapX 0 M R (x v)) =
      ∫ u in (0 : ℝ)..t, driftGen ((HfL ψ cv) r) (kapX 0 M R (x u)) (σ₀ (x u)) (b₀ (x u))
        (σ₀ (x u)) (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..u, kapX 0 M R (x v)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by rw [Set.uIcc_of_le ht] at hu; exact hu.1
    simp only [Real.coe_toNNReal _ hu0]
  rw [hcongr]
  have hLc : Continuous fun u => driftGen ((HfL ψ cv) r) (kapX 0 M R (x u)) (σ₀ (x u)) (b₀ (x u))
      (σ₀ (x u)) (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..u, kapX 0 M R (x v)) :=
    HfL_drift_continuous (ψ := ψ) (cv := cv) r hgc (hσ.comp hx) (hb.comp hx) (hσ.comp hx)
      (hb.comp hx) hx hx hpc
  have hE : Continuous fun u => Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) :=
    Real.continuous_exp.comp hpc.neg
  have hWc : Continuous fun u => w (x u) * cutR R (x u) :=
    (hwc.comp hx).mul ((cutR_continuous R).comp hx)
  have h1c : Continuous fun u => Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * K := hE.mul continuous_const
  have h2c : Continuous fun u => Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * kapX 0 M R (x u) :=
    hE.mul hgc
  have h3c : Continuous fun u => Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) *
      (w (x u) * cutR R (x u)) := hE.mul hWc
  have hA0 : ∀ u ∈ Set.Icc (0 : ℝ) t, 0 ≤ ∫ v in (0 : ℝ)..u, kapX 0 M R (x v) := fun u hu =>
    intervalIntegral.integral_nonneg hu.1 fun v _ => kapX_nonneg le_rfl hM.le _
  calc _ ≤ ∫ u in (0 : ℝ)..t, (Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * K +
        B * (1 / M) * (Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * kapX 0 M R (x u)) -
        Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * (w (x u) * cutR R (x u))) :=
        intervalIntegral.integral_mono_on ht (hLc.intervalIntegrable _ _)
          (((h1c.add (continuous_const.mul h2c)).sub h3c).intervalIntegrable _ _) fun u _ => by
            have := HfL_drift_le_w (ψ := ψ) (cv := cv) (σx := σ₀ (x u)) (bx := b₀ (x u))
              (σy := σ₀ (x u)) (by' := b₀ (x u)) (x := x u) (y := x u)
              (∫ v in (0 : ℝ)..u, kapX 0 M R (x v)) hR hM hB hK hr (hw0 (x u)) (hin u)
              (fun κ hκ => hBd u κ hκ _)
            linarith only [this]
    _ = (∫ u in (0 : ℝ)..t, Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * K) +
        B * (1 / M) * (∫ u in (0 : ℝ)..t,
          Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * kapX 0 M R (x u)) -
        ∫ u in (0 : ℝ)..t, Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) *
          (w (x u) * cutR R (x u)) := by
        have i1 : IntervalIntegrable (fun u => Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * K)
            MeasureTheory.volume 0 t := h1c.intervalIntegrable _ _
        have i2 : IntervalIntegrable (fun u => B * (1 / M) *
            (Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * kapX 0 M R (x u)))
            MeasureTheory.volume 0 t := (continuous_const.mul h2c).intervalIntegrable _ _
        have i3 : IntervalIntegrable (fun u => Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) *
            (w (x u) * cutR R (x u))) MeasureTheory.volume 0 t := h3c.intervalIntegrable _ _
        rw [intervalIntegral.integral_sub (i1.add i2) i3, intervalIntegral.integral_add i1 i2,
          intervalIntegral.integral_const_mul]
    _ ≤ K * t + B * (1 / M) - ∫ u in (0 : ℝ)..t,
        Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * (w (x u) * cutR R (x u)) := by
        have e1 : ∫ u in (0 : ℝ)..t, Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (x v))) * K ≤ K * t := by
          calc _ ≤ ∫ _u in (0 : ℝ)..t, K :=
                intervalIntegral.integral_mono_on ht (h1c.intervalIntegrable _ _)
                  (continuous_const.intervalIntegrable _ _) fun u hu => by
                    have := Real.exp_le_one_iff.2 (neg_nonpos.2 (hA0 u hu))
                    exact (mul_le_mul_of_nonneg_right this hK).trans_eq (one_mul K)
            _ = K * t := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
        have e2 := integral_exp_neg_primitive hgc t
        have e3 := Real.exp_pos (-(∫ v in (0 : ℝ)..t, kapX 0 M R (x v)))
        have e4 : 0 ≤ B * (1 / M) := mul_nonneg hB (one_div_nonneg.2 hM.le)
        rw [e2]
        linarith only [e1, mul_nonneg e4 e3.le]

set_option maxHeartbeats 1000000 in
/-- Expectation: `E ∫₀ᵗ e^{-A} w cutR ≤ Φ(x₀) + K t + B / M`. -/
theorem lintegral_HfL_w [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {w : SDEState d → ℝ} (hwc : Continuous w) (hw0 : ∀ x, 0 ≤ w x)
    {r R B M K S : ℝ} (hR : 0 ≤ R) (hM : 0 < M) (hK : 0 ≤ K) (hr : r = (R + 1) ^ 2 + 1)
    (hin : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, ‖X u ω‖ ^ 2 < r →
      genL ψ cv (σ₀ (X u ω)) (b₀ (X u ω)) (X u ω) ≤ K - w (X u ω))
    (hS0 : ∀ x : SDEState d, ‖x‖ ^ 2 ≤ r + 1 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (hB : 0 ≤ B) (hBd : ∀ κ, 0 ≤ κ → ∀ (σx : SDEDiffusion d) (bx : SDEState d)
      (σy : SDEDiffusion d) (by' : SDEState d) (x y : SDEState d) (a : ℝ),
      (‖x‖ ^ 2 ≤ r + 1 → ‖σx‖ ≤ S ∧ ‖bx‖ ≤ S ∧ ‖σy‖ ≤ S ∧ ‖by'‖ ≤ S) →
      driftGen ((HfL ψ cv) r) κ σx bx σy by' x y a ≤ Real.exp (-a) * B)
    (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val,
        Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (X v.toNNReal ω))) *
          (w (X u.toNNReal ω) * cutR R (X u.toNNReal ω))) ∂P ≤
      ENNReal.ofReal ((HfL ψ cv) r (pack x₀ x₀ 0) + (K * t.val + B * (1 / M))) := by
  obtain ⟨hXm, hXc, hXa, hX0, JX, -, -, hJX, -, hXeq⟩ := hX
  have hFb := HfL_integrand_ok (ψ := ψ) (cv := cv) (Ω := Ω) r (X := X) (Y := X)
    (HX := fun s ω => σ₀ (X s ω)) (HY := fun s ω => σ₀ (X s ω))
    ⟨S, fun s ω h => ⟨(hS0 _ h).1, (hS0 _ h).1⟩⟩
  have hX0' : ∀ᵐ ω ∂P, X 0 ω = x₀ := by filter_upwards [hX0] with ω h using h
  obtain ⟨Z, hZi, hZ0, hZeq⟩ := ito_coupled_F hW x₀ (X := X) (Y := X)
    (HX := fun s ω => σ₀ (X s ω)) (HY := fun s ω => σ₀ (X s ω)) (JX := JX) (JY := JX)
    (bX := fun s ω => b₀ (X s ω)) (bY := fun s ω => b₀ (X s ω)) hXm hXm hXc hXc hXa hXa
    (fun s => hσ.measurable.comp (hXa s)) (fun s => hσ.measurable.comp (hXa s))
    (fun ω => hσ.comp (hXc ω)) (fun ω => hσ.comp (hXc ω))
    (fun s => hb.measurable.comp (hXa s)) (fun s => hb.measurable.comp (hXa s))
    (fun ω => hb.comp (hXc ω)) (fun ω => hb.comp (hXc ω)) hJX hJX hXeq hXeq
    hX0' hX0' (κ := fun x _ => kapX 0 M R x) (kapX_comp_continuous 0 M R continuous_fst)
    (fun x _ => kapX_nonneg le_rfl hM.le x) (HfL_contDiff (ψ := ψ) (cv := cv) r) hFb t
  set F0 := (HfL ψ cv) r (pack x₀ x₀ 0) with hF0
  set Wi : Ω → ℝ := fun ω => ∫ u in (0 : ℝ)..t.val,
        Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (X v.toNNReal ω))) *
          (w (X u.toNNReal ω) * cutR R (X u.toNNReal ω)) with hWi
  have hW0 : ∀ ω, 0 ≤ Wi ω := fun ω => intervalIntegral.integral_nonneg t.2 fun u _ =>
    mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw0 _) (cutR_nonneg _ _))
  have h := lintegral_le_of_ito (F := Wi) (Z := Z) (D := fun ω => Wi ω - F0 - Z ω)
    (E := fun _ => (0 : ℝ)) (c := F0) (β := K * t.val + B * (1 / M))
    (ae_of_all _ hW0) hZi hZ0 (ae_of_all _ fun ω => by ring) ?_ (integrable_const _)
  · exact h.trans (le_of_eq (by simp))
  · filter_upwards [hZeq, hin] with ω hω hinω
    have hpath := HfL_drift_integral_le_w (ψ := ψ) (cv := cv) hσ hb hwc hw0 hR hM hB hK hr
      (x := fun u => X u.toNNReal ω) ((hXc ω).comp continuous_real_toNNReal)
      (fun u h => hinω u.toNNReal h)
      (fun u κ hκ a => hBd κ hκ _ _ _ _ _ _ a
        (fun h => ⟨(hS0 _ h).1, (hS0 _ h).2, (hS0 _ h).1, (hS0 _ h).2⟩)) t.val t.2
    have hFn := HfL_nonneg (ψ := ψ) (cv := cv) r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX 0 M R (X u.toNNReal ω)))
    simp only [] at hω
    rw [hω] at hFn
    show Wi ω - F0 - Z ω ≤ K * t.val + B * (1 / M) + 0
    simp only [hWi]
    linarith

theorem HfL_pack0_le (r : ℝ) (x y : SDEState d) :
    (HfL ψ cv) r (pack x y 0) ≤ ψ (∑ k, cv k * x k) := by
  simp only [HfL, pack_iac, neg_zero, Real.exp_zero, one_mul, PhifL_pack (ψ := ψ) (cv := cv)]
  exact mul_le_of_le_one_left (hψ0.out _) (cutoff_le_one _ _)

theorem exists_coef_bound {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) (r : ℝ) (hr : 0 ≤ r) :
    ∃ S, 0 ≤ S ∧ ∀ x : SDEState d, ‖x‖ ^ 2 ≤ r + 1 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S := by
  have K := isCompact_closedBall (0 : SDEState d) (r + 1)
  obtain ⟨S1, hS1⟩ := K.exists_bound_of_continuousOn hσ.continuousOn
  obtain ⟨S2, hS2⟩ := K.exists_bound_of_continuousOn hb.continuousOn
  refine ⟨max (max S1 S2) 0, le_max_right _ _, fun x hx => ?_⟩
  have hxr : ‖x‖ ≤ r + 1 := by
    by_contra hc
    have h1 : r + 1 < ‖x‖ := not_le.1 hc
    nlinarith [norm_nonneg x]
  have hm : x ∈ Metric.closedBall (0 : SDEState d) (r + 1) := mem_closedBall_zero_iff.2 hxr
  exact ⟨(hS1 x hm).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hS2 x hm).trans ((le_max_right _ _).trans (le_max_left _ _))⟩

theorem measurable_Wi [MeasurableSpace Ω] {X : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hXc : ∀ ω, Continuous fun s => X s ω)
    {w : SDEState d → ℝ} (hwc : Continuous w) (M R : ℝ) (t : ℝ≥0) :
    Measurable fun ω => ∫ u in (0 : ℝ)..t.val,
      Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (X v.toNNReal ω))) *
        (w (X u.toNNReal ω) * cutR R (X u.toNNReal ω)) := by
  have hA : ∀ s : ℝ≥0, Measurable fun ω => ∫ v in (0 : ℝ)..s.val, kapX 0 M R (X v.toNNReal ω) :=
    fun s => measurable_intervalIntegral_of_continuous _ s
      (fun s' _ => (kapX_comp_continuous 0 M R continuous_id).measurable.comp (hXm s'))
      (fun ω => kapX_comp_continuous 0 M R (hXc ω))
  have hAc : ∀ ω, Continuous fun s : ℝ≥0 => ∫ v in (0 : ℝ)..s.val, kapX 0 M R (X v.toNNReal ω) := by
    intro ω
    have hg : Continuous fun v : ℝ => kapX 0 M R (X v.toNNReal ω) :=
      kapX_comp_continuous 0 M R ((hXc ω).comp continuous_real_toNNReal)
    have hp : Continuous fun u : ℝ => ∫ v in (0 : ℝ)..u, kapX 0 M R (X v.toNNReal ω) :=
      continuous_iff_continuousAt.2 fun u => (hg.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
    exact hp.comp NNReal.continuous_coe
  have e : (fun ω => ∫ u in (0 : ℝ)..t.val,
      Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 M R (X v.toNNReal ω))) *
        (w (X u.toNNReal ω) * cutR R (X u.toNNReal ω))) =
      fun ω => ∫ u in (0 : ℝ)..t.val, (fun (s : ℝ≥0) (ω : Ω) =>
        Real.exp (-(∫ v in (0 : ℝ)..s.val, kapX 0 M R (X v.toNNReal ω))) *
          (w (X s ω) * cutR R (X s ω))) u.toNNReal ω := by
    funext ω
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by rw [Set.uIcc_of_le t.2] at hu; exact hu.1
    simp only [Real.toNNReal_coe, NNReal.val_eq_coe, Real.coe_toNNReal _ hu0]
  rw [e]
  exact measurable_intervalIntegral_of_continuous _ t
    (fun s _ => (Real.continuous_exp.measurable.comp (hA s).neg).mul
      ((hwc.measurable.comp (hXm s)).mul ((cutR_continuous R).measurable.comp (hXm s))))
    (fun ω => (Real.continuous_exp.comp (hAc ω).neg).mul
      ((hwc.comp (hXc ω)).mul ((cutR_continuous R).comp (hXc ω))))

theorem Wi_eventually_eq {X : ℝ≥0 → Ω → SDEState d} (hXc : ∀ ω, Continuous fun s => X s ω)
    {w : SDEState d → ℝ} (Mf : ℕ → ℝ) (t : ℝ≥0) (ω : Ω) :
    ∀ᶠ n : ℕ in atTop, ∫ u in (0 : ℝ)..t.val,
      Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 (Mf n) n (X v.toNNReal ω))) *
        (w (X u.toNNReal ω) * cutR n (X u.toNNReal ω)) =
      ∫ u in (0 : ℝ)..t.val, w (X u.toNNReal ω) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hXc ω).continuousOn
  filter_upwards [eventually_ge_atTop (Nat.ceil C)] with n hn
  have hCn : C ≤ (n : ℝ) := (Nat.le_ceil C).trans (by exact_mod_cast hn)
  have hball : ∀ u : ℝ, u ≤ t.val → ‖X u.toNNReal ω‖ ≤ n := fun u hu =>
    (hC _ ⟨bot_le, Real.toNNReal_le_iff_le_coe.2 hu⟩).trans hCn
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le t.2] at hu
  have hA : ∫ v in (0 : ℝ)..u, kapX 0 (Mf n) n (X v.toNNReal ω) = 0 := by
    have e0 : ∫ v in (0 : ℝ)..u, kapX 0 (Mf n) n (X v.toNNReal ω) = ∫ _v in (0 : ℝ)..u, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le hu.1] at hv
      simp only [kapX, distB_eq_zero (hball v (hv.2.trans hu.2)), mul_zero, add_zero]
    rw [e0, intervalIntegral.integral_zero]
  simp only [hA, neg_zero, Real.exp_zero, one_mul, cutR_eq_one (hball u hu.2), mul_one]

/-- `E ∫₀ᵗ w(X_u) du ≤ ψ(ℓ x₀) + K t` when `genL ≤ K - w` along a.e. path. -/
theorem lintegral_w_le [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {w : SDEState d → ℝ} (hwc : Continuous w) (hw0 : ∀ x, 0 ≤ w x) {K : ℝ} (hK : 0 ≤ K)
    (hin : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, genL ψ cv (σ₀ (X u ω)) (b₀ (X u ω)) (X u ω) ≤ K - w (X u ω))
    (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val, w (X u.toNNReal ω)) ∂P ≤
      ENNReal.ofReal (ψ (∑ k, cv k * x₀ k) + K * t.val) := by
  have hXm : ∀ s, Measurable (X s) := hX.1
  have hXc : ∀ ω, Continuous fun s => X s ω := hX.2.1
  have hSn : ∀ n : ℕ, ∃ S, 0 ≤ S ∧ ∀ x : SDEState d, ‖x‖ ^ 2 ≤ (((n : ℝ) + 1) ^ 2 + 1) + 1 →
      ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S := fun n => exists_coef_bound hσ hb _ (by positivity)
  choose S hS0 hS using hSn
  have hBn := fun n : ℕ => HfL_drift_bound (ψ := ψ) (cv := cv) (d := d) (((n : ℝ) + 1) ^ 2 + 1) (S n) (hS0 n)
  choose B hB0 hBd using hBn
  set Mf : ℕ → ℝ := fun n => ((n : ℝ) + 1) * (B n + 1) with hMf
  have hMf0 : ∀ n, 0 < Mf n := fun n => by simp only [hMf]; have := hB0 n; positivity
  set g : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (∫ u in (0 : ℝ)..t.val,
      Real.exp (-(∫ v in (0 : ℝ)..u, kapX 0 (Mf n) n (X v.toNNReal ω))) *
        (w (X u.toNNReal ω) * cutR n (X u.toNNReal ω))) with hg
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ENNReal.measurable_ofReal.comp (measurable_Wi hXm hXc hwc (Mf n) n t)
  have hgn : ∀ n : ℕ, ∫⁻ ω, g n ω ∂P ≤
      ENNReal.ofReal (ψ (∑ k, cv k * x₀ k) + K * t.val + 1 / ((n : ℝ) + 1)) := by
    intro n
    refine (lintegral_HfL_w (ψ := ψ) (cv := cv) hW x₀ hσ hb hX hwc hw0 (R := n) (M := Mf n)
      (Nat.cast_nonneg n) (hMf0 n) hK rfl
      (by filter_upwards [hin] with ω h u _ using h u) (hS n) (hB0 n) (hBd n) t).trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := HfL_pack0_le (ψ := ψ) (cv := cv) (((n : ℝ) + 1) ^ 2 + 1) x₀ x₀
    have h2 : B n * (1 / Mf n) ≤ 1 / ((n : ℝ) + 1) := by
      have hb0 := hB0 n
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := Nat.cast_add_one_pos n
      simp only [hMf]
      rw [mul_one_div, div_le_div_iff₀ (mul_pos hn1 (by linarith only [hb0])) hn1]
      linarith only [hn1]
    linarith only [h1, h2]
  have hlim : ∀ ω, Filter.liminf (fun n => g n ω) atTop =
      ENNReal.ofReal (∫ u in (0 : ℝ)..t.val, w (X u.toNNReal ω)) := by
    intro ω
    refine Tendsto.liminf_eq ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Wi_eventually_eq (w := w) hXc Mf t ω] with n hn
    simp only [hg, hn]
  calc ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val, w (X u.toNNReal ω)) ∂P
      = ∫⁻ ω, Filter.liminf (fun n => g n ω) atTop ∂P := by simp only [hlim]
    _ ≤ Filter.liminf (fun n => ∫⁻ ω, g n ω ∂P) atTop := lintegral_liminf_le hgm
    _ ≤ Filter.liminf (fun n : ℕ => ENNReal.ofReal (ψ (∑ k, cv k * x₀ k) + K * t.val +
          1 / ((n : ℝ) + 1))) atTop := Filter.liminf_le_liminf (Eventually.of_forall hgn)
    _ = ENNReal.ofReal (ψ (∑ k, cv k * x₀ k) + K * t.val) := by
        refine Tendsto.liminf_eq ?_
        refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (ψ (∑ k, cv k * x₀ k) + K * t.val)
        simpa using this

end M12a

section M12b
/-! M12b: the Lyapunov function `log(1 + cᵀx)` for (1.1): `E ∫₀ᵗ w(X_u) du ≤ log(1 + cᵀx) + log 2 + K t`
with `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)` and `K = max H 0` (`H` of (3.5)). -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- A smooth positive function equal to `1 + s` for `s > -1/4`. -/
noncomputable def pL (s : ℝ) : ℝ := 1 + s * Real.smoothTransition (4 * s + 2)

noncomputable def psiK (s : ℝ) : ℝ := Real.log (pL s) + Real.log 2

theorem pL_ge (s : ℝ) : 1 / 2 ≤ pL s := by
  unfold pL
  have h0 := Real.smoothTransition.nonneg (4 * s + 2)
  have h1 := Real.smoothTransition.le_one (4 * s + 2)
  by_cases hs : 0 ≤ s
  · nlinarith
  · push Not at hs
    by_cases hs2 : s < -1 / 2
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; norm_num
    · push Not at hs2
      nlinarith

theorem pL_pos (s : ℝ) : 0 < pL s := lt_of_lt_of_le (by norm_num) (pL_ge s)

theorem pL_eq {s : ℝ} (hs : -1 / 4 < s) : pL s = 1 + s := by
  unfold pL; rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem pL_contDiff : ContDiff ℝ 2 pL :=
  contDiff_const.add (contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).add contDiff_const)))

theorem psiK_contDiff : ContDiff ℝ 2 psiK :=
  (pL_contDiff.log fun s => (pL_pos s).ne').add contDiff_const

theorem psiK_nonneg (s : ℝ) : 0 ≤ psiK s := by
  unfold psiK
  have h := Real.log_le_log (by norm_num) (pL_ge s)
  rw [one_div, Real.log_inv] at h
  linarith

theorem psiK_eq {s : ℝ} (hs : -1 / 4 < s) : psiK s = Real.log (1 + s) + Real.log 2 := by
  unfold psiK; rw [pL_eq hs]

theorem deriv_psiK {s : ℝ} (hs : -1 / 4 < s) : deriv psiK s = (1 + s)⁻¹ := by
  have hev : psiK =ᶠ[𝓝 s] fun s => Real.log (1 + s) + Real.log 2 := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs' using psiK_eq hs'
  rw [hev.deriv_eq]
  have h := (((hasDerivAt_id s).const_add 1).log (by simp; linarith)).add_const (Real.log 2)
  exact h.deriv.trans (by simp)

theorem deriv2_psiK {s : ℝ} (hs : -1 / 4 < s) : deriv (deriv psiK) s = -((1 + s) ^ 2)⁻¹ := by
  have hev : deriv psiK =ᶠ[𝓝 s] fun s => (1 + s)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs' using deriv_psiK hs'
  rw [hev.deriv_eq]
  have h := ((hasDerivAt_id s).const_add 1).inv (by simp; linarith)
  exact h.deriv.trans (by rw [neg_div, one_div]; rfl)

theorem posPart_of_mem {x : SDEState n} (hx : x ∈ orthant n) : posPart x = x := by
  ext i; rw [posPart_apply']; exact max_eq_left (hx i)

theorem sig_sum_sq (C : Coeffs n) (v : Fin n → ℝ) :
    ∑ j, (∑ k, v k * C.Γ j k) ^ 2 = ∑ i, ∑ l, C.sig i l * v i * v l := by
  calc ∑ j, (∑ k, v k * C.Γ j k) ^ 2 = ∑ j, ∑ i, ∑ l, (v i * C.Γ j i) * (v l * C.Γ j l) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ l, ∑ j, (v i * C.Γ j i) * (v l * C.Γ j l) := by
        rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ l, C.sig i l * v i * v l := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
        simp only [Coeffs.sig, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring

/-- On `ℝⁿ₊` the generator of `log(1 + cᵀx)` is the bracket of (1.2). -/
theorem genL_kolm (C : Coeffs n) {c x : SDEState n} (hc : c ∈ openOrthant n) (hx : x ∈ orthant n) :
    genL psiK c (diffusion C (0, x)) (drift C (0, x)) x = cBracket C c x := by
  have hℓ : 0 ≤ ∑ k, c k * x k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k)
  have hℓ' : -1 / 4 < ∑ k, c k * x k := by linarith
  have hp : 0 < 1 + ∑ k, c k * x k := by linarith
  unfold genL cBracket
  rw [deriv_psiK hℓ', deriv2_psiK hℓ']
  simp only [diffusion, drift, PiLp.toLp_apply, posPart_of_mem hx]
  have key := sig_sum_sq C (fun k => c k * x k * C.g k x)
  have e1 : ∑ j, (∑ k, c k * (x k * C.g k x * C.Γ j k)) ^ 2 =
      ∑ i, ∑ j, C.sig i j * c i * c j * x i * x j * C.g i x * C.g j x := by
    rw [show (∑ j, (∑ k, c k * (x k * C.g k x * C.Γ j k)) ^ 2) =
      ∑ j, (∑ k, (c k * x k * C.g k x) * C.Γ j k) ^ 2 from
        Finset.sum_congr rfl fun j _ => by congr 1; exact Finset.sum_congr rfl fun k _ => by ring, key]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have e2 : ∑ k, c k * (x k * C.f k x) = ∑ i, c i * x i * C.f i x :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [← Finset.mul_sum, e1, e2]
  field_simp
  ring

/-- A solution from `x₀ ∈ ℝⁿ₊` stays in `ℝⁿ₊` at all times, a.s. -/
theorem orthant_inv_all {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x₀) Y) :
    ∀ᵐ ω ∂P, ∀ u, Y u ω ∈ orthant n := by
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, Y ((q : ℝ).toNNReal) ω ∈ orthant n :=
    ae_all_iff.2 fun q => orthant_inv1 P C B hB hC hx₀ hY _
  filter_upwards [hq] with ω hω u
  have hcl : IsClosed {s : ℝ≥0 | Y s ω ∈ orthant n} := orthant_isClosed.preimage (hY.2.1 ω)
  have hsub : Set.range (fun q : ℚ => (q : ℝ).toNNReal) ⊆ {s : ℝ≥0 | Y s ω ∈ orthant n} := by
    rintro _ ⟨q, rfl⟩; exact hω q
  have := hcl.closure_subset_iff.2 hsub
  rw [denseRange_rat_toNNReal.closure_range] at this
  exact this (Set.mem_univ u)

end M12b

end ItoLib

-- ===== Z =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section M12c
/-! M12c: invariant measures integrate the weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`:
`∫ w dμ ≤ max H 0`, hence the Lyapunov integrands `fᵢ − σᵢᵢ gᵢ²/2` are `μ`-integrable. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- The transition kernel at time `t` (universe-polymorphic copy of `markov_stmt_of_inv`, part 1). -/
theorem kernel_of_family {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (t : ℝ≥0) :
    ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
      ∀ x ∈ orthant n, κ x = trans P X t x := by
  obtain ⟨hP, hB, hX⟩ := hfam
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := kolm_trunc C hC
  have hXm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t) := fun y hy t => (hX y hy).1 t
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hX y hy
  obtain ⟨κ, hκ, hκx, -⟩ := markov_of_core orthant_isClosed.measurableSet hXm t fun F _ m => by
    obtain ⟨hm, hb, hl⟩ := thick_props (Nat.one_div_pos_of_nat (n := m)) F
    obtain ⟨g, hg, -, hg1, hg2⟩ := markov_core hB hσc hbc s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX' t hm hb
      (inv_nonneg.2 (Nat.one_div_pos_of_nat (n := m)).le) hl
    exact ⟨g, hg, hg1, hg2⟩
  exact ⟨κ, hκ, hκx⟩

theorem inv_lintegral_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : SDEState n → ℝ≥0 → Ω → SDEState n} {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ)
    {t : ℝ≥0} {κ : Kernel (SDEState n) (SDEState n)} (hκx : ∀ x ∈ orthant n, κ x = trans P X t x)
    {g : SDEState n → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ∫⁻ y, g y ∂(κ x) ∂μ = ∫⁻ y, g y ∂μ := by
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  have hbind : μ.bind κ = μ := by
    ext A hA
    rw [Measure.bind_apply hA κ.measurable.aemeasurable, ← hμ.2.2 t A hA]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    rw [hκx x hx]
  rw [← Measure.lintegral_bind κ.measurable.aemeasurable hg.aemeasurable, hbind]

/-- Time-averaged invariance: `t ∫ h dμ = ∫ E ∫₀ᵗ h(X^x_u) du dμ(x)` for bounded continuous `h ≥ 0`. -/
theorem inv_avg_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : SDEState n → ℝ≥0 → Ω → SDEState n} {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ)
    (hXm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t))
    (hXc : ∀ x ∈ orthant n, ∀ ω, Continuous fun t => X x t ω)
    (κ : ℝ≥0 → Kernel (SDEState n) (SDEState n)) (hκx : ∀ t, ∀ x ∈ orthant n, κ t x = trans P X t x)
    {h : SDEState n → ℝ} (hc : Continuous h) (h0 : ∀ x, 0 ≤ h x) {N : ℝ} (hN : ∀ x, h x ≤ N)
    (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * ∫⁻ x, ENNReal.ofReal (h x) ∂μ =
      ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t, h (X x u.toNNReal ω)) ∂P ∂μ := by
  have hμP := hμ.1
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  have hhm : Measurable fun y => ENNReal.ofReal (h y) := ENNReal.measurable_ofReal.comp hc.measurable
  set G : ℝ → SDEState n → ℝ := fun u x => (orthant n).indicator
    (fun x => (∫⁻ y, ENNReal.ofReal (h y) ∂(κ u.toNNReal x)).toReal) x with hG
  have hGx : ∀ u, ∀ x ∈ orthant n, G u x = ∫ ω, h (X x u.toNNReal ω) ∂P := by
    intro u x hx
    simp only [hG, Set.indicator_of_mem hx, hκx _ x hx, StochKolmogorov.Persist.trans]
    rw [lintegral_map hhm (hXm x hx _), integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun ω => h0 _) (hc.measurable.comp (hXm x hx _)).aestronglyMeasurable]
  have hGc : ∀ x, Continuous fun u => G u x := by
    intro x
    by_cases hx : x ∈ orthant n
    · simp only [hGx _ x hx]
      refine continuous_of_dominated (bound := fun _ => N)
        (fun u => (hc.measurable.comp (hXm x hx _)).aestronglyMeasurable)
        (fun u => ae_of_all _ fun ω => ?_) (integrable_const N)
        (ae_of_all _ fun ω => hc.comp ((hXc x hx ω).comp continuous_real_toNNReal))
      rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hN _
    · simp only [hG, Set.indicator_of_notMem hx]; exact continuous_const
  have hGm : ∀ u, Measurable (G u) := fun u =>
    ((Measurable.lintegral_kernel hhm).ennreal_toReal).indicator orthant_isClosed.measurableSet
  have hGj : Measurable (Function.uncurry G) := measurable_uncurry_of_continuous_of_measurable hGc hGm
  -- inner integral in x for fixed u
  have hfin : ∀ u : ℝ, ∀ x ∈ orthant n, ∫⁻ y, ENNReal.ofReal (h y) ∂(κ u.toNNReal x) ≠ ⊤ := by
    intro u x hx
    rw [hκx _ x hx, StochKolmogorov.Persist.trans]
    have := Measure.isProbabilityMeasure_map (μ := P) (hXm x hx u.toNNReal).aemeasurable
    refine ne_top_of_le_ne_top (b := ∫⁻ _y, ENNReal.ofReal N ∂(P.map (X x u.toNNReal))) ?_
      (lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hN y))
    simp
  have hin : ∀ u, ∫⁻ x, ENNReal.ofReal (G u x) ∂μ = ∫⁻ x, ENNReal.ofReal (h x) ∂μ := by
    intro u
    rw [← inv_lintegral_eq hμ (hκx u.toNNReal) hhm]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with x hx
    simp only [hG, Set.indicator_of_mem hx]
    exact ENNReal.ofReal_toReal (hfin u x hx)
  -- swap u and x
  have hswap := lintegral_lintegral_swap (μ := volume.restrict (Set.Ioc (0 : ℝ) t)) (ν := μ)
    (f := fun (u : ℝ) (x : SDEState n) => ENNReal.ofReal (G u x)) (ENNReal.measurable_ofReal.comp hGj).aemeasurable
  simp only [hin, setLIntegral_const, Real.volume_Ioc, sub_zero] at hswap
  rw [mul_comm, hswap]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  -- for fixed x in the orthant: swap u and ω
  have hHj : Measurable (Function.uncurry fun (u : ℝ) (ω : Ω) => ENNReal.ofReal (h (X x u.toNNReal ω))) :=
    ENNReal.measurable_ofReal.comp (measurable_uncurry_of_continuous_of_measurable
      (fun ω => hc.comp ((hXc x hx ω).comp continuous_real_toNNReal))
      (fun u => hc.measurable.comp (hXm x hx _)))
  have hint : ∀ u : ℝ, Integrable (fun ω => h (X x u.toNNReal ω)) P := fun u =>
    Integrable.of_bound (hc.measurable.comp (hXm x hx _)).aestronglyMeasurable N
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]; exact hN _)
  calc ∫⁻ u in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (G u x)
      = ∫⁻ u in Set.Ioc (0 : ℝ) t, ∫⁻ ω, ENNReal.ofReal (h (X x u.toNNReal ω)) ∂P := by
        refine lintegral_congr fun u => ?_
        rw [hGx u x hx, ofReal_integral_eq_lintegral_ofReal (hint u) (ae_of_all _ fun ω => h0 _)]
    _ = ∫⁻ ω, (∫⁻ u in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (h (X x u.toNNReal ω))) ∂P :=
        lintegral_lintegral_swap hHj.aemeasurable
    _ = ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t, h (X x u.toNNReal ω)) ∂P := by
        refine lintegral_congr fun ω => ?_
        have hcu : Continuous fun u : ℝ => h (X x u.toNNReal ω) :=
          hc.comp ((hXc x hx ω).comp continuous_real_toNNReal)
        rw [intervalIntegral.integral_of_le ht.le, ofReal_integral_eq_lintegral_ofReal
          ((hcu.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self) (ae_of_all _ fun u => h0 _)]

end M12c

end ItoLib

-- ===== L33 =====
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

namespace ItoLib
open EthierKurtz

section L33
/-! L33 (lemma_3_2/3_3/3_4 work, s1 2026-10-30): generic Lyapunov bounds for the Kolmogorov family. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- Generic form of `lintegral_wK_le`: `E ∫₀ᵗ w(X^x₀) ≤ ψ(cᵀx₀) + K t` when `genL ψ + w ≤ K` on the orthant. -/
theorem lintegral_gen_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (c : SDEState n) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ∀ v, 0 ≤ ψ v)
    {w : SDEState n → ℝ} (hwc : Continuous w) (hw0 : ∀ x, 0 ≤ w x) {K : ℝ} (hK : 0 ≤ K)
    (hle : ∀ x ∈ orthant n, genL ψ c (diffusion C (0, x)) (drift C (0, x)) x ≤ K - w x)
    {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val, w (X x₀ u.toNNReal ω)) ∂P ≤
      ENNReal.ofReal (ψ (∑ k, c k * x₀ k) + K * t.val) := by
  obtain ⟨hP, hBm, hX⟩ := hfam
  have := hP
  have : Fact (ContDiff ℝ 2 ψ) := ⟨hψ⟩
  have : Fact (∀ v, 0 ≤ ψ v) := ⟨hψ0⟩
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  have hX' : SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => x₀) (X x₀) := hX x₀ hx₀
  have hall := orthant_inv_all P C B hBm hC hx₀ (hX x₀ hx₀)
  refine lintegral_w_le (ψ := ψ) (cv := c) hBm x₀ hσc hbc hX' hwc hw0 hK ?_ t
  filter_upwards [hall] with ω hω u
  exact hle _ (hω u)

/-- Generic: invariant measures integrate `w` when `genL ψ + w ≤ K` on the orthant. -/
theorem inv_w_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (c : SDEState n) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ∀ v, 0 ≤ ψ v)
    {w : SDEState n → ℝ} (hwc : Continuous w) (hw0 : ∀ x, 0 ≤ w x) {K' : ℝ} (hK0 : 0 ≤ K')
    (hle : ∀ x ∈ orthant n, genL ψ c (diffusion C (0, x)) (drift C (0, x)) x ≤ K' - w x)
    {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) :
    ∫⁻ x, ENNReal.ofReal (w x) ∂μ ≤ ENNReal.ofReal K' := by
  have hP := hfam.1
  have hμP := hμ.1
  choose κ hκ hκx using kernel_of_family P C B X hfam hC
  have hXm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t) := fun x hx t => (hfam.2.2 x hx).1 t
  have hXc : ∀ x ∈ orthant n, ∀ ω, Continuous fun t => X x t ω := fun x hx => (hfam.2.2 x hx).2.1
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  have hΨc : Continuous fun x : SDEState n => ψ (∑ k, c k * x k) :=
    hψ.continuous.comp (continuous_finset_sum _ fun k _ =>
      continuous_const.mul (PiLp.continuous_apply 2 _ k))
  have hNle : ∀ N : ℕ, ∫⁻ x, ENNReal.ofReal (min (w x) N) ∂μ ≤ ENNReal.ofReal K' := by
    intro N
    set F : ℕ → SDEState n → ℝ≥0∞ := fun m x =>
      ENNReal.ofReal (min (ψ (∑ k, c k * x k) / ((m : ℝ) + 1) + K') N) with hF
    have hstep : ∀ m : ℕ, ∫⁻ x, ENNReal.ofReal (min (w x) N) ∂μ ≤ ∫⁻ x, F m x ∂μ := by
      intro m
      have ht : (0 : ℝ) < (m : ℝ) + 1 := Nat.cast_add_one_pos m
      have e := inv_avg_eq hμ hXm hXc κ hκx (h := fun x => min (w x) N)
        (hwc.min continuous_const) (fun x => le_min (hw0 x) (Nat.cast_nonneg N))
        (fun x => min_le_right _ _) _ ht
      have hbd : ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..((m : ℝ) + 1),
          min (w (X x u.toNNReal ω)) N) ∂P ∂μ ≤
          ∫⁻ x, ENNReal.ofReal ((m : ℝ) + 1) * F m x ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with x hx
        have hle1 : ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..((m : ℝ) + 1),
            min (w (X x u.toNNReal ω)) N) ∂P ≤
            ENNReal.ofReal (ψ (∑ k, c k * x k) + K' * ((m : ℝ) + 1)) := by
          refine le_trans (lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_)
            (lintegral_gen_le P C B X hfam hC c hψ hψ0 hwc hw0 hK0 hle hx ((m : ℝ) + 1).toNNReal |>.trans_eq ?_)
          · rw [show (((m : ℝ) + 1).toNNReal).val = (m : ℝ) + 1 from Real.coe_toNNReal _ ht.le]
            refine intervalIntegral.integral_mono_on ht.le ?_ ?_ fun u _ => min_le_left _ _
            · exact ((hwc.comp ((hXc x hx ω).comp continuous_real_toNNReal)).min
                continuous_const).intervalIntegrable _ _
            · exact (hwc.comp ((hXc x hx ω).comp continuous_real_toNNReal)).intervalIntegrable _ _
          · rw [show (((m : ℝ) + 1).toNNReal).val = (m : ℝ) + 1 from Real.coe_toNNReal _ ht.le]
        have hle2 : ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..((m : ℝ) + 1),
            min (w (X x u.toNNReal ω)) N) ∂P ≤ ENNReal.ofReal (N * ((m : ℝ) + 1)) := by
          refine le_trans (lintegral_mono (g := fun _ => ENNReal.ofReal (N * ((m : ℝ) + 1)))
            fun ω => ENNReal.ofReal_le_ofReal ?_) (by simp)
          calc _ ≤ ∫ _u in (0 : ℝ)..((m : ℝ) + 1), (N : ℝ) :=
                intervalIntegral.integral_mono_on ht.le
                  (((hwc.comp ((hXc x hx ω).comp continuous_real_toNNReal)).min
                    continuous_const).intervalIntegrable _ _)
                  (continuous_const.intervalIntegrable _ _) fun u _ => min_le_right _ _
            _ = N * ((m : ℝ) + 1) := by simp [mul_comm]
        refine le_trans (le_min hle1 hle2) (le_of_eq ?_)
        simp only [hF]
        rw [← ENNReal.ofReal_min, ← ENNReal.ofReal_mul ht.le]
        congr 1
        rw [mul_min_of_nonneg _ _ ht.le]
        congr 1
        · rw [eq_comm, mul_add, mul_div_cancel₀ _ ht.ne']
          ring
        · ring
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hbd
      exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top).1
        (e.trans_le hbd)
    have hlim : Tendsto (fun m => ∫⁻ x, F m x ∂μ) atTop (𝓝 (∫⁻ _x, ENNReal.ofReal (min K' N) ∂μ)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal N)
        (fun m => ENNReal.measurable_ofReal.comp (((hΨc.div_const _).add continuous_const).min
          continuous_const).measurable)
        (fun m => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _)) (by simp)
        (ae_of_all _ fun x => ?_)
      have h1 : Tendsto (fun m : ℕ => ψ (∑ k, c k * x k) / ((m : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (ψ (∑ k, c k * x k))
        simpa [div_eq_mul_inv] using this
      have h2 := (h1.add_const K').min (tendsto_const_nhds (x := ((N : ℕ) : ℝ)))
      rw [zero_add] at h2
      exact (ENNReal.continuous_ofReal.tendsto _).comp h2
    refine (ge_of_tendsto' hlim fun m => hstep m).trans ?_
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hsup : ∀ x, ENNReal.ofReal (w x) = ⨆ N : ℕ, ENNReal.ofReal (min (w x) N) := by
    intro x
    refine le_antisymm ?_ (iSup_le fun N => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    refine le_iSup_of_le (Nat.ceil (w x)) (le_of_eq ?_)
    rw [min_eq_left (Nat.le_ceil _)]
  simp only [hsup]
  rw [lintegral_iSup (f := fun (N : ℕ) x => ENNReal.ofReal (min (w x) N))
    (fun N => ENNReal.measurable_ofReal.comp (hwc.min continuous_const).measurable)
    (fun N M hNM x => ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hNM)))]
  exact iSup_le hNle

theorem hd1_of {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (v : ℝ) : HasDerivAt g (deriv g v) v :=
  ((hg.differentiable (by norm_num)) v).hasDerivAt

theorem hd2_of {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) (v : ℝ) :
    HasDerivAt (deriv g) (deriv (deriv g) v) v := by
  have h2 : ContDiff ℝ (1 + 1) g := hg.of_le (by norm_num)
  have h1 : ContDiff ℝ 1 (deriv g) := (contDiff_succ_iff_deriv.1 h2).2.2
  exact ((h1.differentiable (by norm_num)) v).hasDerivAt

theorem contDiff_deriv_of {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) : Continuous (deriv g) := by
  have h2 : ContDiff ℝ (1 + 1) g := hg.of_le (by norm_num)
  exact (contDiff_succ_iff_deriv.1 h2).2.2.continuous

theorem contDiff_deriv2_of {g : ℝ → ℝ} (hg : ContDiff ℝ 3 g) : Continuous (deriv (deriv g)) := by
  have h3 : ContDiff ℝ (2 + 1) g := hg.of_le (by norm_num)
  exact contDiff_deriv_of (contDiff_succ_iff_deriv.1 h3).2.2

/-- Smooth saturation: `ρ0 v = v` for `v ≤ 0`, `= 1` for `v ≥ 1`. -/
noncomputable def rho0 (v : ℝ) : ℝ := v + (1 - v) * Real.smoothTransition v

theorem rho0_contDiff3 : ContDiff ℝ 3 rho0 :=
  contDiff_id.add ((contDiff_const.sub contDiff_id).mul Real.smoothTransition.contDiff)

theorem rho0_contDiff : ContDiff ℝ 2 rho0 := rho0_contDiff3.of_le (by norm_num)

theorem rho0_of_nonpos {v : ℝ} (hv : v ≤ 0) : rho0 v = v := by
  unfold rho0; rw [Real.smoothTransition.zero_of_nonpos hv]; ring

theorem rho0_of_one_le {v : ℝ} (hv : 1 ≤ v) : rho0 v = 1 := by
  unfold rho0; rw [Real.smoothTransition.one_of_one_le hv]; ring

theorem rho0_le_one (v : ℝ) : rho0 v ≤ 1 := by
  rcases le_or_gt 1 v with hv | hv
  · rw [rho0_of_one_le hv]
  · unfold rho0
    have := Real.smoothTransition.le_one v
    nlinarith

theorem rho0_nonneg {v : ℝ} (hv : 0 ≤ v) : 0 ≤ rho0 v := by
  rcases le_or_gt 1 v with h1 | h1
  · rw [rho0_of_one_le h1]; norm_num
  · unfold rho0
    have := Real.smoothTransition.nonneg v
    nlinarith

theorem deriv_rho0_out {v : ℝ} (hv : v ∉ Set.Icc (0 : ℝ) 1) :
    |deriv rho0 v| ≤ 1 ∧ deriv (deriv rho0) v = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hv
  rcases hv with hv | hv
  · have hev : rho0 =ᶠ[𝓝 v] fun s => s := by
      filter_upwards [Iio_mem_nhds (show v < 0 from hv)] with s hs using rho0_of_nonpos hs.le
    have hev1 : deriv rho0 =ᶠ[𝓝 v] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds (show v < 0 from hv)] with s hs
      have hev' : rho0 =ᶠ[𝓝 s] fun s => s := by
        filter_upwards [Iio_mem_nhds hs] with r hr using rho0_of_nonpos hr.le
      rw [hev'.deriv_eq, deriv_id'']
    rw [hev.deriv_eq, hev1.deriv_eq, deriv_id'', deriv_const]; simp
  · have hev1 : deriv rho0 =ᶠ[𝓝 v] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds (show 1 < v from hv)] with s hs
      have hev' : rho0 =ᶠ[𝓝 s] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds hs] with r hr using rho0_of_one_le hr.le
      rw [hev'.deriv_eq, deriv_const]
    rw [hev1.eq_of_nhds, hev1.deriv_eq, deriv_const]; simp

theorem bound_of_out {g : ℝ → ℝ} (hg : Continuous g) (hout : ∀ v, v ∉ Set.Icc (0 : ℝ) 1 → |g v| ≤ 1) :
    ∃ C, 0 ≤ C ∧ ∀ v, |g v| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hg.continuousOn (s := Set.Icc (0 : ℝ) 1))
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), fun v => ?_⟩
  by_cases hv : v ∈ Set.Icc (0 : ℝ) 1
  · have := hC v hv; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  · exact (hout v hv).trans (le_max_right _ _)

theorem rho0_d1_bound : ∃ C, 0 ≤ C ∧ ∀ v, |deriv rho0 v| ≤ C :=
  bound_of_out (contDiff_deriv_of rho0_contDiff) fun v hv => (deriv_rho0_out hv).1

theorem rho0_d2_bound : ∃ C, 0 ≤ C ∧ ∀ v, |deriv (deriv rho0) v| ≤ C :=
  bound_of_out (contDiff_deriv2_of rho0_contDiff3) fun v hv => by
    rw [(deriv_rho0_out hv).2]; simp

/-- Generator of a shifted composite `a + ρ (ψ₁ - a)`. -/
theorem genL_shift {d : ℕ} {ψ₁ ρ : ℝ → ℝ} (h1 : ContDiff ℝ 2 ψ₁) (h2 : ContDiff ℝ 2 ρ) (a : ℝ)
    (cv : SDEState d) (σx : SDEDiffusion d) (bx x : SDEState d) :
    genL (fun s => a + ρ (ψ₁ s - a)) cv σx bx x =
      deriv ρ (ψ₁ (∑ k, cv k * x k) - a) * genL ψ₁ cv σx bx x +
        (1 / 2) * deriv (deriv ρ) (ψ₁ (∑ k, cv k * x k) - a) * deriv ψ₁ (∑ k, cv k * x k) ^ 2 *
          ∑ j, (∑ k, cv k * σx (k, j)) ^ 2 := by
  have hD : deriv (fun s => a + ρ (ψ₁ s - a)) = fun s => deriv ρ (ψ₁ s - a) * deriv ψ₁ s :=
    funext fun s => (((hd1_of h2 _).comp s ((hd1_of h1 s).sub_const a)).const_add a).deriv
  have hD2 : deriv (fun s => deriv ρ (ψ₁ s - a) * deriv ψ₁ s) = fun s =>
      deriv (deriv ρ) (ψ₁ s - a) * deriv ψ₁ s * deriv ψ₁ s + deriv ρ (ψ₁ s - a) * deriv (deriv ψ₁) s :=
    funext fun s => (((hd2_of h2 _).comp s ((hd1_of h1 s).sub_const a)).mul (hd2_of h1 s)).deriv
  unfold genL
  rw [hD, hD2]
  simp only
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem genL_neg {d : ℕ} {ψ : ℝ → ℝ} (h1 : ContDiff ℝ 2 ψ) (M : ℝ)
    (cv : SDEState d) (σx : SDEDiffusion d) (bx x : SDEState d) :
    genL (fun s => M - ψ s) cv σx bx x = - genL ψ cv σx bx x := by
  have hD : deriv (fun s => M - ψ s) = fun s => - deriv ψ s :=
    funext fun s => ((hd1_of h1 s).const_sub M).deriv
  have hD2 : deriv (fun s => - deriv ψ s) = fun s => - deriv (deriv ψ) s :=
    funext fun s => (hd2_of h1 s).neg.deriv
  unfold genL
  rw [hD, hD2]
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

theorem genL_continuous {d : ℕ} {ψ : ℝ → ℝ} (h1 : ContDiff ℝ 2 ψ) (cv : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d} (hσ : Continuous σ₀)
    (hb : Continuous b₀) : Continuous fun x => genL ψ cv (σ₀ x) (b₀ x) x := by
  have hl : Continuous fun x : SDEState d => ∑ k, cv k * x k :=
    continuous_finset_sum _ fun k _ => continuous_const.mul (PiLp.continuous_apply 2 _ k)
  have hd1 := contDiff_deriv_of h1
  have hd2 : Continuous (deriv (deriv ψ)) :=
    ((contDiff_succ_iff_deriv.1 (h1.of_le (by norm_num) : ContDiff ℝ (1 + 1) ψ)).2.2).continuous_deriv le_rfl
  unfold genL
  refine ((hd1.comp hl).mul (continuous_finset_sum _ fun k _ => continuous_const.mul
    ((PiLp.continuous_apply 2 _ k).comp hb))).add (continuous_const.mul
    (continuous_finset_sum _ fun j _ => (hd2.comp hl).mul ((continuous_finset_sum _ fun k _ =>
      continuous_const.mul ((PiLp.continuous_apply 2 _ (k, j)).comp hσ)).pow 2)))

theorem deriv_rho0_neg {v : ℝ} (hv : v < 0) : deriv rho0 v = 1 ∧ deriv (deriv rho0) v = 0 := by
  have hev1 : deriv rho0 =ᶠ[𝓝 v] fun _ => 1 := by
    filter_upwards [Iio_mem_nhds hv] with s hs
    have hev' : rho0 =ᶠ[𝓝 s] fun s => s := by
      filter_upwards [Iio_mem_nhds hs] with r hr using rho0_of_nonpos hr.le
    rw [hev'.deriv_eq, deriv_id'']
  exact ⟨hev1.eq_of_nhds, by rw [hev1.deriv_eq, deriv_const]⟩

theorem deriv_rho0_gt {v : ℝ} (hv : 1 < v) : deriv rho0 v = 0 ∧ deriv (deriv rho0) v = 0 := by
  have hev1 : deriv rho0 =ᶠ[𝓝 v] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hv] with s hs
    have hev' : rho0 =ᶠ[𝓝 s] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds hs] with r hr using rho0_of_one_le hr.le
    rw [hev'.deriv_eq, deriv_const]
  exact ⟨hev1.eq_of_nhds, by rw [hev1.deriv_eq, deriv_const]⟩

/-- Bounded test functions: `∫ genL ψ dμ = 0` for every invariant `μ`. -/
theorem inv_genL_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (c : SDEState n) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψ0 : ∀ v, 0 ≤ ψ v) {M : ℝ}
    (hψM : ∀ v, ψ v ≤ M) {K : ℝ}
    (hK : ∀ x ∈ orthant n, |genL ψ c (diffusion C (0, x)) (drift C (0, x)) x| ≤ K)
    {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) :
    ∫ x, genL ψ c (diffusion C (0, posPart x)) (drift C (0, posPart x)) (posPart x) ∂μ = 0 := by
  have hμP := hμ.1
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  set G : SDEState n → ℝ := fun x =>
    genL ψ c (diffusion C (0, posPart x)) (drift C (0, posPart x)) (posPart x) with hG
  have hGc : Continuous G := (genL_continuous hψ c hσc hbc).comp continuous_posPart
  have hGb : ∀ x, |G x| ≤ K := fun x => hK _ (posPart_mem_orthant x)
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hGb 0)
  have hGint : Integrable G μ := Integrable.of_bound hGc.aestronglyMeasurable K
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hGb x)
  have hGx : ∀ x ∈ orthant n, genL ψ c (diffusion C (0, x)) (drift C (0, x)) x = G x := by
    intro x hx; simp only [hG, posPart_of_mem hx]
  have h1 := inv_w_le P C B X hfam hC c hψ hψ0 (w := fun x => K - G x) (continuous_const.sub hGc)
    (fun x => by have := abs_le.1 (hGb x); linarith) hK0
    (fun x hx => by rw [hGx x hx]; linarith) hμ
  have h2 := inv_w_le P C B X hfam hC c (ψ := fun s => M - ψ s) (contDiff_const.sub hψ)
    (fun v => sub_nonneg.2 (hψM v)) (w := fun x => K + G x) (continuous_const.add hGc)
    (fun x => by have := abs_le.1 (hGb x); linarith) hK0
    (fun x hx => by rw [genL_neg hψ, hGx x hx]; linarith) hμ
  have e1 : ∫ x, (K - G x) ∂μ ≤ K := by
    have hi : Integrable (fun x => K - G x) μ := (integrable_const K).sub hGint
    rw [← ENNReal.ofReal_le_ofReal_iff hK0, ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun x => by have := abs_le.1 (hGb x); simp only [Pi.zero_apply]; linarith)]
    exact h1
  have e2 : ∫ x, (K + G x) ∂μ ≤ K := by
    have hi : Integrable (fun x => K + G x) μ := (integrable_const K).add hGint
    rw [← ENNReal.ofReal_le_ofReal_iff hK0, ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun x => by have := abs_le.1 (hGb x); simp only [Pi.zero_apply]; linarith)]
    exact h2
  rw [integral_sub (integrable_const K) hGint] at e1
  rw [integral_add (integrable_const K) hGint] at e2
  simp only [integral_const, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul,
    probReal_univ] at e1 e2
  show ∫ x, G x ∂μ = 0
  linarith

/-- Continuous functions are bounded on `{x ∈ ℝⁿ₊ : cᵀx ≤ R}` (`c > 0`). -/
theorem bdd_on_ell {c : SDEState n} (hc : c ∈ openOrthant n) {g : SDEState n → ℝ}
    (hg : Continuous g) (R : ℝ) : ∃ K, ∀ x ∈ orthant n, ∑ k, c k * x k ≤ R → |g x| ≤ K := by
  set S : Set (SDEState n) := orthant n ∩ {x | ∑ k, c k * x k ≤ R} with hS
  have hcl : IsClosed S := orthant_isClosed.inter (isClosed_le (continuous_finset_sum _ fun k _ =>
    continuous_const.mul (PiLp.continuous_apply 2 _ k)) continuous_const)
  have hbd : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨∑ k, |R| / c k, fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (euc_norm_le_sum' x).trans (Finset.sum_le_sum fun k _ => ?_)
    have hxk := hx.1 k
    have hck := hc k
    have hsum : c k * x k ≤ ∑ j, c j * x j := Finset.single_le_sum
      (f := fun j => c j * x j) (fun j _ => mul_nonneg (hc j).le (hx.1 j)) (Finset.mem_univ k)
    rw [abs_of_nonneg hxk, le_div_iff₀ hck]
    have := hx.2; simp only [Set.mem_setOf_eq] at this
    nlinarith [le_abs_self R]
  obtain ⟨K, hK⟩ := (Metric.isCompact_of_isClosed_isBounded hcl hbd).exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨K, fun x hx hR => by have := hK x ⟨hx, hR⟩; rwa [Real.norm_eq_abs] at this⟩

/-- The truncated logarithm `ψ_L = L + ρ0 (psiK - L)`. -/
noncomputable def psiT (L : ℝ) (s : ℝ) : ℝ := L + rho0 (psiK s - L)

theorem psiT_contDiff (L : ℝ) : ContDiff ℝ 2 (psiT L) :=
  contDiff_const.add (rho0_contDiff.comp (psiK_contDiff.sub contDiff_const))

theorem psiT_nonneg {L : ℝ} (hL : 0 ≤ L) (s : ℝ) : 0 ≤ psiT L s := by
  unfold psiT
  rcases le_or_gt (psiK s - L) 0 with h | h
  · rw [rho0_of_nonpos h]; linarith [psiK_nonneg s]
  · linarith [rho0_nonneg h.le]

theorem psiT_le (L s : ℝ) : psiT L s ≤ L + 1 := by
  unfold psiT; linarith [rho0_le_one (psiK s - L)]

theorem genL_psiT (C : Coeffs n) {c x : SDEState n} (L : ℝ) :
    genL (psiT L) c (diffusion C (0, x)) (drift C (0, x)) x =
      deriv rho0 (psiK (∑ k, c k * x k) - L) * genL psiK c (diffusion C (0, x)) (drift C (0, x)) x +
        (1 / 2) * deriv (deriv rho0) (psiK (∑ k, c k * x k) - L) *
          (deriv psiK (∑ k, c k * x k) ^ 2 * ∑ j, (∑ k, c k * diffusion C (0, x) (k, j)) ^ 2) := by
  rw [show psiT L = fun s => L + rho0 (psiK s - L) from rfl,
    genL_shift psiK_contDiff rho0_contDiff L c (diffusion C (0, x)) (drift C (0, x)) x]
  ring

theorem psiT_genL_bdd (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c : SDEState n} (hc : c ∈ openOrthant n) (L : ℝ) :
    ∃ K, ∀ x ∈ orthant n, |genL (psiT L) c (diffusion C (0, x)) (drift C (0, x)) x| ≤ K := by
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  obtain ⟨K, hK⟩ := bdd_on_ell hc (genL_continuous (psiT_contDiff L) c hσc hbc) (Real.exp (L + 1))
  refine ⟨K, fun x hx => ?_⟩
  by_cases hR : ∑ k, c k * x k ≤ Real.exp (L + 1)
  · exact hK x hx hR
  · push Not at hR
    have hℓ0 : 0 ≤ ∑ k, c k * x k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k)
    have hu : 1 < psiK (∑ k, c k * x k) - L := by
      rw [psiK_eq (by linarith)]
      have h1 : L + 1 < Real.log (1 + ∑ k, c k * x k) := by
        rw [Real.lt_log_iff_exp_lt (by linarith)]; linarith
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    obtain ⟨d1, d2⟩ := deriv_rho0_gt hu
    rw [genL_psiT, d1, d2]
    have := hK 0 (fun i => le_refl _) (by simp; positivity)
    simp only [zero_mul, mul_zero, add_zero, abs_zero]
    exact (abs_nonneg _).trans this

/-- Part 1 of lemma 3.3: invariant measures integrate the weight of (3.8) with bound `H₂`. -/
theorem inv_weight_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (c : SDEState n) (hc : c ∈ openOrthant n) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {H₂ : ℝ} (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
        ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    {μ : Measure (SDEState n)} (hμ : IsInvariant P X μ) :
    ∫⁻ x, ENNReal.ofReal ((1 + ∑ i, c i * x i) ^ δ₀ *
        (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) ∂μ ≤ ENNReal.ofReal H₂ := by
  have hP := hfam.1
  have hμP := hμ.1
  set K' := H₂ with hK'
  have hK0 : 0 ≤ K' := hH₂.le
  set wt : SDEState n → ℝ := fun y => (1 + ∑ i, c i * y i) ^ δ₀ *
    (1 + ∑ i, (|C.f i y| + |C.g i y| ^ 2)) with hwt
  set w : SDEState n → ℝ := fun x => wt (posPart x) with hw
  have hfc : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hgc : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hlc : Continuous fun x : SDEState n => 1 + ∑ i, c i * x i :=
    continuous_const.add (continuous_finset_sum _ fun k _ => continuous_const.mul (PiLp.continuous_apply 2 _ k))
  have hwc : Continuous w := ((hlc.comp continuous_posPart).rpow_const fun x => Or.inr hδ₀.le).mul
    (continuous_const.add (continuous_finset_sum _ fun i _ => (hfc i).abs.add ((hgc i).abs.pow 2)))
  have hw0 : ∀ x, 0 ≤ w x := fun x => by
    have hp : 0 ≤ 1 + ∑ i, c i * posPart x i := by
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
        mul_nonneg (hc i).le (posPart_mem_orthant x i)
      linarith only [this]
    exact mul_nonneg (Real.rpow_nonneg hp _) (by positivity)
  have hall : ∀ x ∈ orthant n, ∀ᵐ ω ∂P, ∀ u, X x u ω ∈ orthant n := fun x hx =>
    orthant_inv_all P C B hfam.2.1 hC hx (hfam.2.2 x hx)
  choose κ hκ hκx using kernel_of_family P C B X hfam hC
  have hXm : ∀ x ∈ orthant n, ∀ t, Measurable (X x t) := fun x hx t => (hfam.2.2 x hx).1 t
  have hXc : ∀ x ∈ orthant n, ∀ ω, Continuous fun t => X x t ω := fun x hx => (hfam.2.2 x hx).2.1
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  have hΨc : Continuous fun x : SDEState n => H₂ * (1 + ∑ i, c i * x i) ^ δ₀ :=
    continuous_const.mul (hlc.rpow_const fun x => Or.inr hδ₀.le)
  have hNle : ∀ N : ℕ, ∫⁻ x, ENNReal.ofReal (min (w x) N) ∂μ ≤ ENNReal.ofReal K' := by
    intro N
    set F : ℕ → SDEState n → ℝ≥0∞ := fun m x =>
      ENNReal.ofReal (min (H₂ * (1 + ∑ i, c i * x i) ^ δ₀ / ((m : ℝ) + 1) + K') N) with hF
    have hstep : ∀ m : ℕ, ∫⁻ x, ENNReal.ofReal (min (w x) N) ∂μ ≤ ∫⁻ x, F m x ∂μ := by
      intro m
      have ht : (0 : ℝ) < (m : ℝ) + 1 := Nat.cast_add_one_pos m
      have e := inv_avg_eq hμ hXm hXc κ hκx (h := fun x => min (w x) N)
        (hwc.min continuous_const) (fun x => le_min (hw0 x) (Nat.cast_nonneg N))
        (fun x => min_le_right _ _) _ ht
      have hbd : ∫⁻ x, ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..((m : ℝ) + 1),
          min (w (X x u.toNNReal ω)) N) ∂P ∂μ ≤
          ∫⁻ x, ENNReal.ofReal ((m : ℝ) + 1) * F m x ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with x hx
        have hle1 : ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..((m : ℝ) + 1),
            min (w (X x u.toNNReal ω)) N) ∂P ≤
            ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + ((m : ℝ) + 1))) := by
          have hT := h38 x hx ((m : ℝ) + 1).toNNReal (by simp [ht])
          rw [show (((m : ℝ) + 1).toNNReal : ℝ) = (m : ℝ) + 1 from Real.coe_toNNReal _ ht.le] at hT
          refine le_trans (lintegral_mono_ae ?_) hT
          filter_upwards [hall x hx] with ω hω
          have hcu : Continuous fun u : ℝ => w (X x u.toNNReal ω) :=
            hwc.comp ((hXc x hx ω).comp continuous_real_toNNReal)
          calc ENNReal.ofReal (∫ u in (0 : ℝ)..((m : ℝ) + 1), min (w (X x u.toNNReal ω)) N)
              ≤ ENNReal.ofReal (∫ u in (0 : ℝ)..((m : ℝ) + 1), w (X x u.toNNReal ω)) :=
                ENNReal.ofReal_le_ofReal (intervalIntegral.integral_mono_on ht.le
                  ((hcu.min continuous_const).intervalIntegrable _ _) (hcu.intervalIntegrable _ _)
                  fun u _ => min_le_left _ _)
            _ = ∫⁻ u in Set.Ioc (0 : ℝ) ((m : ℝ) + 1), ENNReal.ofReal (w (X x u.toNNReal ω)) := by
                rw [intervalIntegral.integral_of_le ht.le, ofReal_integral_eq_lintegral_ofReal
                  ((hcu.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self) (ae_of_all _ fun u => hw0 _)]
            _ ≤ ∫⁻ u in Set.Icc (0 : ℝ) ((m : ℝ) + 1), ENNReal.ofReal (w (X x u.toNNReal ω)) :=
                lintegral_mono_set Set.Ioc_subset_Icc_self
            _ = _ := lintegral_congr fun u => by simp only [hw, hwt, posPart_of_mem (hω _)]
        have hle2 : ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..((m : ℝ) + 1),
            min (w (X x u.toNNReal ω)) N) ∂P ≤ ENNReal.ofReal (N * ((m : ℝ) + 1)) := by
          refine le_trans (lintegral_mono (g := fun _ => ENNReal.ofReal (N * ((m : ℝ) + 1)))
            fun ω => ENNReal.ofReal_le_ofReal ?_) (by simp)
          calc _ ≤ ∫ _u in (0 : ℝ)..((m : ℝ) + 1), (N : ℝ) :=
                intervalIntegral.integral_mono_on ht.le
                  (((hwc.comp ((hXc x hx ω).comp continuous_real_toNNReal)).min
                    continuous_const).intervalIntegrable _ _)
                  (continuous_const.intervalIntegrable _ _) fun u _ => min_le_right _ _
            _ = N * ((m : ℝ) + 1) := by simp [mul_comm]
        refine le_trans (le_min hle1 hle2) (le_of_eq ?_)
        simp only [hF]
        rw [← ENNReal.ofReal_min, ← ENNReal.ofReal_mul ht.le]
        congr 1
        rw [mul_min_of_nonneg _ _ ht.le]
        congr 1
        · field_simp
          ring
        · ring
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hbd
      exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 ht).ne' ENNReal.ofReal_ne_top).1
        (e.trans_le hbd)
    have hlim : Tendsto (fun m => ∫⁻ x, F m x ∂μ) atTop (𝓝 (∫⁻ _x, ENNReal.ofReal (min K' N) ∂μ)) := by
      refine tendsto_lintegral_of_dominated_convergence (fun _ => ENNReal.ofReal N)
        (fun m => ENNReal.measurable_ofReal.comp (((hΨc.div_const _).add continuous_const).min
          continuous_const).measurable)
        (fun m => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _)) (by simp)
        (ae_of_all _ fun x => ?_)
      have h1 : Tendsto (fun m : ℕ => H₂ * (1 + ∑ i, c i * x i) ^ δ₀ / ((m : ℝ) + 1)) atTop (𝓝 0) := by
        have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (H₂ * (1 + ∑ i, c i * x i) ^ δ₀)
        simpa [div_eq_mul_inv] using this
      have h2 := (h1.add_const K').min (tendsto_const_nhds (x := ((N : ℕ) : ℝ)))
      rw [zero_add] at h2
      exact (ENNReal.continuous_ofReal.tendsto _).comp h2
    refine (ge_of_tendsto' hlim fun m => hstep m).trans ?_
    simp only [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
  rw [show ∫⁻ x, ENNReal.ofReal ((1 + ∑ i, c i * x i) ^ δ₀ * (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) ∂μ =
      ∫⁻ x, ENNReal.ofReal (w x) ∂μ from lintegral_congr_ae (by
        filter_upwards [hae] with x hx; simp only [hw, hwt, posPart_of_mem hx])]
  have hsup : ∀ x, ENNReal.ofReal (w x) = ⨆ N : ℕ, ENNReal.ofReal (min (w x) N) := by
    intro x
    refine le_antisymm ?_ (iSup_le fun N => ENNReal.ofReal_le_ofReal (min_le_left _ _))
    refine le_iSup_of_le (Nat.ceil (w x)) (le_of_eq ?_)
    rw [min_eq_left (Nat.le_ceil _)]
  simp only [hsup]
  rw [lintegral_iSup (f := fun (N : ℕ) x => ENNReal.ofReal (min (w x) N))
    (fun N => ENNReal.measurable_ofReal.comp (hwc.min continuous_const).measurable)
    (fun N M hNM x => ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hNM)))]
  exact iSup_le hNle

noncomputable def Ef (C : Coeffs n) (c x : SDEState n) : ℝ :=
  deriv psiK (∑ k, c k * x k) ^ 2 * ∑ j, (∑ k, c k * diffusion C (0, x) (k, j)) ^ 2

theorem genL_psiK_split (C : Coeffs n) {c x : SDEState n} (hc : c ∈ openOrthant n) (hx : x ∈ orthant n) :
    genL psiK c (diffusion C (0, x)) (drift C (0, x)) x =
      (1 + ∑ k, c k * x k)⁻¹ * ∑ k, c k * (x k * C.f k x) - (1 / 2) * Ef C c x := by
  have hℓ : 0 ≤ ∑ k, c k * x k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k)
  have hℓ' : -1 / 4 < ∑ k, c k * x k := by linarith
  unfold genL Ef
  rw [deriv_psiK hℓ', deriv2_psiK hℓ', ← Finset.mul_sum, ← inv_pow]
  simp only [drift, PiLp.toLp_apply, posPart_of_mem hx]
  ring

theorem A1_bound (C : Coeffs n) {c y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ orthant n) :
    |(1 + ∑ k, c k * y k)⁻¹ * ∑ k, c k * (y k * C.f k y)| ≤ ∑ k, |C.f k y| := by
  have hℓ : 0 ≤ ∑ k, c k * y k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hy k)
  have hp : 0 < 1 + ∑ k, c k * y k := by linarith
  rw [abs_mul, abs_of_pos (inv_pos.2 hp), inv_mul_le_iff₀ hp]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hck : c k * y k ≤ 1 + ∑ j, c j * y j := by
    have := Finset.single_le_sum (f := fun j => c j * y j) (fun j _ => mul_nonneg (hc j).le (hy j))
      (Finset.mem_univ k)
    simp only at this; linarith
  rw [show c k * (y k * C.f k y) = (c k * y k) * C.f k y by ring, abs_mul,
    abs_of_nonneg (mul_nonneg (hc k).le (hy k))]
  exact mul_le_mul_of_nonneg_right hck (abs_nonneg _)

theorem Ef_bound (C : Coeffs n) {c x : SDEState n} (hc : c ∈ openOrthant n) (hx : x ∈ orthant n) :
    0 ≤ Ef C c x ∧ Ef C c x ≤ (∑ i, ∑ l, |C.sig i l|) * ∑ k, C.g k x ^ 2 := by
  have hℓ : 0 ≤ ∑ k, c k * x k := Finset.sum_nonneg fun k _ => mul_nonneg (hc k).le (hx k)
  have hp : 0 < 1 + ∑ k, c k * x k := by linarith
  set p := 1 + ∑ k, c k * x k with hpdef
  have hd : deriv psiK (∑ k, c k * x k) = p⁻¹ := deriv_psiK (by linarith)
  set v : Fin n → ℝ := fun k => c k * x k * C.g k x with hv
  have hsum : ∑ j, (∑ k, c k * diffusion C (0, x) (k, j)) ^ 2 = ∑ i, ∑ l, C.sig i l * v i * v l := by
    rw [← sig_sum_sq C v]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [diffusion, PiLp.toLp_apply, posPart_of_mem hx, hv]
    ring
  have hvk : ∀ k, |v k| ≤ p * |C.g k x| := by
    intro k
    have hck : c k * x k ≤ p := by
      have := Finset.single_le_sum (f := fun j => c j * x j) (fun j _ => mul_nonneg (hc j).le (hx j))
        (Finset.mem_univ k)
      simp only at this; linarith only [this, hpdef]
    have e : v k = (c k * x k) * C.g k x := rfl
    rw [e, abs_mul, abs_of_nonneg (mul_nonneg (hc k).le (hx k))]
    exact mul_le_mul_of_nonneg_right hck (abs_nonneg _)
  set G2 := ∑ k, C.g k x ^ 2 with hG2
  have hgk : ∀ k, C.g k x ^ 2 ≤ G2 := fun k => Finset.single_le_sum (f := fun j => C.g j x ^ 2)
    (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  have hgg : ∀ i l, |C.g i x| * |C.g l x| ≤ G2 := by
    intro i l
    have h1 := hgk i
    have h2 := hgk l
    have : 2 * (|C.g i x| * |C.g l x|) ≤ C.g i x ^ 2 + C.g l x ^ 2 := by
      linarith only [sq_nonneg (|C.g i x| - |C.g l x|), sq_abs (C.g i x), sq_abs (C.g l x)]
    linarith only [this, h1, h2]
  have hQ : ∑ i, ∑ l, C.sig i l * v i * v l ≤ p ^ 2 * ((∑ i, ∑ l, |C.sig i l|) * G2) := by
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun l _ => ?_
    have e1 : C.sig i l * v i * v l ≤ |C.sig i l| * (|v i| * |v l|) := by
      have h := le_abs_self (C.sig i l * v i * v l)
      rw [abs_mul, abs_mul] at h
      exact h.trans_eq (mul_assoc _ _ _)
    have e2 : |v i| * |v l| ≤ p ^ 2 * G2 := by
      calc |v i| * |v l| ≤ (p * |C.g i x|) * (p * |C.g l x|) :=
            mul_le_mul (hvk i) (hvk l) (abs_nonneg _) (mul_nonneg hp.le (abs_nonneg _))
        _ = p ^ 2 * (|C.g i x| * |C.g l x|) := by ring
        _ ≤ p ^ 2 * G2 := mul_le_mul_of_nonneg_left (hgg i l) (sq_nonneg p)
    calc C.sig i l * v i * v l ≤ |C.sig i l| * (|v i| * |v l|) := e1
      _ ≤ |C.sig i l| * (p ^ 2 * G2) := mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
      _ = p ^ 2 * (|C.sig i l| * G2) := by ring
  unfold Ef
  rw [hd]
  constructor
  · exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  · rw [hsum]
    calc p⁻¹ ^ 2 * ∑ i, ∑ l, C.sig i l * v i * v l
        ≤ p⁻¹ ^ 2 * (p ^ 2 * ((∑ i, ∑ l, |C.sig i l|) * G2)) :=
          mul_le_mul_of_nonneg_left hQ (sq_nonneg _)
      _ = (∑ i, ∑ l, |C.sig i l|) * G2 := by
          rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hp.ne', one_pow, one_mul]

theorem arith1 {a e F G Cs D : ℝ} (ha : |a| ≤ F) (he0 : 0 ≤ e) (he : e ≤ Cs * G) (hF : 0 ≤ F)
    (hG : 0 ≤ G) (hCs : 0 ≤ Cs) (hD : 1 + Cs ≤ D) : |a - 1 / 2 * e| ≤ D * (1 + (F + G)) := by
  have h1 : |a - 1 / 2 * e| ≤ F + Cs * G := by
    rw [abs_le] at ha ⊢; constructor <;> linarith only [ha.1, ha.2, he0, he]
  have h2 : F + Cs * G ≤ (1 + Cs) * (1 + (F + G)) := by linarith only [hG, hCs, mul_nonneg hCs hF]
  have h3 : (1 + Cs) * (1 + (F + G)) ≤ D * (1 + (F + G)) :=
    mul_le_mul_of_nonneg_right hD (by linarith only [hF, hG])
  linarith only [h1, h2, h3]

theorem arith2 {r1 r2 a e F G Cs C1 C2 : ℝ} (hr1 : |r1| ≤ C1) (hr2 : |r2| ≤ C2) (ha : |a| ≤ F)
    (he0 : 0 ≤ e) (he : e ≤ Cs * G) (hF : 0 ≤ F) (hG : 0 ≤ G) (hCs : 0 ≤ Cs) (hC1 : 0 ≤ C1)
    (hC2 : 0 ≤ C2) :
    |r1 * (a - 1 / 2 * e) + 1 / 2 * r2 * e| ≤ ((C1 + 1) * (1 + Cs) + C2 * Cs) * (1 + (F + G)) := by
  have h1 : |a - 1 / 2 * e| ≤ F + Cs * G := by
    rw [abs_le] at ha ⊢; constructor <;> linarith only [ha.1, ha.2, he0, he]
  have h2 : |r1 * (a - 1 / 2 * e)| ≤ C1 * (F + Cs * G) := by
    rw [abs_mul]; exact mul_le_mul hr1 h1 (abs_nonneg _) hC1
  have h3 : |1 / 2 * r2 * e| ≤ C2 * (Cs * G) := by
    rw [show 1 / 2 * r2 * e = r2 * (e / 2) by ring, abs_mul, abs_of_nonneg (by linarith only [he0] : 0 ≤ e / 2)]
    exact mul_le_mul hr2 (by linarith only [he, he0]) (by linarith only [he0]) hC2
  have h4 := abs_add_le (r1 * (a - 1 / 2 * e)) (1 / 2 * r2 * e)
  have h5 : C1 * (F + Cs * G) + C2 * (Cs * G) ≤ ((C1 + 1) * (1 + Cs) + C2 * Cs) * (1 + (F + G)) := by
    linarith only [hC1, hF, hG, hCs, mul_nonneg hC1 hG, mul_nonneg hC1 hCs,
      mul_nonneg (mul_nonneg hC1 hCs) hF, mul_nonneg hCs hF, mul_nonneg hCs hG, mul_nonneg hC2 hCs,
      mul_nonneg (mul_nonneg hC2 hCs) hF]
  linarith only [h2, h3, h4, h5]

/-- Lemma 3.3 (Hening–Nguyen): proof in the library. -/
theorem lemma_3_3_proof (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
        ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ) :
    ∫⁻ x, ENNReal.ofReal ((1 + ∑ i, c i * x i) ^ δ₀ *
        (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) ∂μ ≤ ENNReal.ofReal H₂ ∧
      Integrable (cBracket C c) μ ∧ ∫ x, cBracket C c x ∂μ = 0 := by
  have hC := hA.2.1
  have hc := hA.2.2.1
  have hμP := hμ.1
  have hae : ∀ᵐ x ∂μ, x ∈ orthant n := by rw [ae_iff]; exact hμ.2.1
  have hW := inv_weight_le P C B X hX hC c hc hδ₀.1 hH₂ h38 hμ
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  have hfc : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hgc : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  set wt0 : SDEState n → ℝ := fun x => 1 + (∑ i, |C.f i (posPart x)| + ∑ i, C.g i (posPart x) ^ 2)
    with hwt0
  have hwt0c : Continuous wt0 := continuous_const.add
    ((continuous_finset_sum _ fun i _ => (hfc i).abs).add (continuous_finset_sum _ fun i _ => (hgc i).pow 2))
  have hwt0n : ∀ x, 0 ≤ wt0 x := fun x => by positivity
  have hwt0i : Integrable wt0 μ := by
    refine (lintegral_ofReal_ne_top_iff_integrable hwt0c.aestronglyMeasurable
      (ae_of_all _ hwt0n)).1 ?_
    refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (lintegral_mono_ae ?_) hW)
    filter_upwards [hae] with x hx
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [hwt0, posPart_of_mem hx, sq_abs, Finset.sum_add_distrib]
    have hp : 1 ≤ 1 + ∑ i, c i * x i := by
      have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_nonneg (hc i).le (hx i)
      linarith
    have h1 : 1 ≤ (1 + ∑ i, c i * x i) ^ δ₀ := Real.one_le_rpow hp hδ₀.1.le
    have h2 : 0 ≤ 1 + (∑ i, |C.f i x| + ∑ i, C.g i x ^ 2) := by positivity
    nlinarith
  obtain ⟨C1, hC1, hC1b⟩ := rho0_d1_bound
  obtain ⟨C2, hC2, hC2b⟩ := rho0_d2_bound
  set Cs := ∑ i, ∑ l, |C.sig i l| with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  set D := (C1 + 1) * (1 + Cs) + C2 * Cs with hD
  have hD1 : 1 + Cs ≤ D := by nlinarith [mul_nonneg hC1 hCs0, mul_nonneg hC2 hCs0]
  set cB : SDEState n → ℝ := fun x =>
    genL psiK c (diffusion C (0, posPart x)) (drift C (0, posPart x)) (posPart x) with hcB
  have hcBc : Continuous cB := (genL_continuous psiK_contDiff c hσc hbc).comp continuous_posPart
  have hcBb : ∀ x, |cB x| ≤ D * wt0 x := fun x => by
    have hy := posPart_mem_orthant x
    obtain ⟨hE0, hE1⟩ := Ef_bound C hc hy
    simp only [hcB, hwt0]
    rw [genL_psiK_split C hc hy]
    exact arith1 (A1_bound C hc hy) hE0 hE1 (by positivity) (by positivity) hCs0 hD1
  set GLf : ℕ → SDEState n → ℝ := fun L x =>
    genL (psiT (L : ℝ)) c (diffusion C (0, posPart x)) (drift C (0, posPart x)) (posPart x) with hGLf
  have hGLfb : ∀ L x, |GLf L x| ≤ D * wt0 x := fun L x => by
    have hy := posPart_mem_orthant x
    obtain ⟨hE0, hE1⟩ := Ef_bound C hc hy
    simp only [hGLf, hwt0, hD]
    rw [genL_psiT, genL_psiK_split C hc hy]
    exact arith2 (hC1b _) (hC2b _) (A1_bound C hc hy) hE0 hE1 (by positivity) (by positivity) hCs0
      hC1 hC2
  have hGLf0 : ∀ L : ℕ, ∫ x, GLf L x ∂μ = 0 := fun L => by
    obtain ⟨K, hK⟩ := psiT_genL_bdd C hC hc (L : ℝ)
    exact inv_genL_zero P C B X hX hC c (psiT_contDiff _) (psiT_nonneg (Nat.cast_nonneg L))
      (psiT_le _) hK hμ
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun L : ℕ => GLf L x) atTop (𝓝 (cB x)) := by
    filter_upwards [hae] with x hx
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (psiK (∑ k, c k * x k))] with L hL
    obtain ⟨d1, d2⟩ := deriv_rho0_neg (show psiK (∑ k, c k * x k) - L < 0 by linarith)
    simp only [hGLf, hcB, posPart_of_mem hx]
    rw [genL_psiT, d1, d2]
    ring
  have hcBint : Integrable cB μ := (hwt0i.const_mul D).mono' hcBc.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hcBb x)
  have hcB0 : ∫ x, cB x ∂μ = 0 := by
    have ht := tendsto_integral_of_dominated_convergence (fun x => D * wt0 x)
      (fun L => ((genL_continuous (psiT_contDiff (L : ℝ)) c hσc hbc).comp
        continuous_posPart).aestronglyMeasurable)
      (hwt0i.const_mul D) (fun L => ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hGLfb L x) hlim
    have ht' : Tendsto (fun L : ℕ => ∫ x, GLf L x ∂μ) atTop (𝓝 (∫ x, cB x ∂μ)) := ht
    rw [show (fun L : ℕ => ∫ x, GLf L x ∂μ) = fun _ => (0 : ℝ) from funext hGLf0] at ht'
    exact tendsto_nhds_unique ht' tendsto_const_nhds
  have hae_eq : cB =ᵐ[μ] cBracket C c := by
    filter_upwards [hae] with x hx
    simp only [hcB, posPart_of_mem hx]
    exact genL_kolm C hc hx
  refine ⟨hW, hcBint.congr hae_eq, ?_⟩
  rw [← integral_congr_ae hae_eq]
  exact hcB0

end L33

end ItoLib

-- ===== HA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HA (Harris route, s29): abstract Hairer-Mattingly contraction ("Yet another look at Harris'
ergodic theorem", Thm 3.1) in function form. Drift `QV ≤ γ V + K` plus pairwise overlap
`tvDist (Q x) (Q y) ≤ 1 - α` on `{V x + V y ≤ R}` (`R > 2K/(1-γ)`) make `Q` a strict contraction
for the weighted oscillation `|φ x - φ y| ≤ M (2 + β V x + β V y)`. -/

section HA
variable {X : Type*} [MeasurableSpace X]

end HA
end ItoLib

-- ===== HB =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! HB (Harris route, s30): iterates of a Markov kernel, drift iteration, and the TV-Cauchy
estimate for `kpow κ k x` coming from `hm_iterate` (HA). -/

section HB
variable {X : Type*} [MeasurableSpace X]

end HB
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
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (H₂ : ℝ) (hH₂ : 0 < H₂)
    (h38 : ∀ x ∈ orthant n, ∀ t : ℝ≥0, 0 < t →
      ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
          ENNReal.ofReal ((1 + ∑ i, c i * X x s.toNNReal ω i) ^ δ₀ *
            (1 + ∑ i, (|C.f i (X x s.toNNReal ω)| + |C.g i (X x s.toNNReal ω)| ^ 2)))) ∂P ≤
        ENNReal.ofReal (H₂ * ((1 + ∑ i, c i * x i) ^ δ₀ + t)))
    (μ : Measure (SDEState n)) (hμ : IsInvariant P X μ) :
    ∫⁻ x, ENNReal.ofReal ((1 + ∑ i, c i * x i) ^ δ₀ *
        (1 + ∑ i, (|C.f i x| + |C.g i x| ^ 2))) ∂μ ≤ ENNReal.ofReal H₂ ∧
      Integrable (cBracket C c) μ ∧ ∫ x, cBracket C c x ∂μ = 0 := by
  exact ItoLib.lemma_3_3_proof hn P C B X hX c γb hA δ₀ hδ₀ H₂ hH₂ h38 μ hμ
