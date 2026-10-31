-- Prove2me | solution 1 for StochKolmogorov.Persist.kolmogorov_sde_pathwise_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T04:29:07.013724+00:00
-- url     : https://prove2.me/submissions/ace61993-2f44-4123-a55a-c3fb576d8f89

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

theorem hasDerivAt_sq_affine (α β r : ℝ) :
    HasDerivAt (fun s : ℝ => (α + s * β) ^ 2) (2 * (α + r * β) * β) r := by
  have h := (((hasDerivAt_id r).mul_const β).const_add α).pow 2
  exact h.congr_deriv (by simp only [id]; ring)

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

def ixc (k : Fin d) : Fin (d + d + 1) := Fin.castSucc (Fin.castAdd d k)
def iyc (k : Fin d) : Fin (d + d + 1) := Fin.castSucc (Fin.natAdd d k)
def iac : Fin (d + d + 1) := Fin.last _

/-- `Q(u) = |x - y|²`. -/
noncomputable def Qf (u : SDEState (d + d + 1)) : ℝ := ∑ k, (u (ixc k) - u (iyc k)) ^ 2
/-- `N(u) = |x|² + |y|²`. -/
noncomputable def Nf (u : SDEState (d + d + 1)) : ℝ := ∑ k, (u (ixc k) ^ 2 + u (iyc k) ^ 2)
/-- Inner test function `e^{-a} |x-y|²`. -/
noncomputable def F0f (u : SDEState (d + d + 1)) : ℝ := Real.exp (-u iac) * Qf u
/-- Cut-off test function `e^{-a} χ_r(|x|²+|y|²) |x-y|²`. -/
noncomputable def Ff (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * (cutoff r (Nf u) * Qf u)

theorem coord_contDiff {e : ℕ} (i : Fin e) {n : ℕ∞} :
    ContDiff ℝ n (fun u : SDEState e => u i) :=
  (EuclideanSpace.proj i : SDEState e →L[ℝ] ℝ).contDiff

theorem Qf_contDiff {n : ℕ∞} : ContDiff ℝ n (Qf (d := d)) := by
  unfold Qf
  exact ContDiff.sum fun k _ => ((coord_contDiff _).sub (coord_contDiff _)).pow 2

theorem Nf_contDiff {n : ℕ∞} : ContDiff ℝ n (Nf (d := d)) := by
  unfold Nf
  exact ContDiff.sum fun k _ => ((coord_contDiff _).pow 2).add ((coord_contDiff _).pow 2)

theorem F0f_contDiff {n : ℕ∞} : ContDiff ℝ n (F0f (d := d)) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul Qf_contDiff

theorem Ff_contDiff (r : ℝ) {n : ℕ∞} : ContDiff ℝ n (Ff (d := d) r) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul
    (((cutoff_contDiff r).comp Nf_contDiff).mul Qf_contDiff)

theorem Ff_eq_F0f_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : Nf u < r) :
    Ff r =ᶠ[𝓝 u] F0f := by
  have hc : ContinuousAt (Nf (d := d)) u := (Nf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (gt_mem_nhds hu)] with w hw
  simp only [Ff, F0f, cutoff_eq_one hw.le, one_mul]

/-- Line expansion of `F0f` (coordinates of `u + r • v`). -/
theorem F0f_line (u v : SDEState (d + d + 1)) (r : ℝ) :
    F0f (u + r • v) = Real.exp (-(u iac + r * v iac)) *
      ∑ k, ((u (ixc k) - u (iyc k)) + r * (v (ixc k) - v (iyc k))) ^ 2 := by
  simp only [F0f, Qf, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `D F0(u) v = e^{-a} (2 Σ (x-y)·(v_x - v_y) - v_a |x-y|²)`. -/
theorem F0f_fderiv (u v : SDEState (d + d + 1)) :
    fderiv ℝ F0f u v = Real.exp (-u iac) *
      (2 * ∑ k, (u (ixc k) - u (iyc k)) * (v (ixc k) - v (iyc k)) - v iac * Qf u) := by
  refine fderiv_eq_of_line (F0f_contDiff (n := 1)).differentiable_one u v ?_
  simp only [F0f_line]
  have he := (((hasDerivAt_mul_const (v iac)).const_add (u iac)).neg (x := (0 : ℝ))).exp
  have hs : HasDerivAt (fun r : ℝ => ∑ k, ((u (ixc k) - u (iyc k)) + r * (v (ixc k) - v (iyc k))) ^ 2)
      (∑ k, 2 * ((u (ixc k) - u (iyc k)) + 0 * (v (ixc k) - v (iyc k))) *
        (v (ixc k) - v (iyc k))) 0 :=
    HasDerivAt.fun_sum fun k _ => hasDerivAt_sq_affine _ _ 0
  refine (he.mul hs).congr_deriv ?_
  simp only [Pi.neg_apply, zero_mul, add_zero, Qf]
  have h2 : ∑ k, 2 * (u (ixc k) - u (iyc k)) * (v (ixc k) - v (iyc k)) =
      2 * ∑ k, (u (ixc k) - u (iyc k)) * (v (ixc k) - v (iyc k)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [h2]; ring

/-- `D² F0(u)(v,v) = 2 e^{-a} |v_x - v_y|²` for `v_a = 0`. -/
theorem F0f_fderiv2 (u v : SDEState (d + d + 1)) (hv : v iac = 0) :
    fderiv ℝ (fderiv ℝ F0f) u v v = Real.exp (-u iac) *
      (2 * ∑ k, (v (ixc k) - v (iyc k)) ^ 2) := by
  refine fderiv2_eq_of_line F0f_contDiff u v
    (φ' := fun s => Real.exp (-u iac) * ∑ k, 2 * ((u (ixc k) - u (iyc k)) +
      s * (v (ixc k) - v (iyc k))) * (v (ixc k) - v (iyc k))) (fun s => ?_) ?_
  · simp only [F0f_line, hv, mul_zero, add_zero]
    exact (HasDerivAt.fun_sum fun k _ => hasDerivAt_sq_affine _ _ s).const_mul _
  · have hs : HasDerivAt (fun s : ℝ => ∑ k, 2 * ((u (ixc k) - u (iyc k)) +
        s * (v (ixc k) - v (iyc k))) * (v (ixc k) - v (iyc k)))
        (∑ k, 2 * (v (ixc k) - v (iyc k)) * (v (ixc k) - v (iyc k))) 0 := by
      refine HasDerivAt.fun_sum fun k _ => ?_
      have := ((((hasDerivAt_id (0 : ℝ)).mul_const (v (ixc k) - v (iyc k))).const_add
        (u (ixc k) - u (iyc k))).const_mul 2).mul_const (v (ixc k) - v (iyc k))
      exact this.congr_deriv (by first | ring | (simp; ring) | simp)
    refine (hs.const_mul (Real.exp (-u iac))).congr_deriv ?_
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

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

theorem Nf_pack (x y : SDEState d) (a : ℝ) : Nf (pack x y a) = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  simp only [Nf, pack_ixc, pack_iyc, Finset.sum_add_distrib, EuclideanSpace.real_norm_sq_eq]

theorem Qf_pack (x y : SDEState d) (a : ℝ) : Qf (pack x y a) = ‖x - y‖ ^ 2 := by
  simp only [Qf, pack_ixc, pack_iyc, EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]

theorem Ff_translate (r c : ℝ) (w : SDEState (d + d + 1)) :
    Ff r (w + c • (eac (d := d))) = Real.exp (-c) * Ff r w := by
  have hx : ∀ k, (w + c • (eac (d := d))) (ixc k) = w (ixc k) := fun k => by
    have : (eac (d := d)) (ixc k) = 0 := by simp [eac]
    simp [this]
  have hy : ∀ k, (w + c • (eac (d := d))) (iyc k) = w (iyc k) := fun k => by
    have : (eac (d := d)) (iyc k) = 0 := by simp [eac]
    simp [this]
  have ha : (w + c • (eac (d := d))) iac = w iac + c := by
    have : (eac (d := d)) iac = 1 := by simp [eac]
    simp [this]
  simp only [Ff, Nf, Qf, hx, hy, ha]
  rw [show -(w iac + c) = -c + -w iac by ring, Real.exp_add]
  ring

theorem Ff_fderiv_pack (r : ℝ) (x y : SDEState d) (a : ℝ) :
    fderiv ℝ (Ff r) (pack x y a) = Real.exp (-a) • fderiv ℝ (Ff r) (pack x y 0) ∧
      fderiv ℝ (fderiv ℝ (Ff r)) (pack x y a) =
        Real.exp (-a) • fderiv ℝ (fderiv ℝ (Ff r)) (pack x y 0) := by
  have h := fderiv12_translate (Ff_contDiff r) (a • (eac (d := d))) (Real.exp (-a))
    (fun w => Ff_translate r a w) (pack x y 0)
  rwa [pack_add_eac, zero_add] at h

theorem Ff_fderiv_eac (r : ℝ) (u : SDEState (d + d + 1)) :
    fderiv ℝ (Ff r) u (eac (d := d)) = -Ff r u := by
  refine fderiv_eq_of_line ((Ff_contDiff r (n := 1)).differentiable_one) u _ ?_
  have e : (fun s : ℝ => Ff r (u + s • (eac (d := d)))) = fun s => Real.exp (-s) * Ff r u :=
    funext fun s => Ff_translate r s u
  rw [e]
  have h := ((hasDerivAt_neg (0 : ℝ)).exp).mul_const (Ff r u)
  refine h.congr_deriv ?_
  simp

theorem Ff_nonneg (r : ℝ) (u : SDEState (d + d + 1)) : 0 ≤ Ff r u := by
  unfold Ff Qf
  exact mul_nonneg (Real.exp_pos _).le
    (mul_nonneg (cutoff_nonneg _ _) (Finset.sum_nonneg fun k _ => sq_nonneg _))

theorem Ff_zero_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nf u) :
    Ff r =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
  have hc : ContinuousAt (Nf (d := d)) u := (Nf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hu)] with w hw
  simp only [Ff, cutoff_eq_zero hw.le, zero_mul, mul_zero]

theorem Ff_fderiv_zero {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nf u) :
    fderiv ℝ (Ff r) u = 0 ∧ fderiv ℝ (fderiv ℝ (Ff r)) u = 0 := by
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (Ff_zero_nhds hu)
  refine ⟨h1.trans (fderiv_const_apply _), h2.trans ?_⟩
  rw [show (fderiv ℝ fun _ : SDEState (d + d + 1) => (0 : ℝ)) = fun _ => 0 from
    funext fun w => fderiv_const_apply _]
  exact fderiv_const_apply _

theorem Ff_pack_inside {r : ℝ} {x y : SDEState d} {a : ℝ} (h : ‖x‖ ^ 2 + ‖y‖ ^ 2 ≤ r) :
    Ff r (pack x y a) = Real.exp (-a) * ‖x - y‖ ^ 2 := by
  simp only [Ff, pack_iac]
  rw [Nf_pack, cutoff_eq_one h, one_mul, Qf_pack]

end M9c2


section M9d
/-! The generator of `Ff` along the coupled pair (x, y, a) and its sign inside the ball. -/

/-- Column `j` of a diffusion matrix. -/
noncomputable def scol (s : SDEDiffusion d) (j : Fin d) : SDEState d :=
  WithLp.toLp 2 (fun k => s (k, j))

/-- Drift of `Ff r (X, Y, A)` when `dX = σ₀(X) dW + b₀(X) dt`, `dY = σ₀(Y) dW + b₀(Y) dt`,
`dA = κ dt`, written with directional derivatives. -/
noncomputable def driftF (r κ : ℝ) (σ₀ : SDEState d → SDEDiffusion d)
    (b₀ : SDEState d → SDEState d) (x y : SDEState d) (a : ℝ) : ℝ :=
  fderiv ℝ (Ff r) (pack x y a) (pack (b₀ x) (b₀ y) κ) +
    (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ (Ff r)) (pack x y a)
      (pack (scol (σ₀ x) j) (scol (σ₀ y) j) 0) (pack (scol (σ₀ x) j) (scol (σ₀ y) j) 0)

theorem sum_scol_sq (s s' : SDEDiffusion d) :
    ∑ j, ∑ k, (scol s j k - scol s' j k) ^ 2 = ‖s - s'‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by simp [scol]

theorem driftF_inside {r κ : ℝ} (σ₀ : SDEState d → SDEDiffusion d)
    (b₀ : SDEState d → SDEState d) {x y : SDEState d} (a : ℝ)
    (h : ‖x‖ ^ 2 + ‖y‖ ^ 2 < r) :
    driftF r κ σ₀ b₀ x y a = Real.exp (-a) * (2 * ∑ k, (x k - y k) * (b₀ x k - b₀ y k) -
      κ * ‖x - y‖ ^ 2 + ‖σ₀ x - σ₀ y‖ ^ 2) := by
  have hN : Nf (pack x y a) < r := by rw [Nf_pack]; exact h
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (Ff_eq_F0f_nhds hN)
  unfold driftF
  rw [h1, h2, F0f_fderiv]
  rw [Finset.sum_congr rfl fun j _ => F0f_fderiv2 (pack x y a)
    (pack (scol (σ₀ x) j) (scol (σ₀ y) j) 0) (pack_iac _ _ _)]
  simp only [pack_ixc, pack_iyc, pack_iac, Qf_pack]
  simp only [← Finset.mul_sum]
  rw [sum_scol_sq]
  ring

/-- Inside the ball, with `κ ≥ 2L + L²` (`L` a Lipschitz constant there), the drift is `≤ 0`. -/
theorem driftF_nonpos_inside {r κ L : ℝ} (σ₀ : SDEState d → SDEDiffusion d)
    (b₀ : SDEState d → SDEState d) {x y : SDEState d} (a : ℝ)
    (h : ‖x‖ ^ 2 + ‖y‖ ^ 2 < r) (hL : 0 ≤ L) (hb : ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖)
    (hσ : ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖) (hκ : 2 * L + L ^ 2 ≤ κ) :
    driftF r κ σ₀ b₀ x y a ≤ 0 := by
  rw [driftF_inside σ₀ b₀ a h]
  refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
  have hin : ∑ k, (x k - y k) * (b₀ x k - b₀ y k) ≤ ‖x - y‖ * ‖b₀ x - b₀ y‖ := by
    have := real_inner_le_norm (x - y) (b₀ x - b₀ y)
    rw [PiLp.inner_apply] at this
    simpa [mul_comm] using this
  have hz := norm_nonneg (x - y)
  have h1 : ‖x - y‖ * ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hb hz]
  have h2 : ‖σ₀ x - σ₀ y‖ ^ 2 ≤ L ^ 2 * ‖x - y‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hσ 2
    nlinarith [this]
  nlinarith [sq_nonneg ‖x - y‖]

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

/-- A continuous function of `(x, y)` vanishing for `‖x‖² + ‖y‖² > r + 1` is bounded. -/
theorem bound_of_support {g : SDEState d × SDEState d → ℝ} (hg : Continuous g) (r : ℝ)
    (hz : ∀ x y : SDEState d, r + 1 < ‖x‖ ^ 2 + ‖y‖ ^ 2 → g (x, y) = 0) :
    ∃ B, 0 ≤ B ∧ ∀ x y, |g (x, y)| ≤ B := by
  set R' : ℝ := |r| + 2 with hR'
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : SDEState d) R' |>.prod
    (isCompact_closedBall (0 : SDEState d) R')).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x y => ?_⟩
  by_cases hin : (x, y) ∈ Metric.closedBall (0 : SDEState d) R' ×ˢ Metric.closedBall 0 R'
  · exact (Real.norm_eq_abs _ ▸ hB _ hin).trans (le_max_left _ _)
  · rw [hz x y ?_, abs_zero]
    · exact le_max_right _ _
    have hr : r + 1 < R' ^ 2 := by
      have := le_abs_self r; have := abs_nonneg r; nlinarith
    simp only [Set.mem_prod, Metric.mem_closedBall, dist_zero_right, not_and_or, not_le] at hin
    have hR0 : 0 ≤ R' := by rw [hR']; positivity
    rcases hin with h | h
    · have := pow_lt_pow_left₀ h hR0 two_ne_zero
      linarith [sq_nonneg ‖y‖]
    · have := pow_lt_pow_left₀ h hR0 two_ne_zero
      linarith [sq_nonneg ‖x‖]

/-- Integrand bound: `|DFf(x,y,a) w · c(x,y)| ≤ e^{-a} B` for continuous `c`. -/
theorem Ff_integrand_bound (r : ℝ) (w : SDEState (d + d + 1))
    {c : SDEState d × SDEState d → ℝ} (hc : Continuous c) :
    ∃ B, 0 ≤ B ∧ ∀ x y a, |fderiv ℝ (Ff r) (pack x y a) w * c (x, y)| ≤ Real.exp (-a) * B := by
  have hD1 : Continuous (fderiv ℝ (Ff (d := d) r)) :=
    (Ff_contDiff r (n := 2)).continuous_fderiv two_ne_zero
  have hgc : Continuous fun p : SDEState d × SDEState d =>
      fderiv ℝ (Ff r) (pack p.1 p.2 0) w * c p :=
    ((hD1.comp (pack_continuous continuous_fst continuous_snd continuous_const)).clm_apply
      continuous_const).mul hc
  obtain ⟨B, hB0, hB⟩ := bound_of_support hgc r fun x y hxy => by
    have := (Ff_fderiv_zero (u := pack x y 0) (by rw [Nf_pack]; exact hxy)).1
    simp [this]
  refine ⟨B, hB0, fun x y a => ?_⟩
  rw [(Ff_fderiv_pack r x y a).1, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_assoc,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hB x y) (Real.exp_pos _).le

/-- Generator bound: for `κ ≥ 0`, `driftF ≤ e^{-a} B` with `B` independent of `κ`. -/
theorem driftF_bound (r : ℝ) {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) :
    ∃ B, 0 ≤ B ∧ ∀ κ, 0 ≤ κ → ∀ x y a, driftF r κ σ₀ b₀ x y a ≤ Real.exp (-a) * B := by
  have hD1 : Continuous (fderiv ℝ (Ff (d := d) r)) :=
    (Ff_contDiff r (n := 2)).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (Ff (d := d) r))) :=
    ((Ff_contDiff r (n := 2)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  set g : SDEState d × SDEState d → ℝ := fun p => driftF r 0 σ₀ b₀ p.1 p.2 0 with hgdef
  have hpk := pack_continuous (d := d) continuous_fst continuous_snd
    (continuous_const (y := (0 : ℝ)))
  have hgc : Continuous g := by
    simp only [hgdef, driftF]
    refine ((hD1.comp hpk).clm_apply (pack_continuous (hb.comp continuous_fst)
      (hb.comp continuous_snd) continuous_const)).add (continuous_const.mul
      (continuous_finset_sum _ fun j _ => ?_))
    have hv := pack_continuous (scol_continuous (hσ.comp continuous_fst) j)
      (scol_continuous (hσ.comp continuous_snd) j) (continuous_const (y := (0 : ℝ)))
    exact ((hD2.comp hpk).clm_apply hv).clm_apply hv
  obtain ⟨B, hB0, hB⟩ := bound_of_support hgc r fun x y hxy => by
    obtain ⟨h1, h2⟩ := Ff_fderiv_zero (u := pack x y 0) (by rw [Nf_pack]; exact hxy)
    simp [hgdef, driftF, h1, h2]
  refine ⟨B, hB0, fun κ hκ x y a => ?_⟩
  have hscale : driftF r κ σ₀ b₀ x y a = Real.exp (-a) * driftF r κ σ₀ b₀ x y 0 := by
    obtain ⟨h1, h2⟩ := Ff_fderiv_pack r x y a
    simp only [driftF, h1, h2, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]; ring
  have hsplit : driftF r κ σ₀ b₀ x y 0 = g (x, y) - κ * Ff r (pack x y 0) := by
    have hv : pack (b₀ x) (b₀ y) κ = pack (b₀ x) (b₀ y) 0 + κ • (eac (d := d)) := by
      rw [pack_add_eac, zero_add]
    simp only [hgdef, driftF]
    rw [hv, map_add, map_smul, Ff_fderiv_eac, smul_eq_mul]
    ring
  rw [hscale, hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have := mul_nonneg hκ (Ff_nonneg r (pack x y 0))
  have := (le_abs_self (g (x, y))).trans (hB x y)
  linarith

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

/-- The completed Brownian past does not depend on a constant initial condition. -/
theorem completedBrownianPast_const [MeasurableSpace Ω] (P : Measure Ω)
    (W : ℝ≥0 → Ω → SDEState d) (x y : SDEState d) :
    completedBrownianPast P W (fun _ => x) = completedBrownianPast P W (fun _ => y) := by
  funext t
  simp only [completedBrownianPast, MeasurableSpace.comap_const]

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

/-- Localizing rate `c + M (dist(x, B_R) + dist(y, B_R))`. -/
noncomputable def kap (c M R : ℝ) (x y : SDEState d) : ℝ := c + M * (distB R x + distB R y)

theorem kap_continuous (c M R : ℝ) :
    Continuous fun p : SDEState d × SDEState d => kap c M R p.1 p.2 :=
  continuous_const.add (continuous_const.mul
    (((distB_continuous R).comp continuous_fst).add ((distB_continuous R).comp continuous_snd)))

theorem kap_comp_continuous (c M R : ℝ) {α : Type*} [TopologicalSpace α] {x y : α → SDEState d}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun v => kap c M R (x v) (y v) := by
  unfold kap
  exact continuous_const.add (continuous_const.mul
    (((distB_continuous R).comp hx).add ((distB_continuous R).comp hy)))

theorem kap_nonneg {c M R : ℝ} (hc : 0 ≤ c) (hM : 0 ≤ M) (x y : SDEState d) :
    0 ≤ kap c M R x y :=
  add_nonneg hc (mul_nonneg hM (add_nonneg (distB_nonneg R x) (distB_nonneg R y)))

theorem driftF_le_kap {r c R L B M : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hL : 0 ≤ L) (hc : 2 * L + L ^ 2 ≤ c) (hM : 0 < M)
    (hB : 0 ≤ B) (hr : r = 2 * (R + 1) ^ 2 + 1)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 1 → ‖y‖ ≤ R + 1 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    (hBd : ∀ κ, 0 ≤ κ → ∀ x y a, driftF r κ σ₀ b₀ x y a ≤ Real.exp (-a) * B)
    (x y : SDEState d) (a : ℝ) :
    driftF r (kap c M R x y) σ₀ b₀ x y a ≤ B * (1 / M) * (Real.exp (-a) * kap c M R x y) := by
  have hc0 : 0 ≤ c := by nlinarith
  have hk0 : 0 ≤ kap c M R x y := kap_nonneg hc0 hM.le x y
  have hea := Real.exp_pos (-a)
  by_cases hin : ‖x‖ ≤ R + 1 ∧ ‖y‖ ≤ R + 1
  · have hx2 := pow_le_pow_left₀ (norm_nonneg x) hin.1 2
    have hy2 := pow_le_pow_left₀ (norm_nonneg y) hin.2 2
    have hκ : 2 * L + L ^ 2 ≤ kap c M R x y := by
      unfold kap
      nlinarith [distB_nonneg R x, distB_nonneg R y]
    have h1 := driftF_nonpos_inside σ₀ b₀ a (r := r) (by rw [hr]; linarith) hL
      (hLip x y hin.1 hin.2).1 (hLip x y hin.1 hin.2).2 hκ
    exact h1.trans (by positivity)
  · have hd : 1 ≤ distB R x + distB R y := by
      rcases not_and_or.1 hin with h | h
      · have : 1 ≤ distB R x := le_max_of_le_right (by linarith)
        linarith [distB_nonneg R y]
      · have : 1 ≤ distB R y := le_max_of_le_right (by linarith)
        linarith [distB_nonneg R x]
    have hkM : M ≤ kap c M R x y := by unfold kap; nlinarith
    have h1 : 1 ≤ kap c M R x y / M := (one_le_div hM).2 hkM
    calc driftF r (kap c M R x y) σ₀ b₀ x y a ≤ Real.exp (-a) * B := hBd _ hk0 x y a
      _ ≤ Real.exp (-a) * B * (kap c M R x y / M) :=
          le_mul_of_one_le_right (by positivity) h1
      _ = B * (1 / M) * (Real.exp (-a) * kap c M R x y) := by ring

end M9e1


section M9e2
/-! Ito formula for `Ff r (X, Y, A)` and pathwise uniqueness for time-homogeneous, locally
Lipschitz coefficients (no stopping times: localization through the rate `kap`). -/

/-- Coefficient vector of the coupled process `(X, Y, A)` in Brownian direction `j`. -/
noncomputable def colU (σ₀ : SDEState d → SDEDiffusion d) (j : Fin d) (x y : SDEState d) :
    SDEState (d + d + 1) :=
  pack (scol (σ₀ x) j) (scol (σ₀ y) j) 0

theorem driftF_coords (r κ : ℝ) (σ₀ : SDEState d → SDEDiffusion d)
    (b₀ : SDEState d → SDEState d) (x y : SDEState d) (a : ℝ) :
    (∑ i, fderiv ℝ (Ff r) (pack x y a) (EuclideanSpace.single i 1) * pack (b₀ x) (b₀ y) κ i) +
      (1 / 2) * ∑ i, ∑ i', ∑ j, fderiv ℝ (fderiv ℝ (Ff r)) (pack x y a)
        (EuclideanSpace.single i 1) (EuclideanSpace.single i' 1) *
          colU σ₀ j x y i * colU σ₀ j x y i'
      = driftF r κ σ₀ b₀ x y a := by
  unfold driftF
  rw [clm_coord (fderiv ℝ (Ff r) (pack x y a)) (pack (b₀ x) (b₀ y) κ)]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · congr 1
    rw [Finset.sum_congr rfl fun j _ => clm2_coord (fderiv ℝ (fderiv ℝ (Ff r)) (pack x y a))
      (pack (scol (σ₀ x) j) (scol (σ₀ y) j) 0) (pack (scol (σ₀ x) j) (scol (σ₀ y) j) 0)]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [colU]
    ring

theorem driftF_continuous' (r : ℝ) {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hσ : Continuous σ₀) (hb : Continuous b₀)
    {α : Type*} [TopologicalSpace α] {κ a : α → ℝ} {x y : α → SDEState d}
    (hκ : Continuous κ) (hx : Continuous x) (hy : Continuous y) (ha : Continuous a) :
    Continuous fun p => driftF r (κ p) σ₀ b₀ (x p) (y p) (a p) := by
  have hD1 : Continuous (fderiv ℝ (Ff (d := d) r)) :=
    (Ff_contDiff r (n := 2)).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (Ff (d := d) r))) :=
    ((Ff_contDiff r (n := 2)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hpk := pack_continuous hx hy ha
  unfold driftF
  refine ((hD1.comp hpk).clm_apply (pack_continuous (hb.comp hx) (hb.comp hy) hκ)).add
    (continuous_const.mul (continuous_finsetSum _ fun j _ => ?_))
  have hv := pack_continuous (scol_continuous (hσ.comp hx) j) (scol_continuous (hσ.comp hy) j)
    (continuous_const (y := (0 : ℝ)))
  exact ((hD2.comp hpk).clm_apply hv).clm_apply hv

/-- Pathwise: the generator integral of the localized pair is at most `B / M`. -/
theorem drift_integral_le {r c R L B M : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hσ : Continuous σ₀) (hb : Continuous b₀)
    (hL : 0 ≤ L) (hc : 2 * L + L ^ 2 ≤ c) (hM : 0 < M) (hB : 0 ≤ B)
    (hr : r = 2 * (R + 1) ^ 2 + 1)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 1 → ‖y‖ ≤ R + 1 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    (hBd : ∀ κ, 0 ≤ κ → ∀ x y a, driftF r κ σ₀ b₀ x y a ≤ Real.exp (-a) * B)
    {x y : ℝ → SDEState d} (hx : Continuous x) (hy : Continuous y) (t : ℝ) (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, driftF r (kap c M R (x u) (y u)) σ₀ b₀ (x u) (y u)
        (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kap c M R (x v) (y v)) ≤ B * (1 / M) := by
  have hgc : Continuous fun v => kap c M R (x v) (y v) := kap_comp_continuous c M R hx hy
  have hpc : Continuous fun u => ∫ v in (0 : ℝ)..u, kap c M R (x v) (y v) :=
    continuous_iff_continuousAt.2 fun u => (hgc.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hcongr : ∫ u in (0 : ℝ)..t, driftF r (kap c M R (x u) (y u)) σ₀ b₀ (x u) (y u)
        (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kap c M R (x v) (y v)) =
      ∫ u in (0 : ℝ)..t, driftF r (kap c M R (x u) (y u)) σ₀ b₀ (x u) (y u)
        (∫ v in (0 : ℝ)..u, kap c M R (x v) (y v)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by rw [Set.uIcc_of_le ht] at hu; exact hu.1
    simp only [Real.coe_toNNReal _ hu0]
  rw [hcongr]
  have hLc : Continuous fun u => driftF r (kap c M R (x u) (y u)) σ₀ b₀ (x u) (y u)
      (∫ v in (0 : ℝ)..u, kap c M R (x v) (y v)) :=
    driftF_continuous' r hσ hb hgc hx hy hpc
  have hRc : Continuous fun u => B * (1 / M) *
      (Real.exp (-(∫ v in (0 : ℝ)..u, kap c M R (x v) (y v))) * kap c M R (x u) (y u)) :=
    continuous_const.mul ((Real.continuous_exp.comp hpc.neg).mul hgc)
  calc _ ≤ ∫ u in (0 : ℝ)..t, B * (1 / M) *
        (Real.exp (-(∫ v in (0 : ℝ)..u, kap c M R (x v) (y v))) * kap c M R (x u) (y u)) :=
        intervalIntegral.integral_mono_on ht (hLc.intervalIntegrable _ _)
          (hRc.intervalIntegrable _ _) fun u _ =>
          driftF_le_kap hL hc hM hB hr hLip hBd (x u) (y u) _
    _ = B * (1 / M) * (1 - Real.exp (-(∫ v in (0 : ℝ)..t, kap c M R (x v) (y v)))) := by
        rw [intervalIntegral.integral_const_mul, integral_exp_neg_primitive hgc]
    _ ≤ B * (1 / M) := by
        have h1 := Real.exp_pos (-(∫ v in (0 : ℝ)..t, kap c M R (x v) (y v)))
        have h2 : 0 ≤ B * (1 / M) := by positivity
        nlinarith

set_option maxHeartbeats 1000000 in
/-- Ito formula for `Ff r` along `(X, Y, A)`, `A = ∫ κ(X, Y)`: martingale part with mean zero
plus the generator integral. -/
theorem ito_coupled [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X Y : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {y₀ : SDEState d}
    (hY : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y₀) Y)
    {κ : SDEState d → SDEState d → ℝ}
    (hκ : Continuous fun p : SDEState d × SDEState d => κ p.1 p.2)
    (hκ0 : ∀ x y, 0 ≤ κ x y) (r : ℝ) (t : ℝ≥0) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧ ∫ ω, Z ω ∂P = 0 ∧
      ∀ᵐ ω ∂P, Ff r (pack (X t ω) (Y t ω)
          (∫ u in (0 : ℝ)..t.val, κ (X u.toNNReal ω) (Y u.toNNReal ω))) =
        Ff r (pack x₀ y₀ 0) + Z ω + ∫ u in (0 : ℝ)..t.val, driftF r (κ (X u.toNNReal ω) (Y u.toNNReal ω)) σ₀ b₀
          (X u.toNNReal ω) (Y u.toNNReal ω)
          (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), κ (X v.toNNReal ω) (Y v.toNNReal ω)) := by
  obtain ⟨hXm, hXc, hXa, hX0, JX, -, -, hJX, -, hXeq⟩ := hX
  obtain ⟨hYm, hYc, hYa, hY0, JY, -, -, hJY, -, hYeq⟩ := hY
  rw [completedBrownianPast_const P W y₀ x₀] at hYa hJY
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
      Continuous fun p : SDEState d × SDEState d => colU σ₀ j p.1 p.2 i := fun i j =>
    ((coord_contDiff i (n := 0)).continuous).comp
      (pack_continuous (scol_continuous (hσ.comp continuous_fst) j)
        (scol_continuous (hσ.comp continuous_snd) j) continuous_const)
  have hbf : ∀ i : Fin (d + d + 1), Continuous fun p : SDEState d × SDEState d =>
      pack (b₀ p.1) (b₀ p.2) (κ p.1 p.2) i := fun i =>
    ((coord_contDiff i (n := 0)).continuous).comp
      (pack_continuous (hb.comp continuous_fst) (hb.comp continuous_snd) hκ)
  let HU : Fin (d + d + 1) → Fin d → ℝ≥0 → Ω → ℝ := fun i j s ω => colU σ₀ j (X s ω) (Y s ω) i
  let JU : Fin (d + d + 1) → Fin d → ℝ≥0 → Ω → ℝ := fun i j s ω =>
    pack (WithLp.toLp 2 fun k => JX s ω (k, j)) (WithLp.toLp 2 fun k => JY s ω (k, j)) 0 i
  let bU : Fin (d + d + 1) → ℝ≥0 → Ω → ℝ := fun i s ω =>
    pack (b₀ (X s ω)) (b₀ (Y s ω)) (κ (X s ω) (Y s ω)) i
  have hHm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (HU i j s) :=
    fun i j s => (hcol i j).measurable.comp (hXYa s)
  have hHc : ∀ i j ω, Continuous fun s => HU i j s ω := fun i j ω => (hcol i j).comp (hXYc ω)
  have hbm : ∀ i s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (bU i s) :=
    fun i s => (hbf i).measurable.comp (hXYa s)
  have hbc : ∀ i ω, Continuous fun s => bU i s ω := fun i ω => (hbf i).comp (hXYc ω)
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
        have e1 : HU (Fin.castSucc (Fin.castAdd d k)) j = fun s ω => σ₀ (X s ω) (k, j) := by
          funext s ω; exact pack_ixc _ _ _ k
        have e2 : JU (Fin.castSucc (Fin.castAdd d k)) j = fun s ω => JX s ω (k, j) := by
          funext s ω; exact pack_ixc _ _ _ k
        rw [e1, e2]; exact hJX k j
      | right k =>
        have e1 : HU (Fin.castSucc (Fin.natAdd d k)) j = fun s ω => σ₀ (Y s ω) (k, j) := by
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
  have hD1c : Continuous (fderiv ℝ (Ff (d := d) r)) :=
    (Ff_contDiff r (n := 2)).continuous_fderiv two_ne_zero
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ (Ff (d := d) r))) :=
    ((Ff_contDiff r (n := 2)).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hKf : ∀ (i : Fin (d + d + 1)) (j : Fin d), Continuous fun q : SDEState d × SDEState d × ℝ =>
      fderiv ℝ (Ff r) (pack q.1 q.2.1 q.2.2) (EuclideanSpace.single i 1) *
        colU σ₀ j q.1 q.2.1 i := fun i j =>
    ((hD1c.comp hpk).clm_apply continuous_const).mul
      ((hcol i j).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
  have hKm : ∀ i j s, Measurable[completedBrownianPast P W (fun _ => x₀) s]
      (fun ω => fderiv ℝ (Ff r) (U s ω) (EuclideanSpace.single i 1) * HU i j s ω) :=
    fun i j s => (hKf i j).measurable.comp ((hXa s).prodMk ((hYa s).prodMk (hAa s)))
  have hKc : ∀ i j ω, Continuous
      (fun s => fderiv ℝ (Ff r) (U s ω) (EuclideanSpace.single i 1) * HU i j s ω) :=
    fun i j ω => (hKf i j).comp ((hXc ω).prodMk ((hYc ω).prodMk (hAc ω)))
  choose K hK using fun (i : Fin (d + d + 1)) (j : Fin d) =>
    exists_hasBrownianItoIntegral hW x₀ j (hKm i j) (hKc i j)
  have hito := ito_formula hW x₀ hUm hUc hUa hHm hHc hJ hbm hbc hUeq (Ff_contDiff r) hK t
  have hKb : ∀ i j, ∃ C, ∀ s ω,
      |fderiv ℝ (Ff r) (U s ω) (EuclideanSpace.single i 1) * HU i j s ω| ≤ C := fun i j => by
    obtain ⟨B, hB0, hB⟩ := Ff_integrand_bound r (EuclideanSpace.single i 1) (hcol i j)
    refine ⟨B, fun s ω => (hB (X s ω) (Y s ω) (A s ω)).trans ?_⟩
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 (hA0 s ω))
    exact mul_le_of_le_one_left hB0 this
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
    have hU0 : Ff r (U 0 ω) = Ff r (pack x₀ y₀ 0) := by
      show Ff r (pack (X 0 ω) (Y 0 ω) (A 0 ω)) = _
      rw [hx0, hy0]
      simp [A]
    show Ff r (U t ω) = Ff r (pack x₀ y₀ 0) + (∑ i, ∑ j, K i j t ω) + _
    rw [h, hU0, add_assoc]
    congr 1
    have hφ : Continuous fun u : ℝ => U u.toNNReal ω := (hUc ω).comp continuous_real_toNNReal
    have hF1c : ∀ i, Continuous fun u : ℝ =>
        fderiv ℝ (Ff r) (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω :=
      fun i => ((hD1c.comp hφ).clm_apply continuous_const).mul
        ((hbc i ω).comp continuous_real_toNNReal)
    have hF2c : ∀ i i' j, Continuous fun u : ℝ =>
        fderiv ℝ (fderiv ℝ (Ff r)) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω :=
      fun i i' j => ((((hD2c.comp hφ).clm_apply continuous_const).clm_apply
        continuous_const).mul ((hHc i j ω).comp continuous_real_toNNReal)).mul
        ((hHc i' j ω).comp continuous_real_toNNReal)
    have E1 : (∑ i, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (Ff r) (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω) =
        ∫ u in (0 : ℝ)..t.val, ∑ i,
          fderiv ℝ (Ff r) (U u.toNNReal ω) (EuclideanSpace.single i 1) * bU i u.toNNReal ω :=
      (intervalIntegral.integral_finsetSum fun i _ => (hF1c i).intervalIntegrable _ _).symm
    have E2 : (∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
        fderiv ℝ (fderiv ℝ (Ff r)) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω) =
        ∫ u in (0 : ℝ)..t.val, ∑ i, ∑ i', ∑ j,
        fderiv ℝ (fderiv ℝ (Ff r)) (U u.toNNReal ω) (EuclideanSpace.single i 1)
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
        fderiv ℝ (fderiv ℝ (Ff r)) (U u.toNNReal ω) (EuclideanSpace.single i 1)
          (EuclideanSpace.single i' 1) * HU i j u.toNNReal ω * HU i' j u.toNNReal ω)
        volume 0 t.val :=
      (continuous_const.mul (continuous_finsetSum Finset.univ fun i _ =>
        continuous_finsetSum Finset.univ fun i' _ => continuous_finsetSum Finset.univ
          fun j _ => hF2c i i' j)).intervalIntegrable _ _
    rw [E1, E2, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hI1 hI2]
    refine intervalIntegral.integral_congr fun u _ => ?_
    exact driftF_coords r _ σ₀ b₀ _ _ _

theorem Ff_pack_diag (r : ℝ) (x : SDEState d) (a : ℝ) : Ff r (pack x x a) = 0 := by
  simp [Ff, Qf_pack]

theorem measurable_Ff_coupled [MeasurableSpace Ω] {X Y : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hYm : ∀ s, Measurable (Y s))
    (hXc : ∀ ω, Continuous fun s => X s ω) (hYc : ∀ ω, Continuous fun s => Y s ω)
    {κ : SDEState d → SDEState d → ℝ}
    (hκ : Continuous fun p : SDEState d × SDEState d => κ p.1 p.2) (r : ℝ) (t : ℝ≥0) :
    Measurable fun ω => Ff r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, κ (X u.toNNReal ω) (Y u.toNNReal ω))) := by
  have hA : Measurable fun ω => ∫ u in (0 : ℝ)..t.val, κ (X u.toNNReal ω) (Y u.toNNReal ω) :=
    measurable_intervalIntegral_of_continuous _ t
    (fun s _ => hκ.measurable.comp ((hXm s).prodMk (hYm s)))
    (fun ω => hκ.comp ((hXc ω).prodMk (hYc ω)))
  exact (Ff_contDiff r (n := 0)).continuous.measurable.comp
    ((pack_continuous continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).measurable.comp
      ((hXm t).prodMk ((hYm t).prodMk hA)))

/-- Expectation bound: `E Ff(U_t) ≤ β` when the generator integral is pathwise `≤ β`. -/
theorem lintegral_Ff_le [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X Y : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {y₀ : SDEState d}
    (hY : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y₀) Y)
    {κ : SDEState d → SDEState d → ℝ}
    (hκ : Continuous fun p : SDEState d × SDEState d => κ p.1 p.2)
    (hκ0 : ∀ x y, 0 ≤ κ x y) (r : ℝ) (t : ℝ≥0) {β : ℝ}
    (hβ : ∀ ω, ∫ u in (0 : ℝ)..t.val, driftF r (κ (X u.toNNReal ω) (Y u.toNNReal ω)) σ₀ b₀
          (X u.toNNReal ω) (Y u.toNNReal ω)
          (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), κ (X v.toNNReal ω) (Y v.toNNReal ω)) ≤ β) :
    ∫⁻ ω, ENNReal.ofReal (Ff r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, κ (X u.toNNReal ω) (Y u.toNNReal ω)))) ∂P ≤
      ENNReal.ofReal (Ff r (pack x₀ y₀ 0) + β) := by
  obtain ⟨Z, hZi, hZ0, hZeq⟩ := ito_coupled hW x₀ hσ hb hX hY hκ hκ0 r t
  have hle : ∀ᵐ ω ∂P, Ff r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, κ (X u.toNNReal ω) (Y u.toNNReal ω))) ≤
        Z ω + (Ff r (pack x₀ y₀ 0) + β) := by
    filter_upwards [hZeq] with ω hω
    rw [hω]
    linarith [hβ ω]
  calc _ ≤ ∫⁻ ω, ENNReal.ofReal (Z ω + (Ff r (pack x₀ y₀ 0) + β)) ∂P :=
        lintegral_mono_ae (hle.mono fun ω h => ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal (∫ ω, (Z ω + (Ff r (pack x₀ y₀ 0) + β)) ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal (hZi.add (integrable_const _))
          (hle.mono fun ω h => (Ff_nonneg _ _).trans h)).symm
    _ = ENNReal.ofReal (Ff r (pack x₀ y₀ 0) + β) := by
        rw [integral_add hZi (integrable_const _), hZ0, integral_const]; simp

/-- Pathwise uniqueness on the event that both paths stay in the ball of radius `R`. -/
theorem pathwise_unique_R [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X Y : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    (hY : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) Y)
    {R L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y : SDEState d, ‖x‖ ≤ R + 1 → ‖y‖ ≤ R + 1 →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, (∀ u ≤ t, ‖X u ω‖ ≤ R ∧ ‖Y u ω‖ ≤ R) → X t ω = Y t ω := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * L + L ^ 2 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 2 * (R + 1) ^ 2 + 1 := ⟨_, rfl⟩
  obtain ⟨B, hB0, hBd⟩ := driftF_bound r hσ hb
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨hXm, hXc, -⟩ := id hX
  obtain ⟨hYm, hYc, -⟩ := id hY
  have hkc : ∀ M : ℝ, Continuous fun p : SDEState d × SDEState d => kap c M R p.1 p.2 :=
    fun M => kap_continuous c M R
  have key : ∀ M : ℕ, ∫⁻ ω, ENNReal.ofReal (Ff r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, kap c ((M : ℝ) + 1) R (X u.toNNReal ω) (Y u.toNNReal ω)))) ∂P ≤
      ENNReal.ofReal (B * (1 / ((M : ℝ) + 1))) := by
    intro M
    have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    have := lintegral_Ff_le hW x₀ hσ hb hX hY (hkc _) (kap_nonneg hc0 hM.le) r t fun ω =>
      drift_integral_le hσ hb hL hc.ge hM hB0 hr hLip hBd
        ((hXc ω).comp continuous_real_toNNReal) ((hYc ω).comp continuous_real_toNNReal)
        t.val t.2
    rwa [Ff_pack_diag, zero_add] at this
  let f : Ω → ℝ≥0∞ := fun ω => ⨅ M : ℕ, ENNReal.ofReal (Ff r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, kap c ((M : ℝ) + 1) R (X u.toNNReal ω) (Y u.toNNReal ω))))
  have hfm : Measurable f := Measurable.iInf fun M => ENNReal.measurable_ofReal.comp
    (measurable_Ff_coupled hXm hYm hXc hYc (hkc _) r t)
  have hf0 : ∫⁻ ω, f ω ∂P = 0 := by
    have ht : Tendsto (fun M : ℕ => ENNReal.ofReal (B * (1 / ((M : ℝ) + 1)))) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul B
    exact le_antisymm (ge_of_tendsto' ht fun M =>
      (lintegral_mono fun ω => iInf_le _ M).trans (key M)) zero_le
  have hfae := (lintegral_eq_zero_iff hfm).1 hf0
  filter_upwards [hfae] with ω hω hpath
  have hconst : ∀ M : ℕ, Ff r (pack (X t ω) (Y t ω)
      (∫ u in (0 : ℝ)..t.val, kap c ((M : ℝ) + 1) R (X u.toNNReal ω) (Y u.toNNReal ω))) =
      Real.exp (-(c * t.val)) * ‖X t ω - Y t ω‖ ^ 2 := by
    intro M
    have e : Set.EqOn (fun u : ℝ => kap c ((M : ℝ) + 1) R (X u.toNNReal ω) (Y u.toNNReal ω))
        (fun _ => c) (Set.uIcc 0 t.val) := fun u hu => by
      have hu' : u.toNNReal ≤ t := by
        rw [Set.uIcc_of_le t.2] at hu
        exact Real.toNNReal_le_iff_le_coe.2 hu.2
      obtain ⟨h1, h2⟩ := hpath _ hu'
      show kap c _ R _ _ = c
      rw [kap, distB_eq_zero h1, distB_eq_zero h2]
      ring
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, mul_comm, Ff_pack_inside]
    obtain ⟨h1, h2⟩ := hpath t le_rfl
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hR0 : 0 ≤ R := (norm_nonneg _).trans h1
    rw [hr]
    nlinarith
  have hfω : f ω = ENNReal.ofReal (Real.exp (-(c * t.val)) * ‖X t ω - Y t ω‖ ^ 2) := by
    simp only [f, hconst, iInf_const]
  have h0 : Real.exp (-(c * t.val)) * ‖X t ω - Y t ω‖ ^ 2 ≤ 0 := by
    have : f ω = 0 := hω
    rw [hfω] at this
    exact ENNReal.ofReal_eq_zero.1 this
  have hpos := Real.exp_pos (-(c * t.val))
  have hq : ‖X t ω - Y t ω‖ ^ 2 = 0 := by
    refine le_antisymm ?_ (by positivity)
    by_contra hne
    push Not at hne
    have := mul_pos hpos hne
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hq))

/-- Pathwise uniqueness for the SDE `dX = σ₀(X) dW + b₀(X) dt`, `X₀ = x₀`, with locally
Lipschitz coefficients. -/
theorem pathwise_unique [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀)
    (hLip : ∀ R : ℝ, ∃ L, 0 ≤ L ∧ ∀ x y : SDEState d, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    {X Y : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    (hY : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) Y)
    (t : ℝ≥0) : X t =ᵐ[P] Y t := by
  have h : ∀ R : ℕ, ∀ᵐ ω ∂P, (∀ u ≤ t, ‖X u ω‖ ≤ R ∧ ‖Y u ω‖ ≤ R) → X t ω = Y t ω :=
    fun R => by
      obtain ⟨L, hL, hLip'⟩ := hLip ((R : ℝ) + 1)
      exact pathwise_unique_R hW x₀ hσ hb hX hY hL hLip' t
  filter_upwards [ae_all_iff.2 h] with ω hω
  obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hX.2.1 ω).continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hY.2.1 ω).continuousOn
  obtain ⟨R, hR⟩ := exists_nat_ge (max C1 C2)
  exact hω R fun u hu => ⟨(hC1 u ⟨zero_le, hu⟩).trans ((le_max_left _ _).trans hR),
    (hC2 u ⟨zero_le, hu⟩).trans ((le_max_right _ _).trans hR)⟩

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

open StochKolmogorov.Persist

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

theorem pathwise_unique_all {Ω : Type*} {d : ℕ} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀)
    (hLip : ∀ R : ℝ, ∃ L, 0 ≤ L ∧ ∀ x y : SDEState d, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖b₀ x - b₀ y‖ ≤ L * ‖x - y‖ ∧ ‖σ₀ x - σ₀ y‖ ≤ L * ‖x - y‖)
    {X Y : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    (hY : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) Y) :
    ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω := by
  have h : ∀ q : ℚ, X (q : ℝ).toNNReal =ᵐ[P] Y (q : ℝ).toNNReal := fun q =>
    pathwise_unique hW x₀ hσ hb hLip hX hY _
  filter_upwards [ae_all_iff.2 h] with ω hω
  have := Continuous.ext_on denseRange_rat_toNNReal (hX.2.1 ω) (hY.2.1 ω)
    (by rintro _ ⟨q, rfl⟩; exact hω q)
  exact fun t => congrFun this t

open StochKolmogorov.Persist

theorem kolm_lip_balls {n : ℕ} (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ∀ R : ℝ, ∃ L, 0 ≤ L ∧ ∀ x y : SDEState n, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖drift C (0, x) - drift C (0, y)‖ ≤ L * ‖x - y‖ ∧
      ‖diffusion C (0, x) - diffusion C (0, y)‖ ≤ L * ‖x - y‖ := by
  obtain ⟨-, -, s₁, b₁, S, L, -, -, hL, -, hLg, hag⟩ := kolm_trunc C hC
  intro R
  obtain ⟨N, hN⟩ := exists_nat_ge R
  refine ⟨L N, hL N, fun x y hx hy => ?_⟩
  obtain ⟨h1, h2⟩ := hag N x (by linarith)
  obtain ⟨h3, h4⟩ := hag N y (by linarith)
  rw [← h1, ← h2, ← h3, ← h4]
  exact ⟨(hLg N x y).2, (hLg N x y).1⟩

/-- lemma_3_1 clause 2: pathwise uniqueness for the Kolmogorov system. -/
theorem kolm_unique {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ∀ x ∈ orthant n, ∀ Y Y' : ℝ≥0 → Ω → SDEState n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y →
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y' →
      ∀ᵐ ω ∂P, ∀ t, Y t ω = Y' t ω := by
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  intro x _ Y Y' hY hY'
  exact pathwise_unique_all hB x hσc hbc (kolm_lip_balls C hC) hY hY'

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

end QEneg

section QEF

end QEF

section QEface
open StochKolmogorov.Persist
variable {n : ℕ}

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
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ∀ x ∈ orthant n, ∀ Y Y' : ℝ≥0 → Ω → SDEState n,
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y →
      SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y' →
      ∀ᵐ ω ∂P, ∀ t, Y t ω = Y' t ω := by
  exact ItoLib.kolm_unique P C B hB hC
