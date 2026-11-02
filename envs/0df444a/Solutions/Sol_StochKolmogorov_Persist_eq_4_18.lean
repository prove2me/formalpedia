-- Prove2me | solution 1 for StochKolmogorov.Persist.eq_4_18
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T21:28:47.903822+00:00
-- url     : https://prove2.me/submissions/e78682e6-3759-49a7-a532-15c28cd9f455

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
import Definitions.Def_TotalVariationDist
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_lyapunov_moment_bound
import Theorems.Thm_EthierKurtz_sde_markov_property_lipschitz
import Theorems.Thm_StochKolmogorov_Persist_orthant_invariance_closed
import Theorems.Thm_EthierKurtz_sde_markov_property_lipschitz_weighted
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_feynman_kac_bound

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

end M8g4

section M8g5
variable [MeasurableSpace Ω]

end M8g5

section M9a
variable [MeasurableSpace Ω]

end M9a


section M9c
/-! M9c: calculus for the pathwise-uniqueness test function (line derivatives, cutoff). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end M9c

section M9cF
/-! The concrete test function on `SDEState (d + d + 1)` = (x, y, a). -/

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
    nlinarith

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

/-- `lemma_3_1` clause 3: faces `ℝ^{I,◦}₊` are invariant for all times, almost surely. -/
theorem face_inv {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (C : Coeffs n) {B : ℝ≥0 → Ω → SDEState n} (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {I : Finset (Fin n)} {x : SDEState n} (hx : x ∈ faceOpen I) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) :
    ∀ᵐ ω ∂P, ∀ t, Y t ω ∈ faceOpen I := by
  exact StochKolmogorov.Persist.kolmogorov_sde_face_invariance C hB hC hx hY
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

theorem openOrthant_sub {y : SDEState n} (hy : y ∈ openOrthant n) : y ∈ orthant n :=
  fun i => (hy i).le

end QFell

section QFalg
variable {n : ℕ}
open StochKolmogorov.Persist

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

/-- (3.6): `E V^δ₀(Y_t) ≤ e^{δ₀ H t} V^δ₀(x)` for `x` in the open orthant. -/
theorem moment_36 (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B) {c p : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) {x : SDEState n} (hx : x ∈ openOrthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) ∂P ≤
      ENNReal.ofReal (Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c p x ^ δ₀) := by
  exact StochKolmogorov.Persist.kolmogorov_lyapunov_moment_bound hn hB hA hδ hp hpl hx hY t
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
-- ===== FK =====
section FlatM_FK
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false

namespace ItoLib
open EthierKurtz

section FKa
/-! a4101326 S4a: the time-slot test function `F(x,y,a) = e^{ψ(x_{i0}) - a} G(y)`. -/
variable {d : ℕ}

end FKa

section FKb
/-! a4101326 S4b: saturation clock and the generator inequality for `e^{γbθ s - a} G_m`. -/
variable {n : ℕ}
open StochKolmogorov.Persist

noncomputable def Rf (C : Coeffs n) (c : SDEState n) (γb : ℝ) (z : SDEState n) : ℝ :=
  cBracket C c z + γb * (1 + ∑ i, (|C.f i z| + C.g i z ^ 2))

end FKb

end ItoLib

end FlatM_FK
-- ===== FK2 =====
section FlatM_FK2
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false

namespace ItoLib
open EthierKurtz

section FKc
/-! a4101326 S4c: the Feynman-Kac bound at a fixed saturation level `m`. -/
variable {n : ℕ}
open StochKolmogorov.Persist

theorem continuous_primitive_nn {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous fun s : ℝ≥0 => ∫ v in (0 : ℝ)..(s : ℝ), g v :=
  (intervalIntegral.continuous_primitive (fun a b => hg.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

set_option maxHeartbeats 2000000 in
/-- Feynman-Kac bound for `W = V^θ` with killing clock `κ`:
`E[e^{γbθ t - A_t} W(Y_t) + λ ∫₀ᵗ κ(Y_u) e^{γbθ u - A_u} W(Y_u) du] ≤ W(x)`, `A = ∫ κ(Y)`. -/
theorem fk (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B) {c p : SDEState n} {γb δ₀ θ lam : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (hθ : 0 < θ) (hθδ : θ ≤ δ₀) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ 1) {κ : SDEState n → ℝ} (hκc : Continuous κ) (hκ0 : ∀ z, 0 ≤ κ z) {N : ℝ}
    (hκN : ∀ z, κ z ≤ N)
    (hκR : ∀ z ∈ openOrthant n, 0 < Rf C c γb z →
      θ * (Hconst C c γb δ₀ + γb) ≤ (1 - lam) * κ z)
    {x : SDEState n} (hx : x ∈ openOrthant n) {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) :
    ∫⁻ ω, (ENNReal.ofReal (Real.exp (γb * θ * t - ∫ v in (0 : ℝ)..(t : ℝ), κ (Y v.toNNReal ω)) *
        Vfun c p (Y t ω) ^ θ) +
      ENNReal.ofReal (∫ u in (0 : ℝ)..(t : ℝ), lam * (κ (Y u.toNNReal ω) *
        (Real.exp (γb * θ * (u.toNNReal : ℝ) - ∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ),
          κ (Y v.toNNReal ω)) * Vfun c p (Y u.toNNReal ω) ^ θ)))) ∂P ≤
      ENNReal.ofReal (Vfun c p x ^ θ) := by
  exact StochKolmogorov.Persist.kolmogorov_feynman_kac_bound hn hB hA hδ hp hpl hθ hθδ hlam0 hlam hκc hκ0 hκN hκR hx hY t
end FKc

end ItoLib

end FlatM_FK2
-- ===== WM =====
section FlatM_WM
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section WM1
/-! a4101326 S1: weighted Euler restart.  A bounded weight `Z` measurable for the completed
Brownian past at the restart time `m h` passes through the restart identity. -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}

variable [MeasurableSpace Ω] {P : Measure Ω}

end WM1

section WM2
variable [MeasurableSpace Ω] {P : Measure Ω}

theorem markov_core_w [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d}
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
      ∀ x ∈ D, ∀ s : ℝ≥0, 0 < s → (∀ᵐ ω ∂P, X x s ω ∈ D) → ∀ Zw : Ω → ℝ,
        Measurable[completedBrownianPast P W (fun _ => x) s] Zw → Measurable Zw →
        (∀ ω, |Zw ω| ≤ 1) →
        ∫ ω, Zw ω * f (X x (s + t) ω) ∂P = ∫ ω, Zw ω * g (X x s ω) ∂P := by
  exact EthierKurtz.sde_markov_property_lipschitz_weighted hW hσ hb s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX t hf hfK hLf hfL
end WM2

end ItoLib

end FlatM_WM
-- ===== WM2 =====
section FlatM_WM2
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section WM3
/-! a4101326 S2: weighted Chapman-Kolmogorov for measurable `F ≥ 0`, from the weighted identity
for thickened indicators (bounded Lipschitz test functions). -/

variable [MeasurableSpace Ω] {P : Measure Ω}

theorem markov_w [IsProbabilityMeasure P] {D : Set (SDEState d)}
    {X : SDEState d → ℝ≥0 → Ω → SDEState d} (hXm : ∀ y ∈ D, ∀ t, Measurable (X y t)) (t : ℝ≥0)
    (G : SDEState d → ℝ≥0 → MeasurableSpace Ω)
    (κ : Kernel (SDEState d) (SDEState d)) [IsMarkovKernel κ] (hκ : ∀ y ∈ D, κ y = P.map (X y t))
    (Hc : ∀ (F : Set (SDEState d)), IsClosed F → ∀ n : ℕ, ∃ g : SDEState d → ℝ, Measurable g ∧
      (∀ y ∈ D, g y = ∫ ω, (thickenedIndicator (Nat.one_div_pos_of_nat (n := n)) F (X y t ω) : ℝ) ∂P) ∧
      ∀ x ∈ D, ∀ s : ℝ≥0, 0 < s → (∀ᵐ ω ∂P, X x s ω ∈ D) → ∀ Zw : Ω → ℝ,
        Measurable[G x s] Zw → Measurable Zw → (∀ ω, |Zw ω| ≤ 1) →
        ∫ ω, Zw ω * (thickenedIndicator (Nat.one_div_pos_of_nat (n := n)) F (X x (s + t) ω) : ℝ) ∂P =
          ∫ ω, Zw ω * g (X x s ω) ∂P)
    (x : SDEState d) (hx : x ∈ D) (s : ℝ≥0) (hs : 0 < s) (hD : ∀ᵐ ω ∂P, X x s ω ∈ D)
    (Zw : Ω → ℝ) (hZm : Measurable[G x s] Zw) (hZa : Measurable Zw) (hZ0 : ∀ ω, 0 ≤ Zw ω)
    (hZ1 : ∀ ω, Zw ω ≤ 1) {F : SDEState d → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, ENNReal.ofReal (Zw ω) * F (X x (s + t) ω) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Zw ω) * ∫⁻ y, F y ∂(κ (X x s ω)) ∂P := by
  have hZK : ∀ ω, |Zw ω| ≤ 1 := fun ω => by rw [abs_of_nonneg (hZ0 ω)]; exact hZ1 ω
  have hz : Measurable fun ω => ENNReal.ofReal (Zw ω) := hZa.ennreal_ofReal
  have hXs := hXm x hx s
  have hXst := hXm x hx (s + t)
  set Pz := P.withDensity (fun ω => ENNReal.ofReal (Zw ω)) with hPz
  haveI : IsFiniteMeasure Pz := by
    refine ⟨?_⟩
    rw [hPz, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    calc ∫⁻ ω, ENNReal.ofReal (Zw ω) ∂P ≤ ∫⁻ _ω, 1 ∂P :=
          lintegral_mono fun ω => ENNReal.ofReal_le_one.2 (hZ1 ω)
      _ < ⊤ := by simp
  have k1 : ∀ {H : SDEState d → ℝ≥0∞}, Measurable H →
      ∫⁻ y, H y ∂(Pz.map (X x (s + t))) =
        ∫⁻ ω, ENNReal.ofReal (Zw ω) * H (X x (s + t) ω) ∂P := by
    intro H hH
    rw [lintegral_map hH hXst, hPz]
    exact lintegral_withDensity_eq_lintegral_mul _ hz (hH.comp hXst)
  have k2 : ∀ {H : SDEState d → ℝ≥0∞}, Measurable H →
      ∫⁻ y, H y ∂((Pz.map (X x s)).bind κ) =
        ∫⁻ ω, ENNReal.ofReal (Zw ω) * ∫⁻ y, H y ∂(κ (X x s ω)) ∂P := by
    intro H hH
    have hm : Measurable fun y => ∫⁻ z, H z ∂(κ y) :=
      (Measure.measurable_lintegral hH).comp κ.measurable
    rw [Measure.lintegral_bind κ.measurable.aemeasurable hH.aemeasurable, lintegral_map hm hXs,
      hPz]
    exact lintegral_withDensity_eq_lintegral_mul _ hz (hm.comp hXs)
  rw [← k1 hF, ← k2 hF]
  congr 1
  have hgen : (inferInstance : MeasurableSpace (SDEState d)) =
      MeasurableSpace.generateFrom {s | IsClosed s} :=
    (BorelSpace.measurable_eq (α := SDEState d)).trans borel_eq_generateFrom_isClosed
  have huniv : Pz.map (X x (s + t)) Set.univ = (Pz.map (X x s)).bind κ Set.univ := by
    rw [← lintegral_one, ← lintegral_one, k1 (H := fun _ => (1 : ℝ≥0∞)) measurable_const,
      k2 (H := fun _ => (1 : ℝ≥0∞)) measurable_const]
    simp [lintegral_one]
  refine ext_of_generate_finite _ hgen isPiSystem_isClosed (fun F' hF' => ?_) huniv
  haveI : IsFiniteMeasure ((Pz.map (X x s)).bind κ) :=
    ⟨by rw [← huniv]; exact measure_lt_top _ _⟩
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 := tendsto_lintegral_thickenedIndicator_of_isClosed (Pz.map (X x (s + t))) hF'
    (fun n => Nat.one_div_pos_of_nat) hδ
  have h2 := tendsto_lintegral_thickenedIndicator_of_isClosed ((Pz.map (X x s)).bind κ) hF'
    (fun n => Nat.one_div_pos_of_nat) hδ
  refine tendsto_nhds_unique h1 (h2.congr fun n => ?_)
  obtain ⟨g, hgm, hgD, hgck⟩ := Hc F' hF' n
  obtain ⟨hm, hb, -⟩ := thick_props (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F'
  have hmE : Measurable fun y =>
      (thickenedIndicator (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F' y : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp (thickenedIndicator _ F').continuous).measurable
  rw [k1 hmE, k2 hmE]
  have hgnn : ∀ y ∈ D, 0 ≤ g y := fun y hy => by
    rw [hgD y hy]; exact integral_nonneg fun ω => NNReal.coe_nonneg _
  have hgb : ∀ y ∈ D, |g y| ≤ 1 := fun y hy => by
    rw [hgD y hy, abs_of_nonneg (integral_nonneg fun ω => NNReal.coe_nonneg _)]
    refine (integral_mono_of_nonneg (ae_of_all _ fun ω => NNReal.coe_nonneg _)
      (integrable_const (1 : ℝ)) (ae_of_all _ fun ω => ?_)).trans (by simp)
    exact (le_abs_self _).trans (hb _)
  have eL : ∫⁻ ω, ENNReal.ofReal (Zw ω) *
      (thickenedIndicator (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F' (X x (s + t) ω) : ℝ≥0∞) ∂P
      = ENNReal.ofReal (∫ ω, Zw ω *
        (thickenedIndicator (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F' (X x (s + t) ω) : ℝ) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (f := fun ω => Zw ω *
        (thickenedIndicator (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F' (X x (s + t) ω) : ℝ))
      (memLp_one_iff_integrable.1 (MemLp.of_bound (hZa.mul (hm.comp hXst)).aestronglyMeasurable 1
        (ae_of_all _ fun ω => by
          simp only [Real.norm_eq_abs, abs_mul]
          exact mul_le_one₀ (hZK ω) (abs_nonneg _) (hb _))))
      (ae_of_all _ fun ω => mul_nonneg (hZ0 ω) (NNReal.coe_nonneg _))]
    congr 1; funext ω
    rw [ENNReal.ofReal_mul (hZ0 ω), ENNReal.ofReal_coe_nnreal]
  have eR : ∫⁻ ω, ENNReal.ofReal (Zw ω) * ∫⁻ y,
      (thickenedIndicator (Nat.one_div_pos_of_nat (n := n) (α := ℝ)) F' y : ℝ≥0∞) ∂(κ (X x s ω)) ∂P
      = ENNReal.ofReal (∫ ω, Zw ω * g (X x s ω) ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (f := fun ω => Zw ω * g (X x s ω))
      (memLp_one_iff_integrable.1 (MemLp.of_bound (hZa.mul (hgm.comp hXs)).aestronglyMeasurable 1
        (hD.mono fun ω hω => by
          simp only [Real.norm_eq_abs, abs_mul]
          exact mul_le_one₀ (hZK ω) (abs_nonneg _) (hgb _ hω))))
      (hD.mono fun ω hω => mul_nonneg (hZ0 ω) (hgnn _ hω))]
    refine lintegral_congr_ae (hD.mono fun ω hω => ?_)
    show ENNReal.ofReal (Zw ω) * _ = ENNReal.ofReal (Zw ω * g (X x s ω))
    rw [ENNReal.ofReal_mul (hZ0 ω), hκ _ hω, lint_thick _ _ (hXm _ hω t), hgD _ hω]
  rw [eR, eL, hgck x hx s hs hD Zw hZm hZa hZK]

end WM3

end ItoLib

end FlatM_WM2
-- ===== HA =====
section FlatM_HA
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

end FlatM_HA
-- ===== HB =====
section FlatM_HB
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

end FlatM_HB
-- ===== TA =====
section FlatM_TA
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section TA
/-! TA (s31): universe-polymorphic Markov statement (Ω : Type*), for the theorem_1_1 glue. -/
open StochKolmogorov.Persist
variable {n : ℕ}

/-- b10: solutions started in the closed orthant stay there almost surely. -/
theorem orthant_inv' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ∀ x ∈ orthant n, ∀ t : ℝ≥0, ∀ᵐ ω ∂P, X x t ω ∈ orthant n := by
  obtain ⟨hP, hB, hX⟩ := hfam
  haveI := hP
  intro x₀ hx₀ t
  exact orthant_inv1 P C B hB hC hx₀ (hX x₀ hx₀) t
end TA

end ItoLib

end FlatM_TA
-- ===== WM3 =====
section FlatM_WM3
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section WM4
/-! a4101326 S3: weighted Markov property of the Kolmogorov solution family. -/

variable {n : ℕ}

theorem kolm_markov_w {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (t : ℝ≥0) :
    ∃ κ : Kernel (SDEState n) (SDEState n), IsMarkovKernel κ ∧
      (∀ x ∈ orthant n, κ x = trans P X t x) ∧
      ∀ x ∈ orthant n, ∀ s : ℝ≥0, 0 < s → ∀ Zw : Ω → ℝ,
        Measurable[completedBrownianPast P B (fun _ => x) s] Zw → Measurable Zw →
        (∀ ω, 0 ≤ Zw ω) → (∀ ω, Zw ω ≤ 1) → ∀ F : SDEState n → ℝ≥0∞, Measurable F →
        ∫⁻ ω, ENNReal.ofReal (Zw ω) * F (X x (s + t) ω) ∂P =
          ∫⁻ ω, ENNReal.ofReal (Zw ω) * ∫⁻ y, F y ∂(κ (X x s ω)) ∂P := by
  have hinv := orthant_inv' P C B X hfam hA.2.1
  obtain ⟨hP, hB, hX⟩ := hfam
  obtain ⟨hσc, hbc, s₁, b₁, S, L, hs₁, hb₁, hL, hSg, hLg, hag⟩ := kolm_trunc C hA.2.1
  have hXm : ∀ y ∈ orthant n, ∀ t, Measurable (X y t) := fun y hy t => (hX y hy).1 t
  have hX' : ∀ y ∈ orthant n, SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => y) (X y) := fun y hy => hX y hy
  obtain ⟨κ, hκM, hκx, -⟩ := markov_of_core orthant_isClosed.measurableSet hXm t fun F _ m => by
    obtain ⟨hm, hb, hl⟩ := thick_props (Nat.one_div_pos_of_nat (n := m)) F
    obtain ⟨g, hg, -, hg1, hg2⟩ := markov_core hB hσc hbc s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX' t
      hm hb (inv_nonneg.2 (Nat.one_div_pos_of_nat (n := m)).le) hl
    exact ⟨g, hg, hg1, hg2⟩
  refine ⟨κ, hκM, hκx, fun x hx s hs Zw hZm hZa hZ0 hZ1 F hF => ?_⟩
  haveI := hκM
  refine markov_w hXm t (fun x s => completedBrownianPast P B (fun _ => x) s) κ hκx
    (fun F' _ m => ?_) x hx s hs (hinv x hx s) Zw hZm hZa hZ0 hZ1 hF
  obtain ⟨hm, hb, hl⟩ := thick_props (Nat.one_div_pos_of_nat (n := m)) F'
  obtain ⟨g, hg, -, hg1, hg2⟩ := markov_core_w hB hσc hbc s₁ b₁ S L hs₁ hb₁ hL hSg hLg hag hX' t
    hm hb (inv_nonneg.2 (Nat.one_div_pos_of_nat (n := m)).le) hl
  exact ⟨g, hg, hg1, hg2⟩

end WM4

end ItoLib

end FlatM_WM3
-- ===== FIN =====
section FlatM_FIN
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false
set_option linter.all false

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

section FINa
/-! a4101326 S5a: clock, Jensen moment bound, one-step bound. -/
variable {n : ℕ}

theorem fin_coord_cont (i : Fin n) : Continuous fun x : SDEState n => x i :=
  (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)

theorem fin_Vfun_meas (c p : SDEState n) (θ : ℝ) : Measurable fun x => Vfun c p x ^ θ := by
  unfold Vfun
  refine Measurable.pow_const (Measurable.div ?_ ?_) θ
  · exact measurable_const.add
      (Finset.measurable_sum _ fun i _ => measurable_const.mul (fin_coord_cont i).measurable)
  · exact Finset.measurable_prod _ fun i _ => (fin_coord_cont i).measurable.pow_const (p i)

theorem fin_Vfun_pos {c p x : SDEState n} (hc : c ∈ openOrthant n) (hx : x ∈ openOrthant n) :
    0 < Vfun c p x := by
  unfold Vfun
  have : 0 ≤ ∑ i, c i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hx i).le
  exact div_pos (by linarith) (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _)

theorem fin_Rf_contOn (C : Coeffs n) {c : SDEState n} (γb : ℝ) (hc : c ∈ openOrthant n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    ContinuousOn (Rf C c γb) (orthant n) := by
  have hx : ∀ i : Fin n, ContinuousOn (fun x : SDEState n => x i) (orthant n) :=
    fun i => (fin_coord_cont i).continuousOn
  have hf : ∀ i, ContinuousOn (C.f i) (orthant n) := fun i => (hC i).1.continuousOn
  have hg : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  have hS : ContinuousOn (fun x : SDEState n => 1 + ∑ i, c i * x i) (orthant n) :=
    continuousOn_const.add (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul (hx i))
  have hS0 : ∀ x ∈ orthant n, (1 + ∑ i, c i * x i) ≠ 0 := fun x hx' => by
    have : 0 ≤ ∑ i, c i * x i := Finset.sum_nonneg fun i _ => mul_nonneg (hc i).le (hx' i)
    exact ne_of_gt (by linarith)
  unfold Rf cBracket
  refine ContinuousOn.add (ContinuousOn.sub ?_ ?_) ?_
  · exact (continuousOn_finset_sum _ fun i _ =>
      (continuousOn_const.mul (hx i)).mul (hf i)).div hS hS0
  · refine (continuousOn_const.mul (continuousOn_finset_sum _ fun i _ =>
      continuousOn_finset_sum _ fun j _ => ?_)).div (hS.pow 2)
      fun x hx' => pow_ne_zero 2 (hS0 x hx')
    exact ((((continuousOn_const.mul (hx i)).mul (hx j)).mul (hg i)).mul (hg j))
  · exact continuousOn_const.mul (continuousOn_const.add
      (continuousOn_finset_sum _ fun i _ => (hf i).abs.add ((hg i).pow 2)))

theorem fin_clock (C : Coeffs n) {c : SDEState n} {γb M N : ℝ} (hc : c ∈ openOrthant n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hM : IsRadiusM C c γb M) (hN : 0 ≤ N) :
    ∃ κ : SDEState n → ℝ, Continuous κ ∧ (∀ z, 0 ≤ κ z) ∧ (∀ z, κ z ≤ N) ∧
      (∀ z, 0 < κ z → l1 z < M) ∧ (∀ z ∈ openOrthant n, 0 < Rf C c γb z → κ z = N) := by
  have hl1 : Continuous (fun z : SDEState n => l1 z) :=
    continuous_finset_sum _ fun i _ => (fin_coord_cont i).abs
  have horth : IsClosed (orthant n) := by
    have : orthant n = ⋂ i, {x : SDEState n | 0 ≤ x i} := by ext x; simp [orthant]
    rw [this]; exact isClosed_iInter fun i => isClosed_le continuous_const (fin_coord_cont i)
  have hs : IsClosed {z : SDEState n | M ≤ l1 z} := isClosed_le continuous_const hl1
  have ht : IsClosed (orthant n ∩ {z | l1 z ≤ M} ∩ Rf C c γb ⁻¹' Ici 0) :=
    ((fin_Rf_contOn C γb hc hC).mono inter_subset_left).preimage_isClosed_of_isClosed
      (horth.inter (isClosed_le hl1 continuous_const)) isClosed_Ici
  have hd : Disjoint {z : SDEState n | M ≤ l1 z}
      (orthant n ∩ {z | l1 z ≤ M} ∩ Rf C c γb ⁻¹' Ici 0) := by
    rw [Set.disjoint_left]
    rintro z hz ⟨⟨hzo, -⟩, hzR⟩
    have h1 := hM z hzo hz
    have h2 : 0 ≤ Rf C c γb z := hzR
    unfold Rf at h2
    linarith
  obtain ⟨f, hf0, hf1, hfI⟩ := exists_continuous_zero_one_of_isClosed hs ht hd
  refine ⟨fun z => N * f z, continuous_const.mul f.continuous, fun z => mul_nonneg hN (hfI z).1,
    fun z => mul_le_of_le_one_right hN (hfI z).2, fun z hz => ?_, fun z hz hR => ?_⟩
  · by_contra h
    have h0 : f z = 0 := by simpa using hf0 (show z ∈ {z : SDEState n | M ≤ l1 z} from not_lt.1 h)
    simp only [h0, mul_zero, lt_irrefl] at hz
  · have hlt : l1 z < M := by
      by_contra h
      have h1 := hM z (openOrthant_sub hz) (not_lt.1 h)
      unfold Rf at hR; linarith
    have h1 : f z = 1 := by
      simpa using hf1 (show z ∈ orthant n ∩ {z | l1 z ≤ M} ∩ Rf C c γb ⁻¹' Ici 0 from
        ⟨⟨openOrthant_sub hz, hlt.le⟩, show (0 : ℝ) ≤ Rf C c γb z from hR.le⟩)
    simp only [h1, mul_one]

/-- Jensen + (3.6): `E V^θ(Y_t) ≤ e^{θ H t} V^θ(x)` for `θ ≤ δ₀`. -/
theorem fin_jensen (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n}
    (hB : IsStandardBrownian P B) {c p : SDEState n} {γb δ₀ θ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (hθ : 0 < θ) (hθδ : θ ≤ δ₀) {x : SDEState n} (hx : x ∈ openOrthant n)
    {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ θ) ∂P ≤
      ENNReal.ofReal (Real.exp (θ * Hconst C c γb δ₀ * t) * Vfun c p x ^ θ) := by
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hδ0 : 0 < δ₀ := hδ.1
  have hm := moment_36 hn hB hA hδ hp hpl hx hY t
  set q : ℝ := θ / δ₀ with hq
  have hq0 : 0 < q := div_pos hθ hδ0
  have hq1 : q ≤ 1 := (div_le_one hδ0).2 hθδ
  set Bd : ℝ := Real.exp (δ₀ * Hconst C c γb δ₀ * t) * Vfun c p x ^ δ₀ with hBd
  have hBd0 : 0 < Bd := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (fin_Vfun_pos hc hx) _)
  set K1 : ℝ := q * Bd ^ (q - 1) with hK1
  set K0 : ℝ := (1 - q) * Bd with hK0'
  have hK1n : 0 ≤ K1 := mul_nonneg hq0.le (Real.rpow_pos_of_pos hBd0 _).le
  have hK0n : 0 ≤ K0 * Bd ^ (q - 1) :=
    mul_nonneg (mul_nonneg (sub_nonneg.2 hq1) hBd0.le) (Real.rpow_pos_of_pos hBd0 _).le
  have hpt : ∀ a : ℝ, 0 ≤ a → a ^ q ≤ K1 * a + K0 * Bd ^ (q - 1) := by
    intro a ha
    have h := Real.geom_mean_le_arith_mean2_weighted hq0.le (sub_nonneg.2 hq1) ha hBd0.le
      (by ring : q + (1 - q) = 1)
    have e1 : Bd ^ (1 - q) * Bd ^ (q - 1) = 1 := by
      rw [← Real.rpow_add hBd0]; simp
    have hB1 : 0 ≤ Bd ^ (q - 1) := (Real.rpow_pos_of_pos hBd0 _).le
    calc a ^ q = a ^ q * Bd ^ (1 - q) * Bd ^ (q - 1) := by rw [mul_assoc, e1, mul_one]
      _ ≤ (q * a + (1 - q) * Bd) * Bd ^ (q - 1) := mul_le_mul_of_nonneg_right h hB1
      _ = K1 * a + K0 * Bd ^ (q - 1) := by rw [hK1, hK0']; ring
  have hxf : x ∈ faceOpen (Finset.univ : Finset (Fin n)) :=
    ⟨openOrthant_sub hx, fun i hi => absurd (Finset.mem_univ i) hi, fun i _ => hx i⟩
  have hinv := face_inv C hB hA.2.1 hxf hY
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (Vfun c p (Y t ω) ^ θ) ≤
      ENNReal.ofReal K1 * ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) +
        ENNReal.ofReal (K0 * Bd ^ (q - 1)) := by
    filter_upwards [hinv] with ω h
    have hyo : Y t ω ∈ openOrthant n := fun i => (h t).2.2 i (Finset.mem_univ i)
    have hV : 0 < Vfun c p (Y t ω) := fin_Vfun_pos hc hyo
    have ha : 0 ≤ Vfun c p (Y t ω) ^ δ₀ := (Real.rpow_pos_of_pos hV _).le
    have e : Vfun c p (Y t ω) ^ θ = (Vfun c p (Y t ω) ^ δ₀) ^ q := by
      rw [← Real.rpow_mul hV.le, hq]; congr 1; field_simp
    rw [e, ← ENNReal.ofReal_mul hK1n, ← ENNReal.ofReal_add (mul_nonneg hK1n ha) hK0n]
    exact ENNReal.ofReal_le_ofReal (hpt _ ha)
  calc ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ θ) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal K1 * ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) +
        ENNReal.ofReal (K0 * Bd ^ (q - 1))) ∂P := lintegral_mono_ae hae
    _ = ENNReal.ofReal K1 * ∫⁻ ω, ENNReal.ofReal (Vfun c p (Y t ω) ^ δ₀) ∂P +
        ENNReal.ofReal (K0 * Bd ^ (q - 1)) := by
      rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal K1 * ENNReal.ofReal Bd + ENNReal.ofReal (K0 * Bd ^ (q - 1)) := by
      gcongr
    _ = ENNReal.ofReal (Real.exp (θ * Hconst C c γb δ₀ * t) * Vfun c p x ^ θ) := by
      rw [← ENNReal.ofReal_mul hK1n, ← ENNReal.ofReal_add (mul_nonneg hK1n hBd0.le) hK0n]
      congr 1
      have e2 : Bd ^ q = Bd * Bd ^ (q - 1) := by
        rw [← Real.rpow_one_add' hBd0.le (by linarith : (1 : ℝ) + (q - 1) ≠ 0)]; congr 1; ring
      have e3 : Bd ^ q = Real.exp (θ * Hconst C c γb δ₀ * t) * Vfun c p x ^ θ := by
        rw [hBd, Real.mul_rpow (Real.exp_pos _).le (Real.rpow_pos_of_pos (fin_Vfun_pos hc hx) _).le,
          ← Real.exp_mul, ← Real.rpow_mul (fin_Vfun_pos hc hx).le, hq]
        congr 2 <;> field_simp
      rw [← e3, e2, hK1, hK0']; ring

/-- One-step bound from `y` with `κ(y) > 0` (so `l1 y < M`): (4.17) for `r ≥ T*`, Jensen otherwise. -/
theorem fin_step (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {C : Coeffs n}
    {B : ℝ≥0 → Ω → SDEState n} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hX : IsSolutionFamily P C B X) {c p : SDEState n} {γb δ₀ θ ρ Tstar Kθ M c1 t : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (hθ : 0 < θ) (hθδ : θ ≤ δ₀) (hρ : 0 < ρ) (hKθ : 0 < Kθ)
    (hprop : ∀ T : ℝ, Tstar ≤ T → T ≤ t → ∀ x ∈ openOrthant n, l1 x ≤ M →
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + Kθ))
    (hc1a : Real.exp (-(1 / 2) * θ * ρ * Tstar) ≤ c1)
    (hc1b : Real.exp (θ * Hconst C c γb δ₀ * Tstar - γb * θ * (t - Tstar)) ≤ c1)
    {y : SDEState n} (hy : y ∈ openOrthant n) (hyM : l1 y ≤ M) {r : ℝ} (hr0 : 0 ≤ r)
    (hrt : r ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (Vfun c p (X y r.toNNReal ω) ^ θ) ∂P ≤
      ENNReal.ofReal (c1 * Real.exp (γb * θ * (t - r)) * Vfun c p y ^ θ + Kθ) := by
  haveI := hX.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  have hW : 0 ≤ Vfun c p y ^ θ := (Real.rpow_pos_of_pos (fin_Vfun_pos hc hy) _).le
  have hc10 : 0 ≤ c1 := (Real.exp_pos _).le.trans hc1a
  have hE1 : 1 ≤ Real.exp (γb * θ * (t - r)) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg hγ.le hθ.le) (by linarith))
  have hH := Hconst_nonneg hA hδ
  by_cases hT : Tstar ≤ r
  · refine (hprop r hT hrt y hy hyM).trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Real.exp (-(1 / 2) * θ * ρ * r) ≤ c1 * Real.exp (γb * θ * (t - r)) := by
      calc Real.exp (-(1 / 2) * θ * ρ * r) ≤ Real.exp (-(1 / 2) * θ * ρ * Tstar) :=
            Real.exp_le_exp.2 (by
              have := mul_le_mul_of_nonneg_left hT (mul_nonneg hθ.le hρ.le)
              linarith)
        _ ≤ c1 := hc1a
        _ ≤ c1 * Real.exp (γb * θ * (t - r)) := le_mul_of_one_le_right hc10 hE1
    nlinarith
  · push_neg at hT
    have hj := fin_jensen hn hX.2.1 hA hδ hp hpl hθ hθδ hy (hX.2.2 y (openOrthant_sub hy))
      r.toNNReal
    rw [Real.coe_toNNReal r hr0] at hj
    refine hj.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : Real.exp (θ * Hconst C c γb δ₀ * r) ≤ c1 * Real.exp (γb * θ * (t - r)) := by
      calc Real.exp (θ * Hconst C c γb δ₀ * r)
          ≤ Real.exp (θ * Hconst C c γb δ₀ * Tstar - γb * θ * (t - Tstar)) *
            Real.exp (γb * θ * (t - Tstar)) := by
            rw [← Real.exp_add]; refine Real.exp_le_exp.2 ?_
            have : θ * Hconst C c γb δ₀ * r ≤ θ * Hconst C c γb δ₀ * Tstar :=
              mul_le_mul_of_nonneg_left hT.le (mul_nonneg hθ.le hH)
            linarith
        _ ≤ c1 * Real.exp (γb * θ * (t - r)) := by
            refine mul_le_mul hc1b (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hc10
            have : γb * θ * r ≤ γb * θ * Tstar :=
              mul_le_mul_of_nonneg_left hT.le (mul_nonneg hγ.le hθ.le)
            linarith
    nlinarith

end FINa

section FINb
/-! a4101326 S5b/S6: Duhamel + weighted Markov + Feynman-Kac, then (4.18). -/
variable {n : ℕ}

theorem fin_W_contOn {c p : SDEState n} {θ : ℝ} (hθ : 0 ≤ θ) :
    ContinuousOn (fun y => Vfun c p y ^ θ) (openOrthant n) := by
  have hnum : Continuous fun y : SDEState n => 1 + ∑ i, c i * y i :=
    continuous_const.add (continuous_finset_sum _ fun i _ => continuous_const.mul (fin_coord_cont i))
  have hden : ContinuousOn (fun y : SDEState n => ∏ i, y i ^ p i) (openOrthant n) :=
    continuousOn_finset_prod _ fun i _ =>
      (fin_coord_cont i).continuousOn.rpow_const fun y hy => Or.inl (hy i).ne'
  have hV : ContinuousOn (Vfun c p) (openOrthant n) :=
    hnum.continuousOn.div hden fun y hy =>
      (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hy i) _).ne'
  exact hV.rpow_const fun y _ => Or.inr hθ

set_option maxHeartbeats 4000000 in
theorem fin_main (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {C : Coeffs n}
    {B : ℝ≥0 → Ω → SDEState n} {X : SDEState n → ℝ≥0 → Ω → SDEState n}
    (hX : IsSolutionFamily P C B X) {c p : SDEState n} {γb δ₀ θ lam Kθ c1 N : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (hθ : 0 < θ) (hθδ : θ ≤ δ₀) (hlam0 : 0 < lam) (hlam : lam ≤ 1)
    (hKθ : 0 ≤ Kθ) (hc10 : 0 ≤ c1) {κ : SDEState n → ℝ} (hκc : Continuous κ)
    (hκ0 : ∀ z, 0 ≤ κ z) (hN : 0 < N) (hκN : ∀ z, κ z ≤ N)
    (hκR : ∀ z ∈ openOrthant n, 0 < Rf C c γb z →
      θ * (Hconst C c γb δ₀ + γb) ≤ (1 - lam) * κ z)
    (t : ℝ≥0)
    (hstep : ∀ y ∈ openOrthant n, 0 < κ y → ∀ r : ℝ, 0 ≤ r → r ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X y r.toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (c1 * Real.exp (γb * θ * (t - r)) * Vfun c p y ^ θ + Kθ))
    {x : SDEState n} (hx : x ∈ openOrthant n) :
    ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x t ω) ^ θ) ∂P ≤
      ENNReal.ofReal (max (Real.exp (-(γb * θ * t))) (c1 / lam) * Vfun c p x ^ θ + Kθ) := by
  haveI := hX.1
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hB := hX.2.1
  have hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) (X x) :=
    hX.2.2 x (openOrthant_sub hx)
  have hWm : Measurable fun y => Vfun c p y ^ θ := fin_Vfun_meas c p θ
  have hxf : x ∈ faceOpen (Finset.univ : Finset (Fin n)) :=
    ⟨openOrthant_sub hx, fun i hi => absurd (Finset.mem_univ i) hi, fun i _ => hx i⟩
  have hinv := face_inv C hB hA.2.1 hxf hY
  have hpos : ∀ᵐ ω ∂P, ∀ s, X x s ω ∈ openOrthant n := by
    filter_upwards [hinv] with ω h using fun s i => (h s).2.2 i (Finset.mem_univ i)
  have hYc' : ∀ ω, Continuous fun v : ℝ => X x v.toNNReal ω := fun ω =>
    (hY.2.1 ω).comp continuous_real_toNNReal
  set A : ℝ → Ω → ℝ := fun u ω =>
    ∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), κ (X x v.toNNReal ω) with hAdef
  set At : Ω → ℝ := fun ω => ∫ v in (0 : ℝ)..(t : ℝ), κ (X x v.toNNReal ω) with hAtdef
  have hAc : ∀ ω, Continuous fun u => A u ω := fun ω =>
    (continuous_primitive_nn (hκc.comp (hYc' ω))).comp continuous_real_toNNReal
  have hAm : ∀ u, Measurable (A u) := fun u =>
    measurable_intervalIntegral_of_continuous _ (H := fun v ω => κ (X x v ω)) u.toNNReal
      (fun v _ => hκc.measurable.comp (hY.1 v)) (fun ω => hκc.comp (hY.2.1 ω))
  have hAtm : Measurable At :=
    measurable_intervalIntegral_of_continuous _ (H := fun v ω => κ (X x v ω)) t
      (fun v _ => hκc.measurable.comp (hY.1 v)) (fun ω => hκc.comp (hY.2.1 ω))
  have hA0 : ∀ u ω, 0 ≤ A u ω := fun u ω =>
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun v _ => hκ0 _
  have hAt0 : ∀ ω, 0 ≤ At ω := fun ω =>
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun v _ => hκ0 _
  have hI3 : ∀ ω, ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-A u ω) * κ (X x u.toNNReal ω) =
      1 - Real.exp (-At ω) := by
    intro ω
    have h := integral_exp_neg_primitive (hκc.comp (hYc' ω)) t
    refine (intervalIntegral.integral_congr fun u hu => ?_).trans h
    have hu0 : 0 ≤ u := by
      rw [uIcc_of_le (NNReal.coe_nonneg t)] at hu; exact hu.1
    simp only [hAdef, Function.comp_apply, Real.coe_toNNReal u hu0]
  -- joint measurability
  have hYj : Measurable (fun q : Ω × ℝ => X x q.2.toNNReal q.1) :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun (u : ℝ) ω => X x u.toNNReal ω)
      hYc' (fun u => hY.1 _)).comp measurable_swap
  have hAj : Measurable (fun q : Ω × ℝ => A q.2 q.1) :=
    (measurable_uncurry_of_continuous_of_measurable (u := A) hAc hAm).comp measurable_swap
  have hYt : Measurable (fun q : Ω × ℝ => X x t q.1) := (hY.1 t).comp measurable_fst
  have hsnd : Measurable (fun q : Ω × ℝ => ((q.2.toNNReal : ℝ≥0) : ℝ)) :=
    (NNReal.continuous_coe.comp continuous_real_toNNReal).measurable.comp measurable_snd
  set G : ℝ → Ω → ℝ := fun u ω =>
    Real.exp (-A u ω) * κ (X x u.toNNReal ω) * Vfun c p (X x t ω) ^ θ with hGdef
  set G2 : ℝ → Ω → ℝ := fun u ω =>
    c1 * (κ (X x u.toNNReal ω) * (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) *
      Vfun c p (X x u.toNNReal ω) ^ θ)) +
    Kθ * (Real.exp (-A u ω) * κ (X x u.toNNReal ω)) with hG2def
  have hGj : Measurable (fun q : Ω × ℝ => ENNReal.ofReal (G q.2 q.1)) :=
    ENNReal.measurable_ofReal.comp (((Real.measurable_exp.comp hAj.neg).mul
      (hκc.measurable.comp hYj)).mul (hWm.comp hYt))
  have hG2j : Measurable (fun q : Ω × ℝ => ENNReal.ofReal (G2 q.2 q.1)) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul ((hκc.measurable.comp hYj).mul
      ((Real.measurable_exp.comp ((measurable_const.mul hsnd).sub hAj)).mul
        (hWm.comp hYj)))).add
      (measurable_const.mul ((Real.measurable_exp.comp hAj.neg).mul (hκc.measurable.comp hYj))))
  -- P1: pathwise Duhamel identity
  have hP1 : ∀ ω, ENNReal.ofReal (Vfun c p (X x t ω) ^ θ) ≤
      ENNReal.ofReal (Real.exp (-At ω) * Vfun c p (X x t ω) ^ θ) +
        ∫⁻ u in Ioc (0 : ℝ) t, ENNReal.ofReal (G u ω) := by
    intro ω
    by_cases hw : Vfun c p (X x t ω) ^ θ ≤ 0
    · rw [ENNReal.ofReal_of_nonpos hw]; positivity
    push_neg at hw
    have hGc : Continuous fun u => G u ω :=
      ((Real.continuous_exp.comp (hAc ω).neg).mul (hκc.comp (hYc' ω))).mul continuous_const
    have hG0 : ∀ u, 0 ≤ G u ω := fun u =>
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (hκ0 _)) hw.le
    rw [← ofReal_integral_eq_lintegral_ofReal (hGc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_of_all _ hG0), ← intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
    have e : ∫ u in (0 : ℝ)..(t : ℝ), G u ω = (1 - Real.exp (-At ω)) * Vfun c p (X x t ω) ^ θ := by
      simp only [hGdef]
      rw [intervalIntegral.integral_mul_const, hI3 ω]
    have h1 : Real.exp (-At ω) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (hAt0 ω))
    rw [e, ← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le hw.le)
      (mul_nonneg (by linarith) hw.le)]
    exact le_of_eq (congrArg _ (by ring))
  -- P3: weighted Markov at each time u
  have hP3 : ∀ u ∈ Ioc (0 : ℝ) t,
      ∫⁻ ω, ENNReal.ofReal (G u ω) ∂P ≤ ∫⁻ ω, ENNReal.ofReal (G2 u ω) ∂P := by
    rintro u ⟨hu0, hut⟩
    have hsu : ((u.toNNReal : ℝ≥0) : ℝ) = u := Real.coe_toNNReal u hu0.le
    have hs0 : 0 < u.toNNReal := Real.toNNReal_pos.2 hu0
    have hst : u.toNNReal ≤ t := by rw [← NNReal.coe_le_coe, hsu]; exact hut
    obtain ⟨K, hKM, hKx, hKw⟩ := kolm_markov_w P C B X hX c γb hA (t - u.toNNReal)
    have hAm' : Measurable[completedBrownianPast P B (fun _ => x) u.toNNReal] (A u) :=
      measurable_intervalIntegral_of_continuous _ (H := fun v ω => κ (X x v ω)) u.toNNReal
        (fun v hv => hκc.measurable.comp
          ((hY.2.2.1 v).mono (completedBrownianPast_mono P B _ hv) le_rfl))
        (fun ω => hκc.comp (hY.2.1 ω))
    have hZm : Measurable[completedBrownianPast P B (fun _ => x) u.toNNReal]
        (fun ω => Real.exp (-A u ω) * κ (X x u.toNNReal ω) / N) :=
      ((Real.measurable_exp.comp hAm'.neg).mul
        (hκc.measurable.comp (hY.2.2.1 u.toNNReal))).div_const N
    have hZa : Measurable (fun ω => Real.exp (-A u ω) * κ (X x u.toNNReal ω) / N) :=
      ((Real.measurable_exp.comp (hAm u).neg).mul (hκc.measurable.comp (hY.1 _))).div_const N
    have hZ0 : ∀ ω, 0 ≤ Real.exp (-A u ω) * κ (X x u.toNNReal ω) / N := fun ω =>
      div_nonneg (mul_nonneg (Real.exp_pos _).le (hκ0 _)) hN.le
    have hZ1 : ∀ ω, Real.exp (-A u ω) * κ (X x u.toNNReal ω) / N ≤ 1 := fun ω => by
      rw [div_le_one hN]
      have h1 : Real.exp (-A u ω) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (hA0 u ω))
      calc Real.exp (-A u ω) * κ (X x u.toNNReal ω) ≤ 1 * κ (X x u.toNNReal ω) :=
            mul_le_mul_of_nonneg_right h1 (hκ0 _)
        _ ≤ N := by rw [one_mul]; exact hκN _
    have hF : Measurable fun y => ENNReal.ofReal (Vfun c p y ^ θ) :=
      ENNReal.measurable_ofReal.comp hWm
    have hmk := hKw x (openOrthant_sub hx) u.toNNReal hs0 _ hZm hZa hZ0 hZ1 _ hF
    rw [add_tsub_cancel_of_le hst] at hmk
    have hts : (((t - u.toNNReal : ℝ≥0)) : ℝ) = t - u := by rw [NNReal.coe_sub hst, hsu]
    calc ∫⁻ ω, ENNReal.ofReal (G u ω) ∂P
        = ENNReal.ofReal N * ∫⁻ ω, ENNReal.ofReal (Real.exp (-A u ω) * κ (X x u.toNNReal ω) / N) *
            ENNReal.ofReal (Vfun c p (X x t ω) ^ θ) ∂P := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun ω => ?_
          rw [← ENNReal.ofReal_mul (hZ0 ω), ← ENNReal.ofReal_mul hN.le]
          congr 1
          simp only [hGdef]
          field_simp
      _ = ENNReal.ofReal N * ∫⁻ ω, ENNReal.ofReal (Real.exp (-A u ω) * κ (X x u.toNNReal ω) / N) *
            ∫⁻ y, ENNReal.ofReal (Vfun c p y ^ θ) ∂(K (X x u.toNNReal ω)) ∂P := by rw [hmk]
      _ ≤ ENNReal.ofReal N * ∫⁻ ω, ENNReal.ofReal (Real.exp (-A u ω) * κ (X x u.toNNReal ω) / N) *
            ENNReal.ofReal (c1 * Real.exp (γb * θ * u) * Vfun c p (X x u.toNNReal ω) ^ θ + Kθ) ∂P := by
          gcongr ENNReal.ofReal N * ?_
          refine lintegral_mono_ae ?_
          filter_upwards [hpos] with ω hω
          by_cases hk : κ (X x u.toNNReal ω) = 0
          · simp [hk]
          have hk' : 0 < κ (X x u.toNNReal ω) := lt_of_le_of_ne (hκ0 _) (Ne.symm hk)
          gcongr _ * ?_
          have hyo := hω u.toNNReal
          rw [hKx _ (openOrthant_sub hyo), StochKolmogorov.Persist.trans,
            lintegral_map hF ((hX.2.2 _ (openOrthant_sub hyo)).1 (t - u.toNNReal))]
          have h := hstep _ hyo hk' (((t - u.toNNReal : ℝ≥0)) : ℝ) (NNReal.coe_nonneg _)
            (by rw [hts]; linarith)
          rw [Real.toNNReal_coe, hts] at h
          refine h.trans (le_of_eq ?_)
          congr 3; ring
      _ = ∫⁻ ω, ENNReal.ofReal (G2 u ω) ∂P := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun ω => ?_
          rw [← ENNReal.ofReal_mul (hZ0 ω), ← ENNReal.ofReal_mul hN.le]
          congr 1
          simp only [hG2def, hsu]
          rw [Real.exp_sub, Real.exp_neg]
          field_simp
  -- P6: pathwise comparison with the Feynman-Kac functional
  set coef : ℝ := max (Real.exp (-(γb * θ * t))) (c1 / lam) with hcoef
  have hcoef0 : 0 ≤ coef := (Real.exp_pos _).le.trans (le_max_left _ _)
  have hP6 : ∀ᵐ ω ∂P, ENNReal.ofReal (Real.exp (-At ω) * Vfun c p (X x t ω) ^ θ) +
        ∫⁻ u in Ioc (0 : ℝ) t, ENNReal.ofReal (G2 u ω) ≤
      ENNReal.ofReal coef * (ENNReal.ofReal (Real.exp (γb * θ * t - At ω) *
        Vfun c p (X x t ω) ^ θ) +
      ENNReal.ofReal (∫ u in (0 : ℝ)..(t : ℝ), lam * (κ (X x u.toNNReal ω) *
        (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) * Vfun c p (X x u.toNNReal ω) ^ θ)))) +
      ENNReal.ofReal Kθ := by
    filter_upwards [hpos] with ω hω
    have hVc : Continuous fun u : ℝ => Vfun c p (X x u.toNNReal ω) ^ θ :=
      (fin_W_contOn hθ.le).comp_continuous (hYc' ω) (fun u => hω _)
    have hWt : 0 ≤ Vfun c p (X x t ω) ^ θ := (Real.rpow_pos_of_pos (fin_Vfun_pos hc (hω t)) _).le
    have hWu : ∀ u : ℝ, 0 ≤ Vfun c p (X x u.toNNReal ω) ^ θ := fun u =>
      (Real.rpow_pos_of_pos (fin_Vfun_pos hc (hω _)) _).le
    have ha_c : Continuous fun u : ℝ => κ (X x u.toNNReal ω) *
        (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) * Vfun c p (X x u.toNNReal ω) ^ θ) :=
      (hκc.comp (hYc' ω)).mul ((Real.continuous_exp.comp ((continuous_const.mul
        (NNReal.continuous_coe.comp continuous_real_toNNReal)).sub (hAc ω))).mul hVc)
    have hb_c : Continuous fun u : ℝ => Real.exp (-A u ω) * κ (X x u.toNNReal ω) :=
      (Real.continuous_exp.comp (hAc ω).neg).mul (hκc.comp (hYc' ω))
    have ha0 : ∀ u : ℝ, 0 ≤ κ (X x u.toNNReal ω) *
        (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) * Vfun c p (X x u.toNNReal ω) ^ θ) :=
      fun u => mul_nonneg (hκ0 _) (mul_nonneg (Real.exp_pos _).le (hWu u))
    have hG2c : Continuous fun u => G2 u ω :=
      (continuous_const.mul ha_c).add (continuous_const.mul hb_c)
    have hG2n : ∀ u, 0 ≤ G2 u ω := fun u =>
      add_nonneg (mul_nonneg hc10 (ha0 u)) (mul_nonneg hKθ (mul_nonneg (Real.exp_pos _).le (hκ0 _)))
    rw [← ofReal_integral_eq_lintegral_ofReal (hG2c.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (ae_of_all _ hG2n), ← intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
    have hsplit : ∫ u in (0 : ℝ)..(t : ℝ), G2 u ω =
        c1 * (∫ u in (0 : ℝ)..(t : ℝ), κ (X x u.toNNReal ω) *
          (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) * Vfun c p (X x u.toNNReal ω) ^ θ)) +
        Kθ * (1 - Real.exp (-At ω)) := by
      have hac1 : Continuous fun u : ℝ => c1 * (κ (X x u.toNNReal ω) *
          (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) * Vfun c p (X x u.toNNReal ω) ^ θ)) :=
        continuous_const.mul ha_c
      have hbc1 : Continuous fun u : ℝ => Kθ * (Real.exp (-A u ω) * κ (X x u.toNNReal ω)) :=
        continuous_const.mul hb_c
      simp only [hG2def]
      rw [intervalIntegral.integral_add (hac1.intervalIntegrable _ _)
        (hbc1.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, hI3 ω]
    rw [hsplit, intervalIntegral.integral_const_mul]
    set I2 : ℝ := ∫ u in (0 : ℝ)..(t : ℝ), κ (X x u.toNNReal ω) *
          (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) * Vfun c p (X x u.toNNReal ω) ^ θ)
      with hI2
    have hI20 : 0 ≤ I2 := intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) fun u _ => ha0 u
    have he1 : Real.exp (-At ω) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (hAt0 ω))
    have hF1 : 0 ≤ Real.exp (γb * θ * t - At ω) * Vfun c p (X x t ω) ^ θ :=
      mul_nonneg (Real.exp_pos _).le hWt
    have hlI : 0 ≤ lam * I2 := mul_nonneg hlam0.le hI20
    rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le hWt)
        (add_nonneg (mul_nonneg hc10 hI20) (mul_nonneg hKθ (by linarith))),
      ← ENNReal.ofReal_add hF1 hlI, ← ENNReal.ofReal_mul hcoef0,
      ← ENNReal.ofReal_add (mul_nonneg hcoef0 (add_nonneg hF1 hlI)) hKθ]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : Real.exp (-At ω) = Real.exp (-(γb * θ * t)) * Real.exp (γb * θ * t - At ω) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : c1 * I2 = (c1 / lam) * (lam * I2) := by field_simp
    have k1 : Real.exp (-(γb * θ * t)) ≤ coef := le_max_left _ _
    have k2 : c1 / lam ≤ coef := le_max_right _ _
    have k3 : Kθ * (1 - Real.exp (-At ω)) ≤ Kθ := by nlinarith [Real.exp_pos (-At ω)]
    calc Real.exp (-At ω) * Vfun c p (X x t ω) ^ θ + (c1 * I2 + Kθ * (1 - Real.exp (-At ω)))
        = Real.exp (-(γb * θ * t)) * (Real.exp (γb * θ * t - At ω) * Vfun c p (X x t ω) ^ θ) +
          (c1 / lam) * (lam * I2) + Kθ * (1 - Real.exp (-At ω)) := by rw [e1, e2]; ring
      _ ≤ coef * (Real.exp (γb * θ * t - At ω) * Vfun c p (X x t ω) ^ θ) + coef * (lam * I2) + Kθ :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_right k1 hF1)
            (mul_le_mul_of_nonneg_right k2 hlI)) k3
      _ = coef * (Real.exp (γb * θ * t - At ω) * Vfun c p (X x t ω) ^ θ + lam * I2) + Kθ := by ring
  have hFK := fk hn hB hA hδ hp hpl hθ hθδ hlam0.le hlam hκc hκ0 hκN hκR hx hY t
  have hmeas1 : Measurable fun ω => ENNReal.ofReal (Real.exp (-At ω) * Vfun c p (X x t ω) ^ θ) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp hAtm.neg).mul (hWm.comp (hY.1 t)))
  have hWx : 0 ≤ Vfun c p x ^ θ := (Real.rpow_pos_of_pos (fin_Vfun_pos hc hx) _).le
  calc ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x t ω) ^ θ) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (-At ω) * Vfun c p (X x t ω) ^ θ) +
          ∫⁻ u in Ioc (0 : ℝ) t, ENNReal.ofReal (G u ω)) ∂P := lintegral_mono hP1
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (-At ω) * Vfun c p (X x t ω) ^ θ) ∂P +
          ∫⁻ u in Ioc (0 : ℝ) t, ∫⁻ ω, ENNReal.ofReal (G u ω) ∂P := by
        rw [lintegral_add_left hmeas1, lintegral_lintegral_swap (μ := P)
          (ν := volume.restrict (Ioc (0 : ℝ) t)) (f := fun ω u => ENNReal.ofReal (G u ω))
          hGj.aemeasurable]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (-At ω) * Vfun c p (X x t ω) ^ θ) ∂P +
          ∫⁻ u in Ioc (0 : ℝ) t, ∫⁻ ω, ENNReal.ofReal (G2 u ω) ∂P :=
        add_le_add le_rfl (lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).2
          (Eventually.of_forall hP3)))
    _ = ∫⁻ ω, (ENNReal.ofReal (Real.exp (-At ω) * Vfun c p (X x t ω) ^ θ) +
          ∫⁻ u in Ioc (0 : ℝ) t, ENNReal.ofReal (G2 u ω)) ∂P := by
        rw [lintegral_add_left hmeas1, lintegral_lintegral_swap (μ := P)
          (ν := volume.restrict (Ioc (0 : ℝ) t)) (f := fun ω u => ENNReal.ofReal (G2 u ω))
          hG2j.aemeasurable]
    _ ≤ ∫⁻ ω, (ENNReal.ofReal coef * (ENNReal.ofReal (Real.exp (γb * θ * t - At ω) *
          Vfun c p (X x t ω) ^ θ) +
        ENNReal.ofReal (∫ u in (0 : ℝ)..(t : ℝ), lam * (κ (X x u.toNNReal ω) *
          (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) * Vfun c p (X x u.toNNReal ω) ^ θ)))) +
        ENNReal.ofReal Kθ) ∂P := lintegral_mono_ae hP6
    _ = ENNReal.ofReal coef * ∫⁻ ω, (ENNReal.ofReal (Real.exp (γb * θ * t - At ω) *
          Vfun c p (X x t ω) ^ θ) +
        ENNReal.ofReal (∫ u in (0 : ℝ)..(t : ℝ), lam * (κ (X x u.toNNReal ω) *
          (Real.exp (γb * θ * (u.toNNReal : ℝ) - A u ω) * Vfun c p (X x u.toNNReal ω) ^ θ)))) ∂P +
        ENNReal.ofReal Kθ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal coef * ENNReal.ofReal (Vfun c p x ^ θ) + ENNReal.ofReal Kθ := by
        gcongr
    _ = ENNReal.ofReal (coef * Vfun c p x ^ θ + Kθ) := by
        rw [← ENNReal.ofReal_mul hcoef0, ← ENNReal.ofReal_add (mul_nonneg hcoef0 hWx) hKθ]

end FINb

section FINc
/-! a4101326 S6: (4.18) of Theorem 4.1. -/

theorem fin_eq418 {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (M : ℝ) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (Tstar : ℝ) (hTstar : 0 < Tstar)
    (nstar : ℕ) (hnstar : Hconst C c γb δ₀ < γb * ((nstar : ℝ) - 1))
    (θ : ℝ) (hθ : 0 < θ) (hθδ : θ < δ₀ / 2) (Kθ : ℝ) (hKθ : 0 < Kθ)
    (hprop : ∀ T : ℝ, Tstar ≤ T → T ≤ nstar * Tstar → ∀ x ∈ openOrthant n, l1 x ≤ M →
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + Kθ)) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ Kt : ℝ, 0 < Kt ∧ ∀ x ∈ openOrthant n,
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x ((nstar : ℝ) * Tstar).toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (κ * Vfun c p x ^ θ + Kt) := by
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  have hδ0 : 0 < δ₀ := hδ₀.1
  have hH := Hconst_nonneg hA hδ₀
  have hθδ' : θ ≤ δ₀ := by linarith
  have hexp1 : ∀ y : ℝ, y < 0 → Real.exp y < 1 := fun y hy => by
    simpa using Real.exp_lt_exp.2 hy
  have hn1 : (1 : ℝ) < nstar := by
    by_contra h
    have : γb * ((nstar : ℝ) - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hγ.le (by linarith [not_lt.1 h])
    linarith
  have htR0 : 0 < (nstar : ℝ) * Tstar := mul_pos (by linarith) hTstar
  have ht : ((((nstar : ℝ) * Tstar).toNNReal : ℝ≥0) : ℝ) = nstar * Tstar :=
    Real.coe_toNNReal _ htR0.le
  set t : ℝ≥0 := ((nstar : ℝ) * Tstar).toNNReal with htdef
  set c1 : ℝ := max (Real.exp (-(1 / 2) * θ * ρ * Tstar))
    (Real.exp (θ * Hconst C c γb δ₀ * Tstar - γb * θ * (t - Tstar))) with hc1
  have hc10 : 0 ≤ c1 := (Real.exp_pos _).le.trans (le_max_left _ _)
  have hc11 : c1 < 1 := by
    refine max_lt (hexp1 _ ?_) (hexp1 _ ?_)
    · have := mul_pos (mul_pos hθ hρ) hTstar
      linarith
    · have h := mul_lt_mul_of_pos_left hnstar (mul_pos hθ hTstar)
      rw [ht]
      nlinarith
  set lam : ℝ := (1 + c1) / 2 with hlam
  have hlam0 : 0 < lam := by rw [hlam]; linarith
  have hlam1 : lam ≤ 1 := by rw [hlam]; linarith
  have hl1 : (0 : ℝ) < 1 - lam := by rw [hlam]; linarith
  set N : ℝ := θ * (Hconst C c γb δ₀ + γb) / (1 - lam) with hNdef
  have hN : 0 < N := div_pos (mul_pos hθ (by linarith)) hl1
  obtain ⟨k, hkc, hk0, hkN, hkM, hkR⟩ := fin_clock C hc hA.2.1 hM hN.le
  have hκR : ∀ z ∈ openOrthant n, 0 < Rf C c γb z →
      θ * (Hconst C c γb δ₀ + γb) ≤ (1 - lam) * k z := fun z hz hR => by
    have e : (1 - lam) * N = θ * (Hconst C c γb δ₀ + γb) := by
      rw [hNdef]; field_simp
    rw [hkR z hz hR, e]
  have hprop' : ∀ T : ℝ, Tstar ≤ T → T ≤ (t : ℝ) → ∀ x ∈ openOrthant n, l1 x ≤ M →
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + Kθ) :=
    fun T h1 h2 => hprop T h1 (h2.trans_eq ht)
  have hstep : ∀ y ∈ openOrthant n, 0 < k y → ∀ r : ℝ, 0 ≤ r → r ≤ t →
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X y r.toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (c1 * Real.exp (γb * θ * (t - r)) * Vfun c p y ^ θ + Kθ) :=
    fun y hy hky r hr0 hrt => fin_step hn hX hA hδ₀ hp hpδ.le hθ hθδ' hρ hKθ hprop'
      (le_max_left _ _) (le_max_right _ _) hy (hkM y hky).le hr0 hrt
  refine ⟨max (Real.exp (-(γb * θ * t))) (c1 / lam),
    lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _), max_lt ?_ ?_, Kθ, hKθ, fun x hx => ?_⟩
  · refine hexp1 _ ?_
    have := mul_pos (mul_pos hγ hθ) (show (0 : ℝ) < t by rw [ht]; exact htR0)
    linarith
  · rw [div_lt_one hlam0, hlam]; linarith
  · exact fin_main hn hX hA hδ₀ hp hpδ.le hθ hθδ' hlam0 hlam1 hKθ.le hc10 hkc hk0 hN hkN hκR t
      hstep hx

end FINc

end ItoLib

end FlatM_FIN

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open EthierKurtz in
open StochKolmogorov.Persist in
open EthierKurtz in
set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (h12 : Assumption12 P C X) (M : ℝ) (hMpos : 0 < M) (hM : IsRadiusM C c γb M)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n) (hpδ : l1 p = δ₀)
    (ρ : ℝ) (hρ : 0 < ρ) (h41 : IsWeightedInvasionMin P C X p ρ)
    (Tstar : ℝ) (hTstar : 0 < Tstar)
    (hT : ∀ T : ℝ, Tstar < T → ∀ x ∈ bdry n, l1 x ≤ M →
      Integrable (Phi C c p) (occMean P X x T) ∧ ∫ y, Phi C c p y ∂(occMean P X x T) ≤ -ρ)
    (nstar : ℕ) (hnstar : Hconst C c γb δ₀ < γb * ((nstar : ℝ) - 1))
    (θ : ℝ) (hθ : 0 < θ) (hθδ : θ < δ₀ / 2) (Kθ : ℝ) (hKθ : 0 < Kθ)
    (hprop : ∀ T : ℝ, Tstar ≤ T → T ≤ nstar * Tstar → ∀ x ∈ openOrthant n, l1 x ≤ M →
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x T.toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (Vfun c p x ^ θ * Real.exp (-(1 / 2) * θ * ρ * T) + Kθ)) :
    ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧ ∃ Kt : ℝ, 0 < Kt ∧ ∀ x ∈ openOrthant n,
      ∫⁻ ω, ENNReal.ofReal (Vfun c p (X x ((nstar : ℝ) * Tstar).toNNReal ω) ^ θ) ∂P ≤
        ENNReal.ofReal (κ * Vfun c p x ^ θ + Kt) := by
  exact ItoLib.fin_eq418 hn P C B X hX c γb hA M hM δ₀ hδ₀ p hp hpδ ρ hρ Tstar hTstar nstar hnstar θ hθ hθδ Kθ hKθ hprop
