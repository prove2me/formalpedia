-- Prove2me | solution 1 for StochKolmogorov.Extinct.box_ball_window
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-03T20:44:50.018189+00:00
-- url     : https://prove2.me/submissions/2778d109-6d47-4d98-b656-3bfca8aed380

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Extinct_Extinction
import Definitions.Def_StochKolmogorov_Persist_Model
import Definitions.Def_TotalVariationDist
import Theorems.Thm_EthierKurtz_euler_scheme_approx_abs
import Theorems.Thm_EthierKurtz_euler_chain_steer_minorisation

set_option linter.all false
set_option Elab.async false


-- ===== ItoM1 =====

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false

namespace ItoLib
open EthierKurtz

variable {Ω : Type*} {d : ℕ}

section BM
variable [MeasurableSpace Ω]

theorem stdBrownian_coord_measurable {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (t : ℝ≥0) (i : Fin d) : Measurable (fun ω => W t ω i) := by
  have := hW.1 t
  fun_prop

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

/-- The path coordinate `j` as a function of real time. -/
noncomputable def wr (j : Fin d) (r : ℝ) : ℝ := w r.toNNReal j

/-- Increment of the scheme over `[k h, k h + r]` from the pair `(a, z) = (Z_{k-1}, Z_k)`. -/
noncomputable def cellInc (a z : SDEState d) (k : ℕ) (r : ℝ) : SDEState d :=
  WithLp.toLp 2 fun i => (∑ j, (s₁ a (i, j) * (wr w j (k * h + r) - wr w j (k * h)) +
      (s₁ z (i, j) - s₁ a (i, j)) / h *
        (r * wr w j (k * h + r) - ∫ v in (k * h : ℝ)..(k * h + r), wr w j v))) +
    b₁ a i * r + (b₁ z i - b₁ a i) * r ^ 2 / (2 * h)

/-- Grid values: `eulerZZ k = (Z_{k-1}, Z_k)`, `Z_{-1} = a`, `Z_0 = y`. -/
noncomputable def eulerZZ (a y : SDEState d) : ℕ → SDEState d × SDEState d
  | 0 => (a, y)
  | k + 1 => ((eulerZZ a y k).2,
      (eulerZZ a y k).2 + cellInc s₁ b₁ h w (eulerZZ a y k).1 (eulerZZ a y k).2 k h)

variable {s₁ b₁ h w}

theorem wr_continuous (hw : Continuous w) (j : Fin d) : Continuous (wr w j) :=
  ((EuclideanSpace.proj j).continuous.comp hw).comp continuous_real_toNNReal

end M10b2s

section M10b2w
/-! M10b-2 (random part): the scheme driven by a Brownian path is adapted, continuous, and an
Ito process. Measurability is proved for any monotone family `G` of σ-algebras that sees the
past of `W` (used with `G = completedBrownianPast` and with the ambient σ-algebra). -/

variable {W : ℝ≥0 → Ω → SDEState d} {G : ℝ≥0 → MeasurableSpace Ω}
  {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d} {h : ℝ}

theorem wr_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    {r : ℝ} {t : ℝ≥0} (hr : r.toNNReal ≤ t) (j : Fin d) :
    Measurable[G t] fun ω => wr (fun s => W s ω) j r :=
  hG _ _ hr j

theorem intW_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) {p : ℝ} (hp : 0 ≤ p) {t : ℝ≥0}
    (hpt : p.toNNReal ≤ t) (j : Fin d) :
    Measurable[G t] fun ω => ∫ v in (0 : ℝ)..p, wr (fun s => W s ω) j v := by
  let _ : MeasurableSpace Ω := G t
  have := measurable_intervalIntegral_of_continuous (G t) (H := fun s ω => W s ω j) p.toNNReal
    (fun s hs => hG s t (hs.trans hpt) j)
    (fun ω => (EuclideanSpace.proj j).continuous.comp (hWc ω))
  have e : (p.toNNReal).val = p := Real.coe_toNNReal _ hp
  rw [e] at this
  simpa only [wr] using this

theorem cellIntW_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) {t : ℝ≥0}
    (hqt : q.toNNReal ≤ t) (j : Fin d) :
    Measurable[G t] fun ω => ∫ v in p..q, wr (fun s => W s ω) j v := by
  have hi : ∀ ω (a b : ℝ), IntervalIntegrable (wr (fun s => W s ω) j) volume a b :=
    fun ω a b => (wr_continuous (hWc ω) j).intervalIntegrable a b
  have e : (fun ω => ∫ v in p..q, wr (fun s => W s ω) j v) = fun ω =>
      (∫ v in (0 : ℝ)..q, wr (fun s => W s ω) j v) - ∫ v in (0 : ℝ)..p, wr (fun s => W s ω) j v :=
    funext fun ω => (intervalIntegral.integral_interval_sub_left (hi ω 0 q) (hi ω 0 p)).symm
  rw [e]
  exact (intW_meas_G hG hWc (hp.trans hpq) hqt j).sub
    (intW_meas_G hG hWc hp ((Real.toNNReal_le_toNNReal hpq).trans hqt) j)

theorem cellInc_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hWc : ∀ ω, Continuous fun s => W s ω) (hs : Continuous s₁) (hb : Continuous b₁)
    {t : ℝ≥0} {A Z : Ω → SDEState d} (hA : Measurable[G t] A) (hZ : Measurable[G t] Z)
    {k : ℕ} {r : ℝ} (hk0 : 0 ≤ (k : ℝ) * h) (hr : 0 ≤ r) (ht : ((k : ℝ) * h + r).toNNReal ≤ t) :
    Measurable[G t] fun ω => cellInc s₁ b₁ h (fun s => W s ω) (A ω) (Z ω) k r := by
  have hkt : ((k : ℝ) * h).toNNReal ≤ t := (Real.toNNReal_le_toNNReal (by linarith)).trans ht
  have hsc : ∀ i j, Measurable fun z : SDEState d => s₁ z (i, j) := fun i j =>
    ((EuclideanSpace.proj (i, j)).continuous.comp hs).measurable
  have hbc : ∀ i, Measurable fun z : SDEState d => b₁ z i := fun i =>
    ((EuclideanSpace.proj i).continuous.comp hb).measurable
  have hsA : ∀ i j, Measurable[G t] fun ω => s₁ (A ω) (i, j) := fun i j => (hsc i j).comp hA
  have hsZ : ∀ i j, Measurable[G t] fun ω => s₁ (Z ω) (i, j) := fun i j => (hsc i j).comp hZ
  have hbA : ∀ i, Measurable[G t] fun ω => b₁ (A ω) i := fun i => (hbc i).comp hA
  have hbZ : ∀ i, Measurable[G t] fun ω => b₁ (Z ω) i := fun i => (hbc i).comp hZ
  have h1 := fun j => wr_meas_G (W := W) hG ht j
  have h0 := fun j => wr_meas_G (W := W) hG hkt j
  have hI := fun j => cellIntW_meas_G hG hWc hk0 (le_add_of_nonneg_right hr) ht j
  simp only [cellInc]
  let _ : MeasurableSpace Ω := G t
  refine (WithLp.measurable_toLp 2 (Fin d → ℝ)).comp (measurable_pi_lambda _ fun i => ?_)
  refine ((Finset.measurable_sum _ fun j _ => ?_).add ((hbA i).mul_const _)).add
    ((((hbZ i).sub (hbA i)).mul_const _).div_const _)
  exact ((hsA i j).mul ((h1 j).sub (h0 j))).add
    ((((hsZ i j).sub (hsA i j)).div_const _).mul (((h1 j).const_mul _).sub (hI j)))

theorem eulerZZ_meas_G (hG : ∀ r t : ℝ≥0, r ≤ t → ∀ j, Measurable[G t] fun ω => W r ω j)
    (hGm : Monotone G) (hWc : ∀ ω, Continuous fun s => W s ω) (hh : 0 < h)
    (hs : Continuous s₁) (hb : Continuous b₁) (a y : SDEState d) (k : ℕ) :
    Measurable[G ((k : ℝ) * h).toNNReal]
        (fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1) ∧
      Measurable[G ((k : ℝ) * h).toNNReal]
        (fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2) := by
  induction k with
  | zero => simp only [eulerZZ]; exact ⟨measurable_const, measurable_const⟩
  | succ k ih =>
    have hle : G ((k : ℝ) * h).toNNReal ≤ G (((k + 1 : ℕ) : ℝ) * h).toNNReal :=
      hGm (Real.toNNReal_le_toNNReal (by push_cast; nlinarith))
    refine ⟨ih.2.mono hle le_rfl, ?_⟩
    show Measurable[G (((k + 1 : ℕ) : ℝ) * h).toNNReal] fun ω => (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 +
      cellInc s₁ b₁ h (fun s => W s ω) (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).1
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y k).2 k h
    exact (ih.2.mono hle le_rfl).add (cellInc_meas_G hG hWc hs hb (ih.1.mono hle le_rfl)
      (ih.2.mono hle le_rfl) (by positivity) hh.le
      (le_of_eq (by rw [show (((k + 1 : ℕ) : ℝ) * h) = (k : ℝ) * h + h by push_cast; ring])))

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

end M10c1

section M10c2
/-! M10c-2: the generator of `Gf r` along `(X, Y, A)` and its form inside the `x`-ball. -/

end M10c2

section M10c3
/-! M10c-3: pointwise bounds for the generator `driftH` of `Gf r`. -/

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

/-- Integrand of the cell noise. -/
noncomputable def zetaF (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (j : Fin d) (u : ℝ) (ω : Ω) : ℝ :=
  W (s + h) ω j - W (s + u.toNNReal) ω j

/-- The cell noise. -/
noncomputable def cellZeta (W : ℝ≥0 → Ω → SDEState d) (s h : ℝ≥0) (j : Fin d) (ω : Ω) : ℝ :=
  (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h, zetaF W s h j u ω

end M10d1

section M10d2
/-! M10d-2: one cell of the L² stability estimate: for completed-past-measurable `D` (L²) and
bounded `A, B`, `E‖D + N‖² ≤ E‖D‖² + 2 d h E(‖A‖² + ‖B‖²)` with the cell noise
`N_i = Σⱼ (A_ij ξ_j + B_ij ζ_j)`. -/

theorem state_norm_sq (x : SDEState d) : ‖x‖ ^ 2 = ∑ i, x i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

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

theorem cellInc_eq {W : ℝ≥0 → Ω → SDEState d} (ω : Ω) (hWc : Continuous fun s => W s ω)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (a z : SDEState d) (k : ℕ) :
    cellInc s₁ b₁ (h : ℝ) (fun s => W s ω) a z k h =
      WithLp.toLp 2 (fun i => ∑ j, (s₁ a (i, j) * (W (((k : ℝ) * h).toNNReal + h) ω j -
          W ((k : ℝ) * h).toNNReal ω j) +
        (s₁ z (i, j) - s₁ a (i, j)) * cellZeta W ((k : ℝ) * h).toNNReal h j ω) +
        (h : ℝ) / 2 * (b₁ a i + b₁ z i)) := by
  set s : ℝ≥0 := ((k : ℝ) * h).toNNReal with hs
  have hk0 : (0 : ℝ) ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) h.2
  have hadd : ∀ u : ℝ, 0 ≤ u → ((k : ℝ) * h + u).toNNReal = s + u.toNNReal := fun u hu => by
    rw [Real.toNNReal_add hk0 hu]
  have hw1 : ∀ j, wr (fun s => W s ω) j ((k : ℝ) * h + h) = W (s + h) ω j := fun j => by
    simp only [wr]; rw [hadd _ (NNReal.coe_nonneg h), Real.toNNReal_coe]
  have hw0 : ∀ j, wr (fun s => W s ω) j ((k : ℝ) * h) = W s ω j := fun j => rfl
  have hcont : ∀ j, Continuous fun u : ℝ => W (s + u.toNNReal) ω j := fun j =>
    (EuclideanSpace.proj j).continuous.comp
      (hWc.comp (continuous_const.add continuous_real_toNNReal))
  have hint : ∀ j, ∫ v in ((k : ℝ) * h)..((k : ℝ) * h + h), wr (fun s => W s ω) j v =
      ∫ u in (0 : ℝ)..h, W (s + u.toNNReal) ω j := fun j => by
    have e := intervalIntegral.integral_comp_add_left (fun v => wr (fun s => W s ω) j v)
      ((k : ℝ) * h) (a := 0) (b := h)
    simp only [add_zero] at e
    rw [← e]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by
      rcases Set.mem_uIcc.1 hu with h1 | h1
      · exact h1.1
      · exact (NNReal.coe_nonneg h).trans h1.1
    simp only [wr]; rw [hadd u hu0]
  have hz : ∀ j, cellZeta W s h j ω =
      (1 / (h : ℝ)) * ((h : ℝ) * W (s + h) ω j - ∫ u in (0 : ℝ)..h, W (s + u.toNNReal) ω j) :=
    fun j => by
      unfold cellZeta zetaF
      rw [intervalIntegral.integral_sub intervalIntegrable_const
        ((hcont j).intervalIntegrable _ _), intervalIntegral.integral_const]
      simp [smul_eq_mul]
  unfold cellInc
  congr 1
  funext i
  have hsum : ∑ j, (s₁ a (i, j) * (wr (fun s => W s ω) j ((k : ℝ) * h + h) -
        wr (fun s => W s ω) j ((k : ℝ) * h)) + (s₁ z (i, j) - s₁ a (i, j)) / h *
        ((h : ℝ) * wr (fun s => W s ω) j ((k : ℝ) * h + h) -
          ∫ v in ((k : ℝ) * h)..((k : ℝ) * h + h), wr (fun s => W s ω) j v)) =
      ∑ j, (s₁ a (i, j) * (W (s + h) ω j - W s ω j) +
        (s₁ z (i, j) - s₁ a (i, j)) * cellZeta W s h j ω) :=
    Finset.sum_congr rfl fun j _ => by
      rw [hw1 j, hw0 j, hint j, hz j]; field_simp
  rw [hsum]
  field_simp
  ring

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

/-- Noise of one cell: `(ξ, ζ)`. -/
abbrev Noise (d : ℕ) := (Fin d → ℝ) × (Fin d → ℝ)

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d) (h : ℝ)

/-- One step of the scheme in noise form. -/
noncomputable def zstep (p : SDEState d × SDEState d) (n : Noise d) : SDEState d :=
  p.2 + WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * n.1 j +
    (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * n.2 j) + h / 2 * (b₁ p.1 i + b₁ p.2 i))

/-- The scheme as a recursion on pairs driven by a noise sequence. -/
noncomputable def zrec (N : ℕ → Noise d) : ℕ → SDEState d × SDEState d → SDEState d × SDEState d
  | 0, p => p
  | k + 1, p => ((zrec N k p).2, zstep s₁ b₁ h (zrec N k p) (N k))

variable {s₁ b₁ h}

/-- Noises of the cells `m, m+1, ...` of the scheme driven by `W`. -/
noncomputable def noiseAt (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0) (m : ℕ) (ω : Ω) (l : ℕ) : Noise d :=
  (fun j => W ((((m + l : ℕ) : ℝ) * h).toNNReal + h) ω j - W (((m + l : ℕ) : ℝ) * h).toNNReal ω j,
    fun j => cellZeta W (((m + l : ℕ) : ℝ) * h).toNNReal h j ω)

theorem eulerZZ_eq_zrec {W : ℝ≥0 → Ω → SDEState d} (ω : Ω) (hWc : Continuous fun s => W s ω)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (a y : SDEState d) (m k : ℕ) :
    eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k) =
      zrec s₁ b₁ h (noiseAt W h m ω) k (eulerZZ s₁ b₁ h (fun s => W s ω) a y m) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show ((eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2,
        (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2 +
          cellInc s₁ b₁ h (fun s => W s ω) (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).1
            (eulerZZ s₁ b₁ h (fun s => W s ω) a y (m + k)).2 (m + k) h) = _
    rw [cellInc_eq ω hWc hh, ih]
    rfl

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

-- ===== CB =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CB (CORE route C2, s22): Cameron-Martin shift formula for centered Gaussians, one-dimensional
and for finite independent families (`Measure.pi`). -/

end ItoLib

-- ===== CC =====
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

-- ===== CD =====
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

-- ===== CE =====
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

/-- Average diffusion matrix of a pair applied to `u`. -/
noncomputable def avgApply (p : SDEState d × SDEState d) (u : Fin d → ℝ) : SDEState d :=
  WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) + s₁ p.2 (i, j)) / 2 * u j)

variable (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)

variable {s₁ b₁ h J m}

end C4a

end ItoLib

-- ===== CF =====
open Filter Set
open scoped BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CORE route C4b (s23): the steered second-moment recursion. If
`e_{k+1} ≤ (1 - 1/(m-k))² e_k + c h (e_k + e_{k-1})` (with `e_{-1}` given by `e' 0`), then
`e_k ≤ G ((m-k)/m)² (1 + 13 c h)^k` for `k < m`. Key fact: `(j+1)² + (j+2)² ≤ 13 j²` for `j ≥ 1`. -/

end ItoLib

-- ===== CG =====
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

-- ===== CH =====
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

-- ===== CI =====
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

-- ===== CK =====
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

-- ===== CL =====
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

/-- Right inverse of `avgApply s p` for `s x (i, j) = a i x * Γ j i`. -/
noncomputable def jInv (a : Fin d → SDEState d → ℝ) (Γ : Matrix (Fin d) (Fin d) ℝ)
    (p : SDEState d × SDEState d) (v : SDEState d) : Fin d → ℝ :=
  (Γ.transpose)⁻¹.mulVec (fun i => 2 * v i / (a i p.1 + a i p.2))

theorem jInv_right {s : SDEState d → SDEDiffusion d} {a : Fin d → SDEState d → ℝ}
    {Γ : Matrix (Fin d) (Fin d) ℝ} (hsa : ∀ x i j, s x (i, j) = a i x * Γ j i)
    (hΓ : IsUnit Γ.det) (ha : ∀ i x y, a i x + a i y ≠ 0) (p : SDEState d × SDEState d)
    (v : SDEState d) : avgApply s p (jInv a Γ p v) = v := by
  ext i
  have hT : Γ.transpose.mulVec (jInv a Γ p v) = fun i => 2 * v i / (a i p.1 + a i p.2) := by
    unfold jInv
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose]),
      Matrix.one_mulVec]
  have e : ∑ j, (s p.1 (i, j) + s p.2 (i, j)) / 2 * jInv a Γ p v j =
      (a i p.1 + a i p.2) / 2 * (Γ.transpose.mulVec (jInv a Γ p v)) i := by
    simp only [hsa, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  show ∑ j, (s p.1 (i, j) + s p.2 (i, j)) / 2 * jInv a Γ p v j = v i
  rw [e, hT]
  have := ha i p.1 p.2
  field_simp

theorem jInv_measurable {a : Fin d → SDEState d → ℝ} (Γ : Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i, Measurable (a i)) : Measurable (Function.uncurry (jInv a Γ)) := by
  refine measurable_pi_lambda _ fun k => ?_
  simp only [Function.uncurry, jInv, Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun i _ => measurable_const.mul ?_
  exact (measurable_const.mul ((EuclideanSpace.proj i).continuous.measurable.comp
    measurable_snd)).div (((ha i).comp (measurable_fst.comp measurable_fst)).add
      ((ha i).comp (measurable_snd.comp measurable_fst)))

theorem jInv_bound {a : Fin d → SDEState d → ℝ} (Γ : Matrix (Fin d) (Fin d) ℝ) {κ : ℝ}
    (hκ : 0 < κ) (ha : ∀ i x y, κ ≤ |a i x + a i y|) (p : SDEState d × SDEState d)
    (v : SDEState d) :
    ∑ j, jInv a Γ p v j ^ 2 ≤
      (2 * Real.sqrt (∑ j, ∑ k, (Γ.transpose)⁻¹ j k ^ 2) / κ) ^ 2 * ‖v‖ ^ 2 := by
  set M := (Γ.transpose)⁻¹ with hM
  set w : Fin d → ℝ := fun i => 2 * v i / (a i p.1 + a i p.2) with hw
  have hJ : ∀ j, jInv a Γ p v j = ∑ k, M j k * w k := fun j => rfl
  have hw2 : ∀ k, w k ^ 2 ≤ 4 / κ ^ 2 * v k ^ 2 := fun k => by
    have h1 : κ ^ 2 ≤ (a k p.1 + a k p.2) ^ 2 := by
      have := pow_le_pow_left₀ hκ.le (ha k p.1 p.2) 2
      rwa [sq_abs] at this
    have hκ2 : 0 < κ ^ 2 := by positivity
    rw [hw]
    simp only
    rw [div_pow, mul_pow, div_mul_eq_mul_div]
    norm_num
    exact div_le_div_of_nonneg_left (by positivity) hκ2 h1
  have hW : ∑ k, w k ^ 2 ≤ 4 / κ ^ 2 * ‖v‖ ^ 2 := by
    rw [state_norm_sq, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => hw2 k
  simp_rw [hJ]
  calc ∑ j, (∑ k, M j k * w k) ^ 2 ≤ ∑ j, ((∑ k, M j k ^ 2) * ∑ k, w k ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ j, ∑ k, M j k ^ 2) * ∑ k, w k ^ 2 := by rw [Finset.sum_mul]
    _ ≤ (∑ j, ∑ k, M j k ^ 2) * (4 / κ ^ 2 * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hW (Finset.sum_nonneg fun j _ =>
          Finset.sum_nonneg fun k _ => sq_nonneg _)
    _ = (2 * Real.sqrt (∑ j, ∑ k, M j k ^ 2) / κ) ^ 2 * ‖v‖ ^ 2 := by
        have hT0 : (0 : ℝ) ≤ ∑ j, ∑ k, M j k ^ 2 :=
          Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => sq_nonneg _
        rw [div_pow, mul_pow, Real.sq_sqrt hT0]
        ring

end C5d
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

theorem stay_eq {X : ℝ≥0 → Ω → SDEState d} (hc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0)
    (R : ℝ) :
    {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R} = ⋂ q : ℚ, {ω | ‖X (min (q : ℝ).toNNReal T) ω‖ ≤ R} := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · exact fun H q => H _ (min_le_right _ _)
  · intro H s hs
    have hg : Continuous fun r : ℝ => ‖X (min r.toNNReal T) ω‖ :=
      continuous_norm.comp ((hc ω).comp (continuous_real_toNNReal.min continuous_const))
    have hcl : IsClosed {r : ℝ | ‖X (min r.toNNReal T) ω‖ ≤ R} := isClosed_le hg continuous_const
    have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    have hsub : Set.range ((↑) : ℚ → ℝ) ⊆ {r : ℝ | ‖X (min r.toNNReal T) ω‖ ≤ R} := by
      rintro _ ⟨q, rfl⟩; exact H q
    have := hcl.closure_subset_iff.2 hsub (hd.closure_eq ▸ Set.mem_univ (s : ℝ))
    simpa [Real.toNNReal_coe, min_eq_left hs] using this

theorem stay_measurableSet {X : ℝ≥0 → Ω → SDEState d} (hm : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0) (R : ℝ) :
    MeasurableSet {ω | ∀ s ≤ T, ‖X s ω‖ ≤ R} := by
  rw [stay_eq hc T R]
  exact MeasurableSet.iInter fun q =>
    measurableSet_le (continuous_norm.measurable.comp (hm _)) measurable_const

theorem exit_tendsto {P : Measure Ω} [IsFiniteMeasure P] {X : ℝ≥0 → Ω → SDEState d}
    (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous fun t => X t ω) (T : ℝ≥0) :
    Tendsto (fun R : ℕ => P {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ) atTop (𝓝 0) := by
  have hmono : Antitone fun R : ℕ => {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ := by
    intro R R' hR
    refine Set.compl_subset_compl.2 fun ω hω s hs => (hω s hs).trans (by exact_mod_cast hR)
  have hemp : ⋂ R : ℕ, {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω
    rw [Set.mem_iInter] at hω
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hc ω).continuousOn
    obtain ⟨R, hR⟩ := exists_nat_ge C
    exact hω R fun s hs => (hC s ⟨zero_le, hs⟩).trans hR
  have := tendsto_measure_iInter_atTop (μ := P)
    (fun R : ℕ => (stay_measurableSet hm hc T (R : ℝ)).compl.nullMeasurableSet) hmono
    ⟨0, measure_ne_top _ _⟩
  rwa [hemp, measure_empty] at this

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

-- ===== CM =====
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

/-- Entrywise Lipschitz functions read through a bounded 1-Lipschitz map are globally Lipschitz
and bounded as vectors. -/
theorem boxed_vec_lip {ι : Type*} [Fintype ι] (φ : ι → SDEState n → ℝ) {β : ℝ}
    (hφ : ∀ k, ∃ L, 0 ≤ L ∧ ∀ u v : SDEState n, (∀ l, |u l| ≤ β) → (∀ l, |v l| ≤ β) →
      |φ k u - φ k v| ≤ L * ‖u - v‖)
    (π : SDEState n → SDEState n) (hπ : ∀ x l, |π x l| ≤ β)
    (hπL : ∀ x y, ‖π x - π y‖ ≤ ‖x - y‖) :
    ∃ L S : ℝ, 0 ≤ L ∧ ∀ x y : SDEState n,
      ‖(WithLp.toLp 2 (fun k => φ k (π x)) : EuclideanSpace ℝ ι) -
        WithLp.toLp 2 (fun k => φ k (π y))‖ ≤ L * ‖x - y‖ ∧
      ‖(WithLp.toLp 2 (fun k => φ k (π x)) : EuclideanSpace ℝ ι)‖ ≤ S := by
  choose L hL0 hL using hφ
  refine ⟨∑ k, L k, ∑ k, (L k * (n * (2 * β)) + |φ k (π 0)|),
    Finset.sum_nonneg fun k _ => hL0 k, fun x y => ⟨?_, ?_⟩⟩
  · calc _ ≤ ∑ k, |((WithLp.toLp 2 (fun k => φ k (π x)) : EuclideanSpace ℝ ι) -
          WithLp.toLp 2 (fun k => φ k (π y))) k| := euc_norm_le_sum' _
      _ ≤ ∑ k, L k * ‖x - y‖ := Finset.sum_le_sum fun k _ => by
          simp only [PiLp.sub_apply, PiLp.toLp_apply]
          exact (hL k _ _ (hπ x) (hπ y)).trans (mul_le_mul_of_nonneg_left (hπL x y) (hL0 k))
      _ = (∑ k, L k) * ‖x - y‖ := by rw [Finset.sum_mul]
  · calc _ ≤ ∑ k, |(WithLp.toLp 2 (fun k => φ k (π x)) : EuclideanSpace ℝ ι) k| :=
          euc_norm_le_sum' _
      _ ≤ ∑ k, (L k * (n * (2 * β)) + |φ k (π 0)|) := Finset.sum_le_sum fun k _ => by
          simp only [PiLp.toLp_apply]
          have h1 := hL k _ _ (hπ x) (hπ 0)
          have h2 : ‖π x - π 0‖ ≤ n * (2 * β) := norm_le_card_mul fun l => by
            rw [PiLp.sub_apply]
            have := abs_sub (π x l) (π 0 l)
            linarith [hπ x l, hπ 0 l]
          have h3 := abs_sub_abs_le_abs_sub (φ k (π x)) (φ k (π 0))
          nlinarith [mul_le_mul_of_nonneg_left h2 (hL0 k)]

open StochKolmogorov.Persist

/-- The diagonal factor of the boxed diffusion. -/
noncomputable def aK (C : Coeffs n) (α β : ℝ) (i : Fin n) (x : SDEState n) : ℝ :=
  boxP α β x i * C.g i (posPart (boxP α β x))

/-- Boxed Kolmogorov diffusion and drift. -/
noncomputable def sK (C : Coeffs n) (α β : ℝ) (x : SDEState n) : SDEDiffusion n :=
  diffusion C (0, boxP α β x)

noncomputable def bK (C : Coeffs n) (α β : ℝ) (x : SDEState n) : SDEState n :=
  drift C (0, boxP α β x)

theorem sK_apply (C : Coeffs n) (α β : ℝ) (x : SDEState n) (i j : Fin n) :
    sK C α β x (i, j) = aK C α β i x * C.Γ j i := rfl

theorem kolm_box (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {α β : ℝ} (hα : 0 ≤ α) (hαβ : α ≤ β) :
    Continuous (sK C α β) ∧ Continuous (bK C α β) ∧ ∃ S L : ℝ, 0 ≤ L ∧
      (∀ x, ‖sK C α β x‖ ≤ S ∧ ‖bK C α β x‖ ≤ S) ∧
      (∀ x y, ‖sK C α β x - sK C α β y‖ ≤ L * ‖x - y‖ ∧
        ‖bK C α β x - bK C α β y‖ ≤ L * ‖x - y‖) := by
  have hβ : 0 ≤ β := hα.trans hαβ
  have hπ : ∀ x l, |boxP (n := n) α β x l| ≤ β := fun x l => by
    obtain ⟨h1, h2⟩ := boxP_mem hαβ x l
    rw [abs_of_nonneg (hα.trans h1)]; exact h2
  obtain ⟨L1, S1, hL1, h1⟩ := boxed_vec_lip
    (fun ij : Fin n × Fin n => fun u : SDEState n => u ij.1 * C.g ij.1 (posPart u) * C.Γ ij.2 ij.1)
    (β := β) (fun ij => prod_box_lip (hC ij.1).2 (C.Γ ij.2 ij.1) ij.1 hβ) (boxP α β) hπ
    (boxP_lip α β)
  obtain ⟨L2, S2, hL2, h2⟩ := boxed_vec_lip
    (fun i : Fin n => fun u : SDEState n => u i * C.f i (posPart u))
    (β := β) (fun i => by
      obtain ⟨L, hL, hLb⟩ := prod_box_lip (hC i).1 1 i hβ
      exact ⟨L, hL, fun u v hu hv => by simpa only [mul_one] using hLb u v hu hv⟩)
    (boxP α β) hπ (boxP_lip α β)
  have hs : ∀ x y, ‖sK C α β x - sK C α β y‖ ≤ L1 * ‖x - y‖ := fun x y => (h1 x y).1
  have hb : ∀ x y, ‖bK C α β x - bK C α β y‖ ≤ L2 * ‖x - y‖ := fun x y => (h2 x y).1
  refine ⟨LipschitzWith.continuous (K := L1.toNNReal) (LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL1]; exact hs x y),
    LipschitzWith.continuous (K := L2.toNNReal) (LipschitzWith.of_dist_le_mul fun x y => by
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL2]; exact hb x y),
    S1 + S2, L1 + L2, by positivity, fun x => ⟨?_, ?_⟩, fun x y => ⟨?_, ?_⟩⟩
  · have := (h1 x x).2; have := (h2 x x).2
    have : ‖bK C α β x‖ ≤ S2 := (h2 x x).2
    have : 0 ≤ ‖bK C α β x‖ := norm_nonneg _
    have : ‖sK C α β x‖ ≤ S1 := (h1 x x).2
    linarith
  · have : ‖sK C α β x‖ ≤ S1 := (h1 x x).2
    have : 0 ≤ ‖sK C α β x‖ := norm_nonneg _
    have : ‖bK C α β x‖ ≤ S2 := (h2 x x).2
    linarith
  · have := hs x y; nlinarith [norm_nonneg (x - y)]
  · have := hb x y; nlinarith [norm_nonneg (x - y)]

/-- The box `[α, β]^n`. -/
def boxSet (α β : ℝ) : Set (SDEState n) := {u | ∀ l, α ≤ u l ∧ u l ≤ β}

theorem boxSet_convex (α β : ℝ) : Convex ℝ (boxSet (n := n) α β) := by
  refine fun x hx y hy a b ha hb hab => fun l => ?_
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  obtain ⟨h1, h2⟩ := hx l
  obtain ⟨h3, h4⟩ := hy l
  have e1 : a * α + b * α = α := by rw [← add_mul, hab, one_mul]
  have e2 : a * β + b * β = β := by rw [← add_mul, hab, one_mul]
  exact ⟨by linarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h3 hb],
    by linarith [mul_le_mul_of_nonneg_left h2 ha, mul_le_mul_of_nonneg_left h4 hb]⟩

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

theorem posPart_of_orthant {u : SDEState n} (hu : u ∈ orthant n) : posPart u = u := by
  ext l; rw [posPart_apply']; exact max_eq_left (hu l)

/-- Assumption 1.1 part 1 makes `aK` uniformly separated from `0` with a fixed sign per
coordinate, so `|aK i x + aK i y| ≥ κ`. -/
theorem aK_sep (C : Coeffs n)
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef)
    (hgc : ∀ i, ContinuousOn (C.g i) (orthant n)) {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ κ > 0, ∀ i x y, κ ≤ |aK C α β i x + aK C α β i y| := by
  set B : Set (SDEState n) := boxSet α β with hBdef
  have hBo : B ⊆ orthant n := fun u hu l => hα.le.trans (hu l).1
  have hBc : IsCompact B := boxSet_isCompact hα.le
  have hBp : IsPreconnected B := (boxSet_convex α β).isPreconnected
  have hBn : (WithLp.toLp 2 (fun _ => α) : SDEState n) ∈ B := fun l => ⟨le_rfl, hαβ⟩
  have hne : ∀ i, ∀ u ∈ orthant n, C.g i u ≠ 0 := fun i u hu e => by
    have := (hpd u hu).diag_pos (i := i)
    simp [e] at this
  have hsign : ∀ i, ∃ m > (0 : ℝ), (∀ u ∈ B, m ≤ C.g i u) ∨ (∀ u ∈ B, C.g i u ≤ -m) := by
    intro i
    have hgB : ContinuousOn (C.g i) B := (hgc i).mono hBo
    obtain ⟨u0, hu0, hmin⟩ := hBc.exists_isMinOn ⟨_, hBn⟩ (continuous_abs.comp_continuousOn hgB)
    have hm : 0 < |C.g i u0| := abs_pos.2 (hne i u0 (hBo hu0))
    have hle : ∀ u ∈ B, |C.g i u0| ≤ |C.g i u| := fun u hu => hmin hu
    refine ⟨|C.g i u0|, hm, ?_⟩
    rcases lt_or_gt_of_ne (hne i u0 (hBo hu0)) with hneg | hpos
    · right
      intro u hu
      have hu' : C.g i u < 0 := by
        by_contra hc
        push Not at hc
        obtain ⟨z, hz, hz0⟩ := hBp.intermediate_value hu0 hu hgB ⟨hneg.le, hc⟩
        exact hne i z (hBo hz) hz0
      have := hle u hu
      rw [abs_of_neg hu'] at this
      linarith
    · left
      intro u hu
      have hu' : 0 < C.g i u := by
        by_contra hc
        push Not at hc
        obtain ⟨z, hz, hz0⟩ := hBp.intermediate_value hu hu0 hgB ⟨hc, hpos.le⟩
        exact hne i z (hBo hz) hz0
      have := hle u hu
      rw [abs_of_pos hu'] at this
      linarith
  choose m hm0 hm using hsign
  have hT : 0 ≤ ∑ i, 1 / m i := Finset.sum_nonneg fun i _ => by have := hm0 i; positivity
  refine ⟨2 * α / (1 + ∑ i, 1 / m i), by positivity, fun i x y => ?_⟩
  have hκ : 2 * α / (1 + ∑ i, 1 / m i) ≤ 2 * α * m i := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 / m i ≤ ∑ j, 1 / m j :=
      Finset.single_le_sum (f := fun j => 1 / m j) (fun j _ => by have := hm0 j; positivity)
        (Finset.mem_univ i)
    have h2 : m i * (1 / m i) = 1 := by field_simp [(hm0 i).ne']
    have h3 := hm0 i
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le]
  refine hκ.trans ?_
  have hx := boxP_mem_boxSet (n := n) hαβ x
  have hy := boxP_mem_boxSet (n := n) hαβ y
  have ex : aK C α β i x = boxP α β x i * C.g i (boxP α β x) := by
    rw [aK, posPart_of_orthant (hBo hx)]
  have ey : aK C α β i y = boxP α β y i * C.g i (boxP α β y) := by
    rw [aK, posPart_of_orthant (hBo hy)]
  rw [ex, ey]
  have hxi := (hx i).1
  have hyi := (hy i).1
  rcases hm i with hp | hn
  · have a1 := hp _ hx; have a2 := hp _ hy
    rw [abs_of_pos (by nlinarith [hm0 i])]
    nlinarith [hm0 i]
  · have a1 := hn _ hx; have a2 := hn _ hy
    rw [abs_of_neg (by nlinarith [hm0 i])]
    nlinarith [hm0 i]

theorem aK_continuous (C : Coeffs n) (hgc : ∀ i, ContinuousOn (C.g i) (orthant n)) (α β : ℝ)
    (i : Fin n) : Continuous (aK C α β i) := by
  have hpc : Continuous fun x : SDEState n => posPart (boxP α β x) :=
    continuous_posPart.comp (boxP_continuous α β)
  exact ((PiLp.continuous_apply 2 _ i).comp (boxP_continuous α β)).mul
    ((hgc i).comp_continuous hpc fun x => posPart_mem_orthant _)

end C5dK
end ItoLib

-- ===== CN =====
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

open StochKolmogorov.Persist in
theorem gamma_isUnit {n : ℕ} (C : Coeffs n)
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef) :
    IsUnit C.Γ.det := by
  have h0 : (0 : SDEState n) ∈ orthant n := fun l => by simp
  have hP := (hpd 0 h0).det_pos
  set D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i => C.g i 0) with hD
  have heq : (Matrix.of fun i j => C.g i 0 * C.g j 0 * C.sig i j) =
      D * (C.Γ.transpose * C.Γ) * D := by
    ext i j
    simp only [hD, Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Coeffs.sig]
    ring
  rw [heq, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hP
  rw [isUnit_iff_ne_zero]
  intro hz
  rw [hz] at hP
  simp at hP

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0} {A B : ℕ → Ω → SDEDiffusion d}

end C5g
end ItoLib

-- ===== CO =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5t
/-! CORE route, s27: tracking estimate for the steered coupling. With `D_k = X_k - Ŷ_k`,
`D_k - ((m-k)/m) D_0 = (m-k) (Σ_{l<k} w_l Δb_l + gmart_k)` (weights `w_l = 1/(m-l-1)`), so a
maximal inequality on `gmart` plus a second-moment bound on the drift sum control
`max_{k ≤ m-1} ‖D_k - ((m-k)/m) D_0‖`. -/

variable (s₁ : SDEState d → SDEDiffusion d) (b₁ : SDEState d → SDEState d)
  (J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)) (m : ℕ)
  (W : ℝ≥0 → Ω → SDEState d) (h : ℝ≥0)
  (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d))

variable {s₁ b₁ J m}

end C5t
end ItoLib

-- ===== CP =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*} {d : ℕ}

section C5u
/-! CORE route, s28: explicit O(T) form of the tracking estimate (T = m h). -/

variable {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}
  {W : ℝ≥0 → Ω → SDEState d} {h : ℝ≥0}

end C5u
end ItoLib

-- ===== CQ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5v
/-! CORE route, s28: discrete Girsanov for PATH events. The law of the plain path from `q₀.2` on a
path set `Ap` is at least `e^{-a}` times the probability that the STEERED path `Ŷ_k = (cq k).2.2`
lies in `Ap`, minus the entropy term. -/

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C5v
end ItoLib

-- ===== CR =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5w
/-! CORE route, s28: finite-`h` lower bound for the plain chain from `q₀.2` on the PATH event
"ends in `A` and stays in `Bx`", in terms of the chain from `q₀.1` ending in `B` (`B` sits `ε` inside
`A`; `Bx` contains the `2δ`-neighbourhood of the segment from `q₀.1.2` to `q₀.2.2`). -/

variable {d : ℕ} {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
  {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

end C5w
end ItoLib

-- ===== CJ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5b
/-! CORE route C5b (s25): two Euler chains whose coefficients agree on a set `N` coincide as long
as one of them stays in `N` (used to replace the ball-localised coefficients of
`euler_close_tendsto` by the nondegenerate `σ ∘ π_N` of the steering). -/

variable {d : ℕ}

end C5b

end ItoLib

-- ===== CS =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5x
/-! CORE route, s28: transfer of `steer_lower_box` (stated for the box coefficients `s₂, b₂`)
to coefficients `s₁, b₁` that agree with `s₂, b₂` on the box `N`. -/

variable {d : ℕ}

variable {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} {m : ℕ}

/-- Finite-`h` minorisation for chains with coefficients `s₁, b₁` started at `(x,x)` and `(y,y)`,
via the box coefficients `s₂, b₂` (nondegenerate: right inverse `J`). -/
theorem steer_lower_s1 [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) {h : ℝ≥0}
    (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) (x y : SDEState d) (hm2 : 2 ≤ m) {G : ℝ}
    (hG : ‖x - y‖ ^ 2 ≤ G)
    {δ ε a : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ) (ha : 0 < a)
    (hT : m * (h * S) ≤ δ / 2)
    {A B : Set (SDEState d)} (hA : MeasurableSet A)
    (hB : ∀ z ∈ B, ∀ z', ‖z' - z‖ < ε → z' ∈ A)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx) :
    Real.exp (-a) * (P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2 ∈ B} -
        2 * (16 * d * S ^ 2 * (m * h) / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
          (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2 -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
          (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 / ε ^ 2 -
        (Λ ^ 2 * (G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m) / (2 * h) + 1) / a) ≤
      P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (y, y)).2 ∈ A} := by
  exact EthierKurtz.euler_chain_steer_minorisation hW hh hh1 hs hb hJm hJ hL hSg hLg hΛ hag hBxN
    hBxm x y hm2 hG hδ hε hεδ ha hT hA hB hBx (fun u ω k => zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) k (u, u))
    (fun _ _ => rfl) (fun u ω k => by simp only [zrec, zstep, noiseAt, cellZeta, zetaF, zero_add])
end C5x
end ItoLib

-- ===== CTZ =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5y
/-! CORE route, s28 (C5e): the `h → 0` limit. The chains of `steer_lower_s1` are compared with the
SDE solutions through `euler_close_tendsto`; the result is a minorisation of `P(X^y_T ∈ F)` by
`P(X^x_T ∈ F_{4ρ})` (`F_r = {z | ball z r ⊆ F}`) up to explicit errors that are small for small `T`. -/

variable {d : ℕ}

/-- `F_r = {z | ball z r ⊆ F}` is closed. -/
theorem inner_set_isClosed (F : Set (SDEState d)) (r : ℝ) :
    IsClosed {z : SDEState d | Metric.ball z r ⊆ F} := by
  rw [← isOpen_compl_iff]
  have e : {z : SDEState d | Metric.ball z r ⊆ F}ᶜ = ⋃ w ∈ Fᶜ, Metric.ball w r := by
    ext z
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_iUnion, Set.not_subset,
      Metric.mem_ball, exists_prop]
    constructor
    · rintro ⟨w, hw, hwF⟩; exact ⟨w, hwF, by rw [dist_comm]; exact hw⟩
    · rintro ⟨w, hwF, hw⟩; exact ⟨w, by rw [dist_comm]; exact hw, hwF⟩
  rw [e]
  exact isOpen_biUnion fun w _ => Metric.isOpen_ball

theorem pow_E_le {c h : ℝ} (hc : 0 ≤ c) (hh : 0 ≤ h) (m : ℕ) :
    (1 + 13 * c * h) ^ m ≤ Real.exp (13 * c * (m * h)) := by
  have h1 : 1 + 13 * c * h ≤ Real.exp (13 * c * h) := by
    have := Real.add_one_le_exp (13 * c * h); linarith
  calc (1 + 13 * c * h) ^ m ≤ Real.exp (13 * c * h) ^ m :=
        pow_le_pow_left₀ (by positivity) h1 m
    _ = Real.exp (13 * c * (m * h)) := by rw [← Real.exp_nat_mul]; ring_nf

/-- Lipschitz cutoff of a set: `1` on `B`, `0` at distance `≥ ρ` from `B`. -/
noncomputable def bCut (B : Set (SDEState d)) (ρ : ℝ) (z : SDEState d) : ℝ :=
  max 0 (1 - Metric.infDist z B / ρ)

theorem bCut_continuous (B : Set (SDEState d)) (ρ : ℝ) : Continuous (bCut B ρ) := by
  show Continuous fun z => max 0 (1 - Metric.infDist z B / ρ)
  exact continuous_const.max (continuous_const.sub ((Metric.continuous_infDist_pt B).div_const ρ))

theorem bCut_abs_le (B : Set (SDEState d)) {ρ : ℝ} (hρ : 0 < ρ) (z : SDEState d) :
    |bCut B ρ z - 1 / 2| ≤ 1 / 2 := by
  have h0 : 0 ≤ Metric.infDist z B / ρ := div_nonneg Metric.infDist_nonneg hρ.le
  have h1 : 0 ≤ bCut B ρ z := le_max_left _ _
  have h2 : bCut B ρ z ≤ 1 := max_le zero_le_one (by linarith)
  rw [abs_le]
  constructor <;> linarith

theorem bCut_lip (B : Set (SDEState d)) {ρ : ℝ} (hρ : 0 < ρ) (z z' : SDEState d) :
    |bCut B ρ z - bCut B ρ z'| ≤ ρ⁻¹ * ‖z - z'‖ := by
  unfold bCut
  rw [max_comm 0, max_comm 0]
  refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
  have e1 := Metric.infDist_le_infDist_add_dist (s := B) (x := z) (y := z')
  have e2 := Metric.infDist_le_infDist_add_dist (s := B) (x := z') (y := z)
  rw [dist_eq_norm] at e1
  rw [dist_comm, dist_eq_norm] at e2
  have e : 1 - Metric.infDist z B / ρ - (1 - Metric.infDist z' B / ρ) =
      ρ⁻¹ * (Metric.infDist z' B - Metric.infDist z B) := by ring
  rw [e, abs_mul, abs_of_pos (inv_pos.2 hρ)]
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hρ).le
  rw [abs_le]
  constructor <;> linarith

/-- Cutoff transfer: `P(A ∈ B) ≤ P(A' ∈ U) + E|φ(A') - φ(A)|` when `U` contains the `ρ`-neighbourhood of `B`. -/
theorem cut_transfer [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B U : Set (SDEState d)} {ρ : ℝ} (hρ : 0 < ρ) (hBm : MeasurableSet B) (hUm : MeasurableSet U)
    (hBU : ∀ w b, b ∈ B → dist w b < ρ → w ∈ U) {A A' : Ω → SDEState d}
    (hA : Measurable A) (hA' : Measurable A') :
    P.real {ω | A ω ∈ B} ≤ P.real {ω | A' ω ∈ U} +
      ∫ ω, |(bCut B ρ (A' ω) - 1 / 2) - (bCut B ρ (A ω) - 1 / 2)| ∂P := by
  have hc := (bCut_continuous B ρ).measurable
  have hS1 : MeasurableSet {ω | A ω ∈ B} := hA hBm
  have hS2 : MeasurableSet {ω | A' ω ∈ U} := hA' hUm
  have hgm : Measurable fun ω => |(bCut B ρ (A' ω) - 1 / 2) - (bCut B ρ (A ω) - 1 / 2)| :=
    continuous_abs.measurable.comp (((hc.comp hA').sub_const _).sub ((hc.comp hA).sub_const _))
  have hgi : Integrable (fun ω => |(bCut B ρ (A' ω) - 1 / 2) - (bCut B ρ (A ω) - 1 / 2)|) P := by
    refine (integrable_const (1 : ℝ)).mono' hgm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    obtain ⟨a1, a2⟩ := abs_le.1 (bCut_abs_le B hρ (A' ω))
    obtain ⟨b1, b2⟩ := abs_le.1 (bCut_abs_le B hρ (A ω))
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    constructor <;> linarith
  have hpt : ∀ ω, {ω | A ω ∈ B}.indicator (1 : Ω → ℝ) ω ≤ {ω | A' ω ∈ U}.indicator (1 : Ω → ℝ) ω +
      |(bCut B ρ (A' ω) - 1 / 2) - (bCut B ρ (A ω) - 1 / 2)| := by
    intro ω
    have hi2 : 0 ≤ {ω | A' ω ∈ U}.indicator (1 : Ω → ℝ) ω :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) _
    by_cases hb : A ω ∈ B
    · have h1 : bCut B ρ (A ω) = 1 := by
        unfold bCut
        rw [Metric.infDist_zero_of_mem hb, zero_div, sub_zero]
        exact max_eq_right zero_le_one
      rw [Set.indicator_of_mem (show ω ∈ {ω | A ω ∈ B} from hb), Pi.one_apply]
      by_cases hu : A' ω ∈ U
      · rw [Set.indicator_of_mem (show ω ∈ {ω | A' ω ∈ U} from hu), Pi.one_apply]
        linarith [abs_nonneg ((bCut B ρ (A' ω) - 1 / 2) - (bCut B ρ (A ω) - 1 / 2))]
      · have h0 : bCut B ρ (A' ω) = 0 := by
          unfold bCut
          refine max_eq_left ?_
          have hle : ρ ≤ Metric.infDist (A' ω) B := by
            by_contra hlt
            obtain ⟨b, hbB, hdb⟩ := (Metric.infDist_lt_iff ⟨_, hb⟩).1 (not_le.1 hlt)
            exact hu (hBU _ b hbB hdb)
          rw [sub_nonpos, le_div_iff₀ hρ]
          linarith
        rw [h0, h1]
        norm_num
        exact hi2
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | A ω ∈ B} from hb)]
      exact add_nonneg hi2 (abs_nonneg _)
  have hi1 : Integrable ({ω | A ω ∈ B}.indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hS1
  have hi2 : Integrable ({ω | A' ω ∈ U}.indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hS2
  calc P.real {ω | A ω ∈ B} = ∫ ω, {ω | A ω ∈ B}.indicator (1 : Ω → ℝ) ω ∂P :=
        (integral_indicator_one hS1).symm
    _ ≤ ∫ ω, ({ω | A' ω ∈ U}.indicator (1 : Ω → ℝ) ω +
          |(bCut B ρ (A' ω) - 1 / 2) - (bCut B ρ (A ω) - 1 / 2)|) ∂P :=
        integral_mono hi1 (hi2.add hgi) hpt
    _ = _ := by rw [integral_add hi2 hgi, integral_indicator_one hS2]

/-- `cut_transfer` with the integrand written the other way round. -/
theorem cut_transfer' [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B U : Set (SDEState d)} {ρ : ℝ} (hρ : 0 < ρ) (hBm : MeasurableSet B) (hUm : MeasurableSet U)
    (hBU : ∀ w b, b ∈ B → dist w b < ρ → w ∈ U) {A A' : Ω → SDEState d}
    (hA : Measurable A) (hA' : Measurable A') :
    P.real {ω | A ω ∈ B} ≤ P.real {ω | A' ω ∈ U} +
      ∫ ω, |(bCut B ρ (A ω) - 1 / 2) - (bCut B ρ (A' ω) - 1 / 2)| ∂P := by
  have h := cut_transfer (P := P) hρ hBm hUm hBU hA hA'
  have e : ∫ ω, |(bCut B ρ (A' ω) - 1 / 2) - (bCut B ρ (A ω) - 1 / 2)| ∂P =
      ∫ ω, |(bCut B ρ (A ω) - 1 / 2) - (bCut B ρ (A' ω) - 1 / 2)| ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => abs_sub_comm _ _)
  linarith

set_option maxHeartbeats 1000000 in
/-- One step `h = T/m` of the limit (C5e): minorisation with Euler errors. -/
theorem core_step_z [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    (x y : SDEState d)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ ρ a : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (F : Set (SDEState d)) {m : ℕ} (hm2 : 2 ≤ m) {h : ℝ≥0} (hh : 0 < (h : ℝ))
    (hh1 : (h : ℝ) ≤ 1) (hmh : (m : ℝ) * h = T) :
    Real.exp (-a) * (P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (x, x)).2 ∈
          {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}} -
        2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * G *
          Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / ρ ^ 2 * h) ≤
      P.real {ω | (zrec s₁ b₁ (h : ℝ) (noiseAt W h 0 ω) m (y, y)).2 ∈
          {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F}} := by
  set c := 2 * L + L ^ 2 + 6 * d * L ^ 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hG0 : 0 ≤ G := le_trans (by positivity) hG
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hTm : (m : ℝ) * ((h : ℝ) * S) ≤ δ / 2 := by rw [← mul_assoc, hmh]; exact hTS
  have hB : ∀ z ∈ {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}, ∀ z', ‖z' - z‖ < ρ →
      z' ∈ {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F} := by
    intro z hz z' hz' w hw
    refine hz ?_
    rw [Metric.mem_ball] at hw ⊢
    rw [dist_eq_norm] at hw ⊢
    have := norm_sub_le_norm_sub_add_norm_sub w z' z
    rw [← dist_eq_norm, ← dist_eq_norm] at this
    rw [dist_eq_norm, dist_eq_norm] at this
    linarith
  have st := steer_lower_s1 (m := m) hW hh hh1 hs hb hJm hJ hL hSg hLg hΛ hag hBxN hBxm x y hm2
    hG hδ hρ hρδ ha hTm (inner_set_isClosed F (2 * ρ)).measurableSet hB hBx
  -- constants
  have hE := pow_E_le hc0 (NNReal.coe_nonneg h) m
  rw [hmh] at hE
  set E := (1 + 13 * c * (h : ℝ)) ^ m with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  have htr : 4 * G * (1 + 13 * E) * (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) /
      δ ^ 2 ≤ 4 * G * (1 + 13 * Real.exp (13 * c * T)) *
        (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 := by
    rw [hmh]
    gcongr
  have hKL : (Λ ^ 2 * (G * E / m) / (2 * h) + 1) / a ≤
      (Λ ^ 2 * G * Real.exp (13 * c * T) / (2 * T) + 1) / a := by
    gcongr ?_ / a
    have e : Λ ^ 2 * (G * E / m) / (2 * h) = Λ ^ 2 * G * E / (2 * T) := by
      rw [← hmh]; field_simp
    rw [e]
    gcongr
  have hch : 5 * c * h * G * E / (m : ℝ) ^ 2 / ρ ^ 2 ≤
      5 * c * G * Real.exp (13 * c * T) / ρ ^ 2 * h := by
    have h1 : 5 * c * h * G * E / (m : ℝ) ^ 2 ≤ 5 * c * h * G * E := by
      rw [div_le_iff₀ (by positivity)]
      have : 0 ≤ 5 * c * h * G * E :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc0) (NNReal.coe_nonneg h)) hG0) hE0
      have hm1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := one_le_pow₀ (by linarith)
      exact le_mul_of_one_le_right this hm1
    have h2 : 5 * c * h * G * E ≤ 5 * c * h * G * Real.exp (13 * c * T) := by
      gcongr
    calc 5 * c * h * G * E / (m : ℝ) ^ 2 / ρ ^ 2 ≤ 5 * c * h * G * Real.exp (13 * c * T) / ρ ^ 2 :=
          div_le_div_of_nonneg_right (h1.trans h2) (by positivity)
      _ = 5 * c * G * Real.exp (13 * c * T) / ρ ^ 2 * h := by ring
  have hex : 2 * (16 * d * S ^ 2 * ((m : ℝ) * h) / (δ / 2) ^ 2) =
      2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) := by rw [hmh]
  refine le_trans ?_ st
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  linarith

/-- C5e: minorisation of the SDE transition laws, `h → 0` limit of `core_step`. -/
theorem core_minor [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb0 : Continuous b₀)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    (hXx : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x) Xx)
    (hXy : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Xy)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S₁ L₁ R : ℝ} (hR : 0 ≤ R) (hL₁ : 0 ≤ L₁)
    (hSg₁ : ∀ x, ‖s₁ x‖ ≤ S₁ ∧ ‖b₁ x‖ ≤ S₁)
    (hLg₁ : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L₁ * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L₁ * ‖x - y‖)
    (hag₁ : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ ρ a : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) (hρδ : ρ ≤ δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (F : Set (SDEState d)) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ {z | Metric.ball z (4 * ρ) ⊆ F}} -
        P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ - 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a) ≤
      P.real {ω | Xy T ω ∈ F} + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ := by
  set hN : ℕ → ℝ≥0 := fun n => T / ((n : ℝ≥0) + 2) with hNdef
  have hcoe : ∀ n, ((hN n : ℝ≥0) : ℝ) = (T : ℝ) / ((n : ℝ) + 2) := fun n => by
    simp [hNdef, NNReal.coe_div]
  have hpos : ∀ n, 0 < ((hN n : ℝ≥0) : ℝ) := fun n => by rw [hcoe]; positivity
  have hlim : Tendsto (fun n => ((hN n : ℝ≥0) : ℝ)) atTop (𝓝 0) := by
    simp_rw [hcoe]
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  have hmh : ∀ n, (((n + 2 : ℕ) : ℝ)) * ((hN n : ℝ≥0) : ℝ) = T := fun n => by
    rw [hcoe]; push_cast; field_simp
  have hWc : ∀ ω, Continuous fun s => W s ω := hW.2.1
  have hZz : ∀ (z : SDEState d) (n : ℕ) (ω : Ω),
      (eulerZZ s₁ b₁ ((hN n : ℝ≥0) : ℝ) (fun s => W s ω) z z (n + 2)).2 =
        (zrec s₁ b₁ ((hN n : ℝ≥0) : ℝ) (noiseAt W (hN n) 0 ω) (n + 2) (z, z)).2 := fun z n ω => by
    have := eulerZZ_eq_zrec (s₁ := s₁) (b₁ := b₁) ω (hWc ω) (hpos n) z z 0 (n + 2)
    rw [zero_add] at this
    rw [this]
    rfl
  have hGm : ∀ r t : ℝ≥0, r ≤ t → ∀ j,
      Measurable[(fun _ : ℝ≥0 => (‹MeasurableSpace Ω›)) t] fun ω => W r ω j :=
    fun r _ _ j => stdBrownian_coord_measurable hW r j
  have hZm : ∀ (z : SDEState d) (n : ℕ),
      Measurable fun ω => (eulerZZ s₁ b₁ ((hN n : ℝ≥0) : ℝ) (fun s => W s ω) z z (n + 2)).2 :=
    fun z n => (eulerZZ_meas_G (G := fun _ => ‹MeasurableSpace Ω›) hGm monotone_const hWc (hpos n)
      hs₁ hb₁ z z (n + 2)).2
  have eul : ∀ (z : SDEState d) (Xz : ℝ≥0 → Ω → SDEState d),
      SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => z) Xz →
      ∀ (B : Set (SDEState d)) {η : ℝ}, 0 < η → ∀ᶠ n in atTop,
        ∫ ω, |(bCut B ρ (eulerZZ s₁ b₁ ((hN n : ℝ≥0) : ℝ) (fun s => W s ω) z z (n + 2)).2 - 1 / 2) -
          (bCut B ρ (Xz T ω) - 1 / 2)| ∂P ≤ P.real {ω | ∀ s ≤ T, ‖Xz s ω‖ ≤ R}ᶜ + η := by
    intro z Xz hXz B η hη
    have e := EthierKurtz.euler_scheme_approx_abs hW z hσ hb0 hXz hs₁ hb₁ hR hL₁ hSg₁ hLg₁ hag₁
      (hn := fun n => ((hN n : ℝ≥0) : ℝ)) hpos hlim T (fun n => n + 2)
      (fun n => ⟨by show 1 ≤ n + 2; omega, (hmh n).le, by
        show (T : ℝ) ≤ ((n + 2 : ℕ) : ℝ) * ((hN n : ℝ≥0) : ℝ) + ((hN n : ℝ≥0) : ℝ)
        rw [hmh n]; linarith [hpos n]⟩)
      (fun _ _ y => bCut B ρ y - 1 / 2) (K := 1 / 2) (Λ := ρ⁻¹) (inv_nonneg.2 hρ.le)
      (fun _ _ y => bCut_abs_le B hρ y)
      (fun _ a y a' y' => by
        show |(bCut B ρ y - 1 / 2) - (bCut B ρ y' - 1 / 2)| ≤ ρ⁻¹ * (‖a - a'‖ + ‖y - y'‖)
        rw [sub_sub_sub_cancel_right]
        exact (bCut_lip B hρ y y').trans (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (norm_nonneg _)) (inv_nonneg.2 hρ.le)))
      hη (fun n ω k => eulerZZ s₁ b₁ ((hN n : ℝ≥0) : ℝ) (fun s => W s ω) z z k)
      (fun _ _ => rfl) (fun _ _ _ => rfl)
    filter_upwards [e] with n hn
    refine hn.trans (le_of_eq ?_)
    rw [measureReal_def]
    ring
  have hFx : MeasurableSet {z : SDEState d | Metric.ball z (4 * ρ) ⊆ F} :=
    (inner_set_isClosed F (4 * ρ)).measurableSet
  have hF3 : MeasurableSet {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F} :=
    (inner_set_isClosed F (3 * ρ)).measurableSet
  have hF2 : MeasurableSet {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F} :=
    (inner_set_isClosed F (2 * ρ)).measurableSet
  have hBUx : ∀ w b, b ∈ {z : SDEState d | Metric.ball z (4 * ρ) ⊆ F} → dist w b < ρ →
      w ∈ {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F} := by
    intro w b hb hwb u hu
    refine hb ?_
    rw [Metric.mem_ball] at hu ⊢
    linarith [dist_triangle u w b]
  have hBUy : ∀ w b, b ∈ {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F} → dist w b < ρ →
      w ∈ interior F := by
    intro w b hb hwb
    refine interior_maximal (fun u hu => hb ?_) Metric.isOpen_ball (Metric.mem_ball_self hρ)
    rw [Metric.mem_ball] at hu ⊢
    linarith [dist_triangle u w b]
  have hev : ∀ᶠ n in atTop, ((hN n : ℝ≥0) : ℝ) < 1 := hlim.eventually (gt_mem_nhds one_pos)
  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hη4 : 0 < η / 4 := by positivity
  have eX := eul x Xx hXx {z | Metric.ball z (4 * ρ) ⊆ F} hη4
  have eY := eul y Xy hXy {z | Metric.ball z (2 * ρ) ⊆ F} hη4
  have hT : ∀ᶠ n in atTop, 5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * G *
      Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / ρ ^ 2 * ((hN n : ℝ≥0) : ℝ) < η / 4 := by
    have := hlim.const_mul (5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * G *
      Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / ρ ^ 2)
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds hη4)
  obtain ⟨n, hnx, hny, hnT, hn1⟩ := (eX.and (eY.and (hT.and hev))).exists
  have st := core_step_z (m := n + 2) (h := hN n) hW x y hs hb hJm hJ hL hSg hLg hΛ hag hBxN hBxm hG
    hT0 hδ hρ hρδ ha hTS hBx F (by omega) (hpos n) hn1.le (hmh n)
  have tx := cut_transfer (P := P) hρ hFx hF3 hBUx (hXx.1 T) (hZm x n)
  have ty := cut_transfer' (P := P) hρ hF2 isOpen_interior.measurableSet hBUy (hZm y n) (hXy.1 T)
  have sx : P.real {ω | (eulerZZ s₁ b₁ ((hN n : ℝ≥0) : ℝ) (fun s => W s ω) x x (n + 2)).2 ∈
      {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}} =
      P.real {ω | (zrec s₁ b₁ ((hN n : ℝ≥0) : ℝ) (noiseAt W (hN n) 0 ω) (n + 2) (x, x)).2 ∈
      {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}} := by simp only [hZz]
  have sy : P.real {ω | (eulerZZ s₁ b₁ ((hN n : ℝ≥0) : ℝ) (fun s => W s ω) y y (n + 2)).2 ∈
      {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F}} =
      P.real {ω | (zrec s₁ b₁ ((hN n : ℝ≥0) : ℝ) (noiseAt W (hN n) 0 ω) (n + 2) (y, y)).2 ∈
      {z : SDEState d | Metric.ball z (2 * ρ) ⊆ F}} := by simp only [hZz]
  have mono : P.real {ω | Xy T ω ∈ interior F} ≤ P.real {ω | Xy T ω ∈ F} :=
    measureReal_mono (fun ω (hω : Xy T ω ∈ interior F) => (interior_subset hω : Xy T ω ∈ F))
  have hea0 := Real.exp_pos (-a)
  have hea1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have k1 : Real.exp (-a) * P.real {ω | Xx T ω ∈ {z | Metric.ball z (4 * ρ) ⊆ F}} ≤
      Real.exp (-a) * (P.real {ω | (zrec s₁ b₁ ((hN n : ℝ≥0) : ℝ) (noiseAt W (hN n) 0 ω) (n + 2)
        (x, x)).2 ∈ {z : SDEState d | Metric.ball z (3 * ρ) ⊆ F}} +
        P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ + η / 4) :=
    mul_le_mul_of_nonneg_left (by linarith) hea0.le
  have k2 : Real.exp (-a) * (5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * G *
      Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / ρ ^ 2 * ((hN n : ℝ≥0) : ℝ)) ≤ η / 4 := by
    rcases le_or_gt 0 (5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * G *
      Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / ρ ^ 2 * ((hN n : ℝ≥0) : ℝ)) with h0 | h0
    · have := mul_le_mul_of_nonneg_right hea1 h0
      linarith
    · have := mul_neg_of_pos_of_neg hea0 h0
      linarith
  have k3 : Real.exp (-a) * (η / 4) ≤ η / 4 := by
    have := mul_le_mul_of_nonneg_right hea1 hη4.le
    linarith
  linarith

end C5y
end ItoLib

-- ===== CU =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5z
/-! CORE route, s28 (C5f, first half): `ρ → 0` in `core_minor` turns `F_{4ρ}` into `interior F`. -/

variable {d : ℕ}

theorem iUnion_inner_eq_interior (F : Set (SDEState d)) {δ : ℝ} (hδ : 0 < δ) :
    ⋃ k : ℕ, {z : SDEState d | Metric.ball z (4 * (δ / ((k : ℝ) + 1))) ⊆ F} = interior F := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk⟩
    exact interior_maximal hk Metric.isOpen_ball (Metric.mem_ball_self (by positivity))
  · intro hz
    obtain ⟨r, hr, hrF⟩ := Metric.isOpen_iff.1 isOpen_interior z hz
    obtain ⟨k, hk⟩ := exists_nat_gt (4 * δ / r)
    refine ⟨k, (Metric.ball_subset_ball ?_).trans (hrF.trans interior_subset)⟩
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hr] at hk
    rw [mul_div_assoc', div_le_iff₀ hk1]
    linarith

theorem inner_mono (F : Set (SDEState d)) {δ : ℝ} (hδ : 0 < δ) :
    Monotone fun k : ℕ => {z : SDEState d | Metric.ball z (4 * (δ / ((k : ℝ) + 1))) ⊆ F} := by
  intro k k' hkk z hz
  refine (Metric.ball_subset_ball ?_).trans hz
  have : (k : ℝ) ≤ k' := by exact_mod_cast hkk
  gcongr

theorem core_minor_int [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb0 : Continuous b₀)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    (hXx : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x) Xx)
    (hXy : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Xy)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    (hs₁ : Continuous s₁) (hb₁ : Continuous b₁) {S₁ L₁ R : ℝ} (hR : 0 ≤ R) (hL₁ : 0 ≤ L₁)
    (hSg₁ : ∀ x, ‖s₁ x‖ ≤ S₁ ∧ ‖b₁ x‖ ≤ S₁)
    (hLg₁ : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L₁ * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L₁ * ‖x - y‖)
    (hag₁ : ∀ x : SDEState d, ‖x‖ ≤ R + 3 → s₁ x = σ₀ x ∧ b₁ x = b₀ x)
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ a : ℝ} (hδ : 0 < δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (F : Set (SDEState d)) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ interior F} -
        P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ R}ᶜ - 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a) ≤
      P.real {ω | Xy T ω ∈ F} + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ R}ᶜ := by
  have hmx : Measurable (Xx T) := hXx.1 T
  have hmono : Monotone fun k : ℕ =>
      Xx T ⁻¹' {z : SDEState d | Metric.ball z (4 * (δ / ((k : ℝ) + 1))) ⊆ F} :=
    fun k k' hkk => Set.preimage_mono (inner_mono F hδ hkk)
  have hU : (⋃ k : ℕ, Xx T ⁻¹' {z : SDEState d | Metric.ball z (4 * (δ / ((k : ℝ) + 1))) ⊆ F}) =
      {ω | Xx T ω ∈ interior F} := by
    rw [← Set.preimage_iUnion, iUnion_inner_eq_interior F hδ]; rfl
  have ht := tendsto_measure_iUnion_atTop (μ := P) hmono
  rw [hU] at ht
  have htr := (ENNReal.tendsto_toReal (measure_ne_top P _)).comp ht
  have hk1 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hρ : ∀ k : ℕ, 0 < δ / ((k : ℝ) + 1) := fun k => by have := hk1 k; positivity
  have hρδ : ∀ k : ℕ, δ / ((k : ℝ) + 1) ≤ δ := fun k =>
    div_le_self hδ.le (by linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  refine le_of_tendsto' (x := (atTop : Filter ℕ)) ?_ fun k => core_minor hW hσ hb0 x y hXx hXy hs₁ hb₁ hR hL₁ hSg₁ hLg₁ hag₁
    hs hb hJm hJ hL hSg hLg hΛ hag hBxN hBxm hG hT0 hδ (hρ k) (hρδ k) ha hTS hBx F
  refine Tendsto.const_mul _ ?_
  refine (((Tendsto.sub_const ?_ _).sub_const _).sub_const _).sub_const _
  have e : ∀ k : ℕ, 4 * (δ / ((k : ℝ) + 1)) = 4 * (δ / ((k : ℝ) + 1)) := fun _ => rfl
  exact htr

end C5z
end ItoLib

-- ===== CV =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5fa
/-! CORE route, s29 (C5f-a): `R → ∞` in `core_minor_int` with a truncation family `s₁ R, b₁ R`. -/

variable {d : ℕ}

theorem exit_real_tendsto [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℝ≥0 → Ω → SDEState d} (hm : ∀ t, Measurable (X t)) (hc : ∀ ω, Continuous fun t => X t ω)
    (T : ℝ≥0) :
    Tendsto (fun R : ℕ => P.real {ω | ∀ s ≤ T, ‖X s ω‖ ≤ (R : ℝ)}ᶜ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (exit_tendsto (P := P) hm hc T)
  simpa [Function.comp_def, measureReal_def] using h

theorem core_minor_lim [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb0 : Continuous b₀)
    {Xx Xy : ℝ≥0 → Ω → SDEState d} (x y : SDEState d)
    (hXx : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x) Xx)
    (hXy : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => y) Xy)
    {s₁ : ℕ → SDEState d → SDEDiffusion d} {b₁ : ℕ → SDEState d → SDEState d} {S₁ L₁ : ℕ → ℝ}
    (hs₁ : ∀ R, Continuous (s₁ R)) (hb₁ : ∀ R, Continuous (b₁ R)) (hL₁ : ∀ R, 0 ≤ L₁ R)
    (hSg₁ : ∀ R x, ‖s₁ R x‖ ≤ S₁ R ∧ ‖b₁ R x‖ ≤ S₁ R)
    (hLg₁ : ∀ R x y, ‖s₁ R x - s₁ R y‖ ≤ L₁ R * ‖x - y‖ ∧ ‖b₁ R x - b₁ R y‖ ≤ L₁ R * ‖x - y‖)
    (hag₁ : ∀ (R : ℕ) (x : SDEState d), ‖x‖ ≤ (R : ℝ) + 3 → s₁ R x = σ₀ x ∧ b₁ R x = b₀ x)
    {s₂ : SDEState d → SDEDiffusion d} {b₂ : SDEState d → SDEState d}
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hs : Continuous s₂) (hb : Continuous b₂)
    (hJm : Measurable (Function.uncurry J)) (hJ : ∀ p v, avgApply s₂ p (J p v) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, σ₀ x = s₂ x ∧ b₀ x = b₂ x)
    {R₀ : ℝ} (hNR : ∀ x ∈ N, ‖x‖ ≤ R₀) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) {G : ℝ} (hG : ‖x - y‖ ^ 2 ≤ G)
    {T : ℝ≥0} (hT0 : 0 < (T : ℝ)) {δ a : ℝ} (hδ : 0 < δ)
    (ha : 0 < a) (hTS : (T : ℝ) * S ≤ δ / 2)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (F : Set (SDEState d)) :
    Real.exp (-a) * (P.real {ω | Xx T ω ∈ interior F} - 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2 -
        (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a) ≤
      P.real {ω | Xy T ω ∈ F} := by
  have hx := exit_real_tendsto (P := P) hXx.1 hXx.2.1 T
  have hy := exit_real_tendsto (P := P) hXy.1 hXy.2.1 T
  set E1 : ℝ := 2 * (16 * d * S ^ 2 * T / (δ / 2) ^ 2)
  set E2 : ℝ := 4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T)) *
          (12 * d * L ^ 2 * T + L ^ 2 * (T : ℝ) ^ 2) / δ ^ 2
  set E3 : ℝ := (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * T) / (2 * T) + 1) / a
  set A : ℝ := P.real {ω | Xx T ω ∈ interior F}
  set B : ℝ := P.real {ω | Xy T ω ∈ F}
  have hf : Tendsto (fun R : ℕ => Real.exp (-a) * (A - P.real {ω | ∀ s ≤ T, ‖Xx s ω‖ ≤ (R : ℝ)}ᶜ
      - E1 - E2 - E3)) atTop (𝓝 (Real.exp (-a) * (A - 0 - E1 - E2 - E3))) :=
    Tendsto.const_mul _ ((((tendsto_const_nhds.sub hx).sub_const _).sub_const _).sub_const _)
  have hg : Tendsto (fun R : ℕ => B + P.real {ω | ∀ s ≤ T, ‖Xy s ω‖ ≤ (R : ℝ)}ᶜ) atTop (𝓝 (B + 0)) :=
    tendsto_const_nhds.add hy
  rw [sub_zero] at hf
  rw [add_zero] at hg
  refine le_of_tendsto_of_tendsto hf hg ?_
  obtain ⟨R1, hR1⟩ := exists_nat_ge R₀
  filter_upwards [eventually_ge_atTop R1] with R hR
  have hRR : R₀ ≤ (R : ℝ) := hR1.trans (by exact_mod_cast hR)
  have hag' : ∀ z ∈ N, s₁ R z = s₂ z ∧ b₁ R z = b₂ z := by
    intro z hz
    have h1 := hag₁ R z (by linarith [hNR z hz])
    exact ⟨h1.1.trans (hag z hz).1, h1.2.trans (hag z hz).2⟩
  exact core_minor_int hW hσ hb0 x y hXx hXy (hs₁ R) (hb₁ R) (Nat.cast_nonneg R) (hL₁ R) (hSg₁ R)
    (hLg₁ R) (hag₁ R) hs hb hJm hJ hL hSg hLg hΛ hag' hBxN hBxm hG hT0 hδ ha hTS hBx F

end C5fa
end ItoLib

-- ===== CA =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib

/-! CA (CORE route, s22): measure-theoretic transfer lemmas for the Euler-limit minorization.
A lower bound `c L(int F) ≤ μ F + η` on closed sets (what a weak/in-probability limit gives)
upgrades to all Borel sets, and a common lower bound of two probability measures bounds their
total variation distance. -/

end ItoLib

-- ===== CW =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz
variable {Ω : Type*}

section C5fb
/-! CORE route, s29 (C5f-b): the closed-set minorisation of `core_minor_lim` gives a TV overlap
of the two time-`T` laws. -/

variable {d : ℕ}

end C5fb
end ItoLib

-- ===== CX =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace ItoLib
open EthierKurtz

section C5g
/-! CORE route, s29 (C5g): instantiation for the Kolmogorov model. For a box `[α, β]ⁿ` with
`α > 0` and every small `T > 0`, the time-`T` laws from any two points of the box overlap. -/

open StochKolmogorov.Persist

variable {n : ℕ}

theorem box_nbhd {α β δ : ℝ} (hδ : 0 < δ) {x y : SDEState n} (hx : x ∈ boxSet α β)
    (hy : y ∈ boxSet α β) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (z : SDEState n)
    (hz : ‖z - (x - t • (x - y))‖ < 2 * δ) : z ∈ boxSet (α - 2 * δ) (β + 2 * δ) := by
  intro i
  have hzi : |z i - (x i - t * (x i - y i))| < 2 * δ := by
    have h := PiLp.norm_apply_le (z - (x - t • (x - y))) i
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs] at h
    exact h.trans_lt hz
  have h1 := (hx i).1
  have h2 := (hx i).2
  have h3 := (hy i).1
  have h4 := (hy i).2
  have hw1 : α ≤ x i - t * (x i - y i) := by nlinarith
  have hw2 : x i - t * (x i - y i) ≤ β := by nlinarith
  rw [abs_lt] at hzi
  constructor <;> linarith [hzi.1, hzi.2]

end C5g
end ItoLib

-- ===== CY43 =====
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

/-! 43e412d4 (Extinct.theorem_1_2) child N1W: uniform minorisation of the time-`T` laws from a box
onto a small ball, for all `T` in a window `[T₀/2, T₀]` (CORE route, core_minor_lim with x := z). -/

namespace ItoLib
open EthierKurtz
open StochKolmogorov.Persist

variable {n : ℕ}

theorem win_arith {e A E1 E2 E3 Bv : ℝ} (he : 0 < e) (h : e * (A - E1 - E2 - E3) ≤ Bv)
    (hA : 1 / 2 ≤ A) (h12 : E1 + E2 < 1 / 8) (h3 : E3 ≤ 1 / 8) : e / 4 ≤ Bv := by
  have hQ : 1 / 4 ≤ A - E1 - E2 - E3 := by linarith
  have := mul_le_mul_of_nonneg_left hQ he.le
  linarith

/-- Per-point short-time stay: `P(Y_T ∈ ball z r) ≥ 1/2` for all small `T`. -/
theorem stay_point {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℝ≥0 → Ω → SDEState n} (hm : ∀ t, Measurable (Y t))
    (hc : ∀ ω, Continuous fun t => Y t ω)
    (z : SDEState n) (h0 : Y 0 =ᵐ[P] fun _ => z) (r : ℝ) (hr : 0 < r) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ∀ T : ℝ≥0, T ≤ ρ →
      (1 / 2 : ℝ) ≤ P.real {ω | Y T ω ∈ Metric.ball z r} := by
  have hlim : Tendsto (fun T : ℝ≥0 => ∫⁻ ω, (Metric.ball z r).indicator
      (fun _ => (1 : ℝ≥0∞)) (Y T ω) ∂P) (𝓝 0) (𝓝 (∫⁻ _ω, (1 : ℝ≥0∞) ∂P)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_ (by simp) ?_
    · exact Eventually.of_forall fun T =>
        (measurable_const.indicator Metric.isOpen_ball.measurableSet).comp (hm T)
    · exact Eventually.of_forall fun T => ae_of_all _ fun ω => by
        by_cases h : Y T ω ∈ Metric.ball z r <;> simp [h]
    · filter_upwards [h0] with ω hω
      have hω' : Y 0 ω = z := hω
      have hcont : Tendsto (fun T => Y T ω) (𝓝 0) (𝓝 z) := by
        have := (hc ω).tendsto 0; rwa [hω'] at this
      have hev : ∀ᶠ T in 𝓝 (0 : ℝ≥0), Y T ω ∈ Metric.ball z r :=
        hcont (Metric.ball_mem_nhds z hr)
      exact tendsto_const_nhds.congr' (by
        filter_upwards [hev] with T hT
        rw [Set.indicator_of_mem hT])
  have e : ∀ T : ℝ≥0, ∫⁻ ω, (Metric.ball z r).indicator (fun _ => (1 : ℝ≥0∞)) (Y T ω) ∂P
      = P {ω | Y T ω ∈ Metric.ball z r} := fun T => by
    rw [lintegral_indicator_const_comp (hm T) Metric.isOpen_ball.measurableSet, one_mul]; rfl
  simp only [e, lintegral_const, measure_univ, mul_one] at hlim
  have hlimR : Tendsto (fun T : ℝ≥0 => P.real {ω | Y T ω ∈ Metric.ball z r}) (𝓝 0) (𝓝 1) := by
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim
    simpa [Function.comp_def, measureReal_def] using this
  obtain ⟨ε, hε, hεev⟩ := Metric.eventually_nhds_iff.1
    (hlimR.eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)))
  refine ⟨Real.toNNReal (ε / 2), Real.toNNReal_pos.2 (by positivity), fun T hT => ?_⟩
  have hT' : (T : ℝ) ≤ ε / 2 := by
    have := NNReal.coe_le_coe.2 hT
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  have hd : dist T 0 < ε := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, NNReal.abs_eq]; linarith
  exact (hεev hd).le

/-- N1W: for a box `[α, β]ⁿ` (`α > 0`), a centre `z` in it and `r > 0`, the time-`T` laws from
every point of the box give the ball `B(z, r)` mass at least `p > 0`, for all `T ∈ [T₀/2, T₀]`. -/
theorem core_window {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    (hpd : ∀ x ∈ orthant n, (Matrix.of fun i j => C.g i x * C.g j x * C.sig i j).PosDef)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (z : SDEState n) (hz : z ∈ boxSet α β)
    (r : ℝ) (hr : 0 < r) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ p : ℝ, 0 < p ∧ ∀ T : ℝ≥0, T₀ / 2 ≤ T → T ≤ T₀ →
      ∀ y ∈ boxSet α β, p ≤ (trans P X T y (Metric.ball z r)).toReal := by
  haveI : IsProbabilityMeasure P := hX.1
  have hW := hX.2.1
  set δ : ℝ := α / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set α' : ℝ := α - 2 * δ with hα'def
  set β' : ℝ := β + 2 * δ with hβ'def
  have hα' : 0 < α' := by rw [hα'def, hδdef]; linarith
  have hαβ' : α' ≤ β' := by rw [hα'def, hβ'def]; linarith
  have hgc : ∀ i, ContinuousOn (C.g i) (orthant n) := fun i => (hC i).2.continuousOn
  obtain ⟨hσc, hbc, s₁, b₁, S₁, L₁, hs₁, hb₁, hL₁, hSg₁, hLg₁, hag₁⟩ := kolm_trunc C hC
  obtain ⟨hs, hb, S, L, hL, hSg, hLg⟩ := kolm_box C hC hα'.le hαβ'
  obtain ⟨κ, hκ, hsep⟩ := aK_sep C hpd hgc hα' hαβ'
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hSg 0).1
  have hne : ∀ i x y, aK C α' β' i x + aK C α' β' i y ≠ 0 := fun i x y h => by
    have := hsep i x y
    rw [h, abs_zero] at this
    linarith
  set J := jInv (aK C α' β') C.Γ with hJdef
  have hJm : Measurable (Function.uncurry J) :=
    jInv_measurable C.Γ (fun i => (aK_continuous C hgc α' β' i).measurable)
  have hJ : ∀ p v, avgApply (sK C α' β') p (J p v) = v :=
    jInv_right (sK_apply C α' β') (gamma_isUnit C hpd) hne
  set Λ : ℝ := 2 * Real.sqrt (∑ j, ∑ k, (C.Γ.transpose)⁻¹ j k ^ 2) / κ with hΛdef
  have hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2 :=
    fun p v => jInv_bound C.Γ hκ hsep p v
  have hNc : IsCompact (boxSet (n := n) α' β') := boxSet_isCompact hα'.le
  obtain ⟨R₀, hR₀⟩ := hNc.isBounded.exists_norm_le
  obtain ⟨D, hD⟩ := Metric.isBounded_iff.1 (boxSet_isCompact (n := n) hα.le).isBounded
  set G : ℝ := D ^ 2 with hGdef
  have hag : ∀ x ∈ boxSet α' β', (fun z : SDEState n => diffusion C (0, z)) x = sK C α' β' x ∧
      (fun z : SDEState n => drift C (0, z)) x = bK C α' β' x := by
    intro x hx
    constructor <;> simp [sK, bK, boxP_eq hx]
  -- choice of T₀
  set f : ℝ → ℝ := fun T => 2 * (16 * n * S ^ 2 * T / (δ / 2) ^ 2) +
      4 * G * (1 + 13 * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T)) *
        (12 * n * L ^ 2 * T + L ^ 2 * T ^ 2) / δ ^ 2 with hfdef
  have hfc : Continuous f := by rw [hfdef]; fun_prop
  have hf0 : f 0 = 0 := by simp [hfdef]
  have hev : ∀ᶠ T in 𝓝 (0 : ℝ), f T < 1 / 8 ∧ T * S < δ / 2 := by
    refine (hfc.tendsto 0).eventually (gt_mem_nhds (by rw [hf0]; norm_num)) |>.and ?_
    have hc : Continuous fun T : ℝ => T * S := by fun_prop
    exact hc.tendsto 0 |>.eventually (gt_mem_nhds (by simpa using half_pos hδ))
  obtain ⟨ρ, hρ, hρev⟩ := Metric.eventually_nhds_iff.1 hev
  have hzo : z ∈ orthant n := fun i => hα.le.trans (hz i).1
  have hXz := hX.2.2 z hzo
  obtain ⟨ρ', hρ', hstay⟩ := stay_point (P := P) hXz.1 hXz.2.1 z hXz.2.2.2.1 r hr
  set T₀ : ℝ≥0 := min (Real.toNNReal (ρ / 2)) ρ' with hT₀
  have hT₀pos : 0 < T₀ := lt_min (Real.toNNReal_pos.2 (by positivity)) hρ'
  have hT₀R : (0 : ℝ) < T₀ := NNReal.coe_pos.2 hT₀pos
  refine ⟨T₀, hT₀pos, ?_⟩
  have hG0 : 0 ≤ G := by rw [hGdef]; positivity
  have hc0 : 0 ≤ 13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [mul_nonneg hn0 (sq_nonneg L), sq_nonneg L]
  set X3m : ℝ := Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T₀) / T₀
    with hX3m
  have hX3m0 : 0 ≤ X3m := by
    rw [hX3m]; exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hG0) (Real.exp_pos _).le)
      hT₀R.le
  set a : ℝ := 8 * (X3m + 1) with hadef
  have ha : 0 < a := by rw [hadef]; linarith
  refine ⟨Real.exp (-a) / 4, by positivity, ?_⟩
  intro T hT1 hT2 y hy
  have hT1R : (T₀ : ℝ) / 2 ≤ T := by
    have := NNReal.coe_le_coe.2 hT1; simpa using this
  have hT2R : (T : ℝ) ≤ T₀ := NNReal.coe_le_coe.2 hT2
  have hT0 : 0 < (T : ℝ) := by linarith
  have hTρ : (T : ℝ) ≤ ρ / 2 := by
    have h1 : (T₀ : ℝ) ≤ ((Real.toNNReal (ρ / 2) : ℝ≥0) : ℝ) := NNReal.coe_le_coe.2 (min_le_left _ _)
    rw [Real.coe_toNNReal _ (by positivity)] at h1
    linarith
  have hdist : dist (T : ℝ) 0 < ρ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hT0]; linarith
  obtain ⟨hfT, hTS⟩ := hρev hdist
  have hyo : y ∈ orthant n := fun i => hα.le.trans (hy i).1
  have hG : ‖z - y‖ ^ 2 ≤ G := by
    rw [hGdef, ← dist_eq_norm]
    exact pow_le_pow_left₀ dist_nonneg (hD hz hy) 2
  have hE3 : (Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T) / (2 * T) + 1) / a
      ≤ 1 / 8 := by
    have hexp : Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T)
        ≤ Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T₀) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT2R hc0)
    have hnum : Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T)
        ≤ Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T₀) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg (sq_nonneg _) hG0)
    have h1 : Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T) / (2 * T) ≤ X3m := by
      calc Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T) / (2 * T)
          ≤ Λ ^ 2 * G * Real.exp (13 * (2 * L + L ^ 2 + 6 * n * L ^ 2) * T₀) / (2 * T) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ X3m := by
            rw [hX3m]
            exact div_le_div_of_nonneg_left
              (mul_nonneg (mul_nonneg (sq_nonneg _) hG0) (Real.exp_pos _).le) hT₀R (by linarith)
    rw [div_le_iff₀ ha, hadef]; linarith
  have hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ w, ‖w - (z - t • (z - y))‖ < 2 * δ →
      w ∈ boxSet α' β' := fun t ht0 ht1 w hw => box_nbhd hδ hz hy ht0 ht1 w hw
  have hmain := core_minor_lim hW hσc hbc z y hXz (hX.2.2 y hyo) hs₁ hb₁ hL₁ hSg₁ hLg₁ hag₁
    hs hb hJm hJ hL hSg hLg hΛ hag (fun w hw => hR₀ w hw) subset_rfl
    hNc.isClosed.measurableSet hG hT0 hδ ha hTS.le hBx (Metric.ball z r)
  rw [Metric.isOpen_ball.interior_eq] at hmain
  have hs := hstay T (hT2.trans (min_le_right _ _))
  have htr : (trans P X T y (Metric.ball z r)).toReal = P.real {ω | X y T ω ∈ Metric.ball z r} := by
    rw [StochKolmogorov.Persist.trans, Measure.map_apply ((hX.2.2 y hyo).1 T) Metric.isOpen_ball.measurableSet]; rfl
  rw [htr]
  rw [hfdef] at hfT
  exact win_arith (Real.exp_pos _) hmain hs hfT hE3

end ItoLib

namespace ExtinctBBW

/-- The same coefficients, read in the `Persist` copy of the model. -/
def toP {n : ℕ} (C : StochKolmogorov.Extinct.Coeffs n) : StochKolmogorov.Persist.Coeffs n :=
  ⟨C.f, C.g, C.Γ⟩

end ExtinctBBW

open MeasureTheory ProbabilityTheory Filter in
open scoped ENNReal NNReal Topology BigOperators in
open StochKolmogorov.Extinct EthierKurtz in
theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n)
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (hX : IsSolutionFamily P C B X)
    (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) (z : SDEState n) (hz : ∀ l, α ≤ z l ∧ z l ≤ β)
    (r : ℝ) (hr : 0 < r) :
    ∃ T₀ : ℝ≥0, 0 < T₀ ∧ ∃ p : ℝ, 0 < p ∧ ∀ T : ℝ≥0, T₀ / 2 ≤ T → T ≤ T₀ →
      ∀ y : SDEState n, (∀ l, α ≤ y l ∧ y l ≤ β) →
        p ≤ (trans P X T y (Metric.ball z r)).toReal := by
  exact ItoLib.core_window P (ExtinctBBW.toP C) B X hX hA.2.1 hA.1 hα hαβ z hz r hr
