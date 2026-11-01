-- Prove2me | solution 1 for StochKolmogorov.Persist.log_V_mean_le_occupation_phi
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-01T03:12:41.996078+00:00
-- url     : https://prove2.me/submissions/16fc6996-b02f-4310-816f-df959e525662

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
import Theorems.Thm_StochKolmogorov_Persist_kolmogorov_sde_face_invariance

set_option linter.all false

section SpeedInst
/-! Shortcut instances (compile speed only; every one is the canonical instance found by `inferInstance`
or the canonical constructor): the default searches for these classes on `ℝ`, `SDEState n` and their
continuous-linear-map spaces were a large share of this file's elaboration time. -/
open EthierKurtz
local instance (priority := high) spdR1 : AddRightMono ℝ := inferInstance
local instance (priority := high) spdR2 : AddLeftMono ℝ := inferInstance
local instance (priority := high) spdR3 : CharZero ℝ := inferInstance
local instance (priority := high) spdR4 : AddRightStrictMono ℝ := inferInstance
local instance (priority := high) spdR5 : AddLeftStrictMono ℝ := inferInstance
local instance (priority := high) spdR6 : AddRightReflectLE ℝ := inferInstance
local instance (priority := high) spdR7 : AddRightReflectLT ℝ := inferInstance
local instance (priority := high) spdR8 : AddLeftReflectLE ℝ := inferInstance
local instance (priority := high) spdR9 : AddLeftReflectLT ℝ := inferInstance
local instance (priority := high) spdR10 : IsOrderedRing ℝ := inferInstance
local instance (priority := high) spdR11 : IsStrictOrderedRing ℝ := inferInstance
local instance (priority := high) spdR12 : PosMulReflectLT ℝ := inferInstance
local instance (priority := high) spdR13 : MulPosMono ℝ := inferInstance
local instance (priority := high) spdR14 : PosMulMono ℝ := inferInstance
local instance (priority := high) spdR15 : PosMulStrictMono ℝ := inferInstance
local instance (priority := high) spdR16 : MulPosStrictMono ℝ := inferInstance
local instance (priority := high) spdR17 : MulPosReflectLT ℝ := inferInstance
local instance (priority := high) spdR18 : ExistsAddOfLE ℝ := inferInstance
local instance (priority := high) spdR19 : IsOrderedAddMonoid ℝ := inferInstance
local instance (priority := high) spdR20 : ContinuousSMul ℝ ℝ := inferInstance
local instance (priority := high) spdR21 : ContinuousSub ℝ := inferInstance
local instance (priority := high) spdR22 : ContinuousAdd ℝ := inferInstance
local instance (priority := high) spdR23 : ContinuousMul ℝ := inferInstance
local instance (priority := high) spdR24 : ClosedIicTopology ℝ := inferInstance
local instance (priority := high) spdR25 : IsOrderedModule ℝ ℝ := inferInstance
local instance (priority := high) spdS1 (n : ℕ) : ContinuousSMul ℝ (SDEState n) := inferInstance
local instance (priority := high) spdS2 (n : ℕ) : T2Space (SDEState n) := inferInstance
local instance (priority := high) spdS3 (n : ℕ) : ProperSpace (SDEState n) := inferInstance
local instance (priority := high) spdS4 (n : ℕ) : CompleteSpace (SDEState n) := inferInstance
local instance (priority := high) spdS5 (n : ℕ) : ContinuousAdd (SDEState n) := inferInstance
local instance (priority := high) spdS6 (n : ℕ) : FiniteDimensional ℝ (SDEState n) := inferInstance
local instance (priority := high) spdS7 (n : ℕ) : IsTopologicalAddGroup (SDEState n) := inferInstance
local instance (priority := high) spdS8 (n : ℕ) : OpensMeasurableSpace (SDEState n) := inferInstance
local instance (priority := high) spdL1 (n : ℕ) : ContinuousSMul ℝ (SDEState n →L[ℝ] ℝ) := inferInstance
local instance (priority := high) spdL2 (n : ℕ) : CompleteSpace (SDEState n →L[ℝ] ℝ) := inferInstance
local instance (priority := high) spdL3 (n : ℕ) : T2Space (SDEState n →L[ℝ] ℝ) := inferInstance
local instance (priority := high) spdL4 (n : ℕ) : ContinuousAdd (SDEState n →L[ℝ] ℝ) := inferInstance
local instance (priority := high) spdL5 (n : ℕ) :
    ContinuousSMul ℝ (SDEState n →L[ℝ] SDEState n →L[ℝ] ℝ) := inferInstance
local instance (priority := high) spdL6 (n : ℕ) :
    CompleteSpace (SDEState n →L[ℝ] SDEState n →L[ℝ] ℝ) := inferInstance
local instance (priority := high) spdL7 (n : ℕ) :
    T2Space (SDEState n →L[ℝ] SDEState n →L[ℝ] ℝ) := inferInstance
local instance (priority := high) spdL8 (n m : ℕ) : ContinuousSMul ℝ (SDEState n →L[ℝ] SDEState m) :=
  inferInstance
local instance (priority := high) spdL9 (n m : ℕ) : T2Space (SDEState n →L[ℝ] SDEState m) := inferInstance
noncomputable local instance (priority := high) spdN1 (n : ℕ) :
    NormedAddCommGroup (SDEState n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance (priority := high) spdN2 (n : ℕ) :
    NormedSpace ℝ (SDEState n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
noncomputable local instance (priority := high) spdN3 (n : ℕ) :
    NormedAddCommGroup (SDEState n →L[ℝ] SDEState n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
noncomputable local instance (priority := high) spdN4 (n : ℕ) :
    NormedSpace ℝ (SDEState n →L[ℝ] SDEState n →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance (priority := high) spdH1 (n : ℕ) : AddHomClass (SDEState n →L[ℝ] ℝ) (SDEState n) ℝ :=
  inferInstance
local instance (priority := high) spdH2 (n : ℕ) :
    AddMonoidHomClass (SDEState n →L[ℝ] ℝ) (SDEState n) ℝ := inferInstance
local instance (priority := high) spdH3 (n : ℕ) :
    MulActionHomClass (SDEState n →L[ℝ] ℝ) ℝ (SDEState n) ℝ := inferInstance
local instance (priority := high) spdH4 (n m : ℕ) :
    AddHomClass (SDEState n →L[ℝ] SDEState m) (SDEState n) (SDEState m) := inferInstance
local instance (priority := high) spdH5 (n m : ℕ) :
    AddMonoidHomClass (SDEState n →L[ℝ] SDEState m) (SDEState n) (SDEState m) := inferInstance
local instance (priority := high) spdH6 (n m : ℕ) :
    MulActionHomClass (SDEState n →L[ℝ] SDEState m) ℝ (SDEState n) (SDEState m) := inferInstance
local instance (priority := high) spdQ1 : ContinuousSMul ℚ≥0 ℝ := inferInstance
noncomputable local instance (priority := high) spdM1 (n : ℕ) : MulAction ℝ (SDEState n →L[ℝ] ℝ) :=
  inferInstance
noncomputable local instance (priority := high) spdM2 (n : ℕ) :
    MulAction ℝ (SDEState n →L[ℝ] SDEState n →L[ℝ] ℝ) := inferInstance



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
  exact (integrableOn_const (by (first | simp only [Real.volume_Ioc, sub_zero, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true] | simp))).indicator measurableSet_Ioc

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
    first | linarith only [hn, mul_lt_mul_of_pos_right h2n hδ] | nlinarith
  obtain ⟨p, hp1, hp2, hp3, hp4⟩ := Set.mem_iUnion.1 (hall n)
  have := hδuc (dyTime t p.1.1 p.1.2) ⟨zero_le, dyTime_le t hp1⟩
    (dyTime t p.2.1 p.2.2) ⟨zero_le, dyTime_le t hp2⟩
    (by rw [NNReal.dist_eq]; exact lt_of_le_of_lt hp3 htn)
  rw [Real.dist_eq] at this
  first | linarith only [this, hp4] | linarith

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
      (first | simp only [dyTime, this, mul_zero, zero_div] | simp [dyTime, this])
    rw [hu, hd, Real.toNNReal_zero, sub_self, abs_zero]
    exact hη
  set y : ℕ → ℝ := fun m => u * 2 ^ (m + n) / t.val with hy
  set s : ℕ → ℝ≥0 := fun m => dyTime t (m + n) ⌊y m⌋₊ with hs
  have hsR : ∀ m, (s m : ℝ) = (⌊y m⌋₊ : ℝ) * t.val / 2 ^ (m + n) := fun m => by
    (first | simp only [hs, dyTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.val_eq_coe] | simp [hs, dyTime])
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
  have hdk : (dyTime t n k : ℝ) = (k : ℝ) * t.val / 2 ^ n := by (first | simp only [dyTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat, NNReal.val_eq_coe] | simp [dyTime])
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
      simpa only [NNReal.val_eq_coe, sub_zero] using (tendsto_const_nhds (x := u)).sub hpow
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds hs_gt hs_le
  have hnn : Tendsto s atTop (𝓝 u.toNNReal) := by
    have := (continuous_real_toNNReal.tendsto u).comp hreal
    simpa only [Function.comp_def, Real.toNNReal_coe] using this
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
  (first | simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, map_sum, map_smul, smul_eq_mul] | simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr])

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
  simpa only [id_eq, Function.comp_def, one_smul] using h

theorem line_hasDerivAt2 {f : E → ℝ} (hf : ContDiff ℝ 2 f) (u v : E) :
    HasDerivAt (fun r : ℝ => fderiv ℝ f (u + r • v) v) (fderiv ℝ (fderiv ℝ f) u v v) 0 := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hc : ∀ w, HasFDerivAt (fun w => fderiv ℝ f w v) ((fderiv ℝ (fderiv ℝ f) w).flip v) w :=
    fun w => by simpa only [ContinuousLinearMap.comp_zero, zero_add] using (hd w).hasFDerivAt.clm_apply (hasFDerivAt_const v w)
  have h := (hc (u + (0 : ℝ) • v)).comp_hasDerivAt (0 : ℝ)
    (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add u)
  simpa only [id_eq, Function.comp_def, zero_smul, add_zero, one_smul, ContinuousLinearMap.flip_apply] using h

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
  (first | simp only [ixc, pack, Fin.lastCases_castSucc, Fin.addCases_left] | simp [pack, ixc])

@[simp] theorem pack_iyc (x y : SDEState d) (a : ℝ) (k : Fin d) : pack x y a (iyc k) = y k := by
  show Fin.lastCases a (fun j => Fin.addCases (fun k => x k) (fun k => y k) j)
    (Fin.castSucc (Fin.natAdd d k)) = y k
  rw [Fin.lastCases_castSucc, Fin.addCases_right]

@[simp] theorem pack_iac (x y : SDEState d) (a : ℝ) : pack x y a iac = a := by
  (first | simp only [iac, pack, Fin.lastCases_last] | simp [pack, iac])

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
  pack_ext (fun k => by (first | simp only [eac, PiLp.add_apply, pack_ixc, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, mul_zero, add_zero] | simp [eac])) (fun k => by (first | simp only [eac, PiLp.add_apply, pack_iyc, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul, mul_zero, add_zero] | simp [eac])) (by (first | simp only [eac, PiLp.add_apply, pack_iac, PiLp.smul_apply, smul_eq_mul, mul_one] | simp [eac]))

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
  refine ⟨fun t ω => by (first | simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, NNReal.val_eq_coe, intervalIntegrable_const] | simp), fun t => ⟨fun _ _ _ => 0, fun _ _ _ => measurable_const,
    fun _ => ⟨0, fun _ _ _ => by simp⟩, ?_, ?_⟩⟩
  · convert (show TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop fun _ => 0 from
      fun ε hε => by (first | simp only [edist_self, nonpos_iff_eq_zero, hε.ne', Set.ofPred_false, measure_empty, tendsto_const_nhds_iff] | simp [hε.ne'])) using 1
    funext n ω
    have hz : ∀ u, itoStepValue t n (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) u ω = 0 := fun u =>
      Finset.sum_eq_zero fun k _ => ite_self _
    (first | simp only [hz, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, NNReal.val_eq_coe, intervalIntegral.integral_zero] | simp [hz])
  · convert (show TendstoInMeasure P (fun (_ : ℕ) (_ : Ω) => (0 : ℝ)) atTop fun _ => 0 from
      fun ε hε => by (first | simp only [edist_self, nonpos_iff_eq_zero, hε.ne', Set.ofPred_false, measure_empty, tendsto_const_nhds_iff] | simp [hε.ne'])) using 1
    funext n ω; (first | simp only [itoStepSum, zero_mul, Finset.sum_const_zero] | simp [itoStepSum])

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

theorem abs_packcol_le (σx σy : SDEDiffusion d) (j : Fin d) (i : Fin (d + d + 1)) :
    |pack (scol σx j) (scol σy j) 0 i| ≤ ‖σx‖ + ‖σy‖ := by
  have h1 := norm_nonneg σx
  have h2 := norm_nonneg σy
  induction i using Fin.lastCases with
  | last => rw [show pack (scol σx j) (scol σy j) 0 (Fin.last _) = 0 from pack_iac _ _ _]; (first | simp only [abs_zero, ge_iff_le] | simp); linarith
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
  | last => rw [show pack u v 0 (Fin.last _) = 0 from pack_iac _ _ _]; (first | simp only [abs_zero, ge_iff_le] | simp); linarith
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
        (first | simp only [probReal_univ, smul_eq_mul, one_mul, zero_add] | simp)

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
  pack_ext (fun k => by (first | simp only [pack_ixc, PiLp.add_apply, PiLp.zero_apply, add_zero] | simp)) (fun k => by (first | simp only [pack_iyc, PiLp.add_apply, PiLp.zero_apply, zero_add] | simp)) (by (first | simp only [pack_iac, PiLp.add_apply, add_zero] | simp))

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
      (first | simp only [NNReal.val_eq_coe, pack_iac, NNReal.coe_zero, intervalIntegral.integral_same, Finset.sum_const_zero, add_zero, zero_add, U, A, JU, bU] | simp [U, JU, bU, A])
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
      (first | simp only [NNReal.val_eq_coe, NNReal.coe_zero, intervalIntegral.integral_same, A] | simp [A])
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
    refine ⟨Lm + max C 0 / δ, by first | exact add_nonneg Lm.coe_nonneg (div_nonneg (le_max_right _ _) hδpos.le) | positivity,
      fun x hx y hy => ?_⟩
    by_cases hxy : dist x y < δ
    · obtain ⟨z, hzT, hxz⟩ : ∃ z ∈ T, x ∈ Metric.ball (z : α) (r z / 2) := by
        have := hT hx; simp only [Set.mem_iUnion] at this
        obtain ⟨z, hz, h⟩ := this; exact ⟨z, hz, h⟩
      have hδz : δ ≤ r z / 2 := Finset.inf'_le _ hzT
      have hx' : x ∈ Metric.ball (z : α) (r z) ∩ s :=
        ⟨Metric.ball_subset_ball (by first | linarith only [hr z] | linarith [hr z]) hxz, hKs hx⟩
      have hy' : y ∈ Metric.ball (z : α) (r z) ∩ s := by
        refine ⟨?_, hKs hy⟩
        rw [Metric.mem_ball] at hxz ⊢
        calc dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
          _ < δ + r z / 2 := by rw [dist_comm]; exact add_lt_add hxy hxz
          _ ≤ r z := by first | linarith only [hδz] | linarith
      have h1 := (hL z).dist_le_mul x hx' y hy'
      have h2 : (L z : ℝ) ≤ Lm := by exact_mod_cast Finset.le_sup (f := L) hzT
      have h3 : 0 ≤ max C 0 / δ * dist x y := by
        first | exact mul_nonneg (div_nonneg (le_max_right _ _) hδpos.le) dist_nonneg | positivity
      first | linarith only [h1, h3, mul_le_mul_of_nonneg_right h2 (dist_nonneg (x := x) (y := y))] | nlinarith [dist_nonneg (x := x) (y := y)]
    · replace hxy := not_lt.1 hxy
      have h1 : dist (f x) (f y) ≤ max C 0 :=
        (hC ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (le_max_left _ _)
      have h2 : max C 0 ≤ max C 0 / δ * dist x y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hδpos]
        exact mul_le_mul_of_nonneg_left hxy (le_max_right _ _)
      have h3 : 0 ≤ (Lm : ℝ) * dist x y := by first | exact mul_nonneg Lm.coe_nonneg dist_nonneg | positivity
      first | linarith only [h1, h2, h3] | nlinarith
  · have hK0 : K = ∅ := by
      rw [Finset.not_nonempty_iff_eq_empty] at hTn
      subst hTn; simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.subset_empty_iff] using hT
    exact ⟨0, le_rfl, fun x hx => by (first | simp only [hK0, Set.mem_empty_iff_false] at hx | simp [hK0] at hx)⟩

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
  first
  | calc |max (-M) (min M a) - max (-M) (min M b)| = |max (min M a) (-M) - max (min M b) (-M)| := by
          rw [max_comm (-M), max_comm (-M)]
      _ ≤ |min M a - min M b| := abs_max_sub_max_le_abs _ _ _
      _ ≤ |a - b| := by
          refine (abs_min_sub_min_le_max M a M b).trans ?_
          rw [sub_self, abs_zero]; exact max_le (abs_nonneg _) le_rfl
  | rw [abs_le]
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
    _ = d * M := by (first | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] | simp)

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
      _ = (Fintype.card ι * Lb R) * ‖x - y‖ := by (first | simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] | simp [mul_assoc])
  refine ⟨s₁, fun R => ∑ k : ι, (|φ k (clampM ((R : ℝ) + 3) 0)| + Lb R * (2 * (d * ((R : ℝ) + 3)))),
    fun R => Fintype.card ι * Lb R, fun R => ?_,
    fun R => by first | exact mul_nonneg (Nat.cast_nonneg _) (hLb0 R) | (have := hLb0 R; positivity),
    fun R x => ?_, hlip, fun R x hx => ?_⟩
  · exact LipschitzWith.continuous (K := ⟨Fintype.card ι * Lb R, by first | exact mul_nonneg (Nat.cast_nonneg _) (hLb0 R) | (have := hLb0 R; positivity)⟩)
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
      ext y; (first | simp only [hKdef, forall_and, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff] | simp [hKdef, forall_and])
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
  have h0 : ∀ i, |(0 : SDEState n) i| ≤ M := fun i => by simpa only [PiLp.zero_apply, abs_zero] using hM
  refine ⟨L, L * (n * M) + |h (posPart 0)|, hL0,
    by first | exact add_nonneg (mul_nonneg hL0 (mul_nonneg (Nat.cast_nonneg n) hM)) (abs_nonneg _) | positivity,
    fun x y hx hy => ⟨?_, ?_⟩⟩
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
  have : orthant n = ⋂ i, {y : SDEState n | 0 ≤ y i} := by ext y; (first | simp only [orthant, Set.mem_ofPred_eq, Set.mem_iInter] | simp [orthant])
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

noncomputable def mneg (v : ℝ) : ℝ := max (-v) 0

theorem mneg_continuous : Continuous mneg := continuous_neg.max continuous_const

theorem mneg_nonneg (v : ℝ) : 0 ≤ mneg v := le_max_right _ _

theorem mneg_mul (v : ℝ) : mneg v * v = -(mneg v ^ 2) := by
  unfold mneg
  rcases le_total v 0 with h | h
  · rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_right (by linarith)]; ring

theorem mneg_eq_zero_iff (v : ℝ) : mneg v = 0 ↔ 0 ≤ v := by
  unfold mneg
  constructor
  · intro h; by_contra hv; push Not at hv
    rw [max_eq_left (by linarith)] at h; linarith
  · intro h; exact max_eq_right (by linarith)

theorem hasDerivAt_mneg_pow (k : ℕ) (v : ℝ) :
    HasDerivAt (fun w => mneg w ^ (k + 2)) (-((k : ℝ) + 2) * mneg v ^ (k + 1)) v := by
  have hne : ∀ y ≠ (0 : ℝ), HasDerivAt (fun w => mneg w ^ (k + 2))
      (-((k : ℝ) + 2) * mneg y ^ (k + 1)) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · have hev : (fun w => mneg w ^ (k + 2)) =ᶠ[𝓝 y] fun w => (-w) ^ (k + 2) := by
        filter_upwards [gt_mem_nhds hlt] with w hw
        simp only [mneg, max_eq_left (by linarith : (0 : ℝ) ≤ -w)]
      have hd := (hasDerivAt_neg y).pow (k + 2)
      have hm : mneg y = -y := by simp only [mneg, max_eq_left (by linarith : (0 : ℝ) ≤ -y)]
      refine (hd.congr_of_eventuallyEq hev).congr_deriv ?_
      rw [hm, show k + 2 - 1 = k + 1 by omega]; push_cast; ring
    · have hev : (fun w => mneg w ^ (k + 2)) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
        filter_upwards [lt_mem_nhds hgt] with w hw
        simp only [mneg, max_eq_right (by linarith : -w ≤ 0)]; ring
      have hm : mneg y = 0 := by simp only [mneg, max_eq_right (by linarith : -y ≤ 0)]
      refine ((hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev).congr_deriv ?_
      rw [hm]; ring
  rcases eq_or_ne v 0 with rfl | hv
  · exact hasDerivAt_of_hasDerivAt_of_ne hne ((mneg_continuous.pow _).continuousAt)
      ((continuous_const.mul (mneg_continuous.pow _)).continuousAt)
  · exact hne v hv

/-- `φ(v) = (v⁻)³`. -/
noncomputable def phi3 (v : ℝ) : ℝ := mneg v ^ 3

theorem phi3_nonneg (v : ℝ) : 0 ≤ phi3 v := pow_nonneg (mneg_nonneg v) 3

theorem hasDerivAt_phi3 (v : ℝ) : HasDerivAt phi3 (-3 * mneg v ^ 2) v := by
  have := hasDerivAt_mneg_pow 1 v
  exact this.congr_deriv (by push_cast; ring)

theorem deriv_phi3 : deriv phi3 = fun v => -3 * mneg v ^ 2 :=
  funext fun v => (hasDerivAt_phi3 v).deriv

theorem hasDerivAt_dphi3 (v : ℝ) : HasDerivAt (fun w => -3 * mneg w ^ 2) (6 * mneg v) v := by
  have := (hasDerivAt_mneg_pow 0 v).const_mul (-3)
  exact this.congr_deriv (by push_cast; ring)

theorem deriv2_phi3 : deriv (deriv phi3) = fun v => 6 * mneg v := by
  rw [deriv_phi3]; exact funext fun v => (hasDerivAt_dphi3 v).deriv

theorem phi3_contDiff : ContDiff ℝ 2 phi3 := by
  rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun v => (hasDerivAt_phi3 v).differentiableAt, by (first | simp only [WithTop.one_ne_top, analyticOn_univ, IsEmpty.forall_iff] | simp), ?_⟩
  rw [deriv_phi3, show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiff_succ_iff_deriv]
  refine ⟨fun v => (hasDerivAt_dphi3 v).differentiableAt, by (first | simp only [WithTop.zero_ne_top, neg_mul, analyticOn_univ, IsEmpty.forall_iff] | simp), ?_⟩
  rw [show deriv (fun w => -3 * mneg w ^ 2) = fun v => 6 * mneg v from
    funext fun v => (hasDerivAt_dphi3 v).deriv]
  exact contDiff_zero.2 (continuous_const.mul mneg_continuous)

theorem phi3_d1 (v : ℝ) : deriv phi3 v * v = 3 * phi3 v := by
  rw [deriv_phi3, phi3, mul_assoc, show mneg v ^ 2 * v = mneg v * (mneg v * v) by ring, mneg_mul]
  ring

theorem phi3_d2 (v : ℝ) : deriv (deriv phi3) v * v ^ 2 = 6 * phi3 v := by
  rw [deriv2_phi3, phi3, show 6 * mneg v * v ^ 2 = 6 * (mneg v * v) * v by ring, mneg_mul,
    show 6 * -mneg v ^ 2 * v = -6 * mneg v * (mneg v * v) by ring, mneg_mul]
  ring

theorem phi3_eq_zero_iff (v : ℝ) : phi3 v = 0 ↔ 0 ≤ v := by
  rw [phi3, pow_eq_zero_iff (by norm_num), mneg_eq_zero_iff]

variable {d : ℕ}

/-- `Φ(u) = Σ_k φ(x_k)`. -/
noncomputable def Phif (u : SDEState (d + d + 1)) : ℝ := ∑ k, phi3 (u (ixc k))

/-- Inner orthant test function `e^{-a} Φ`. -/
noncomputable def H0f (u : SDEState (d + d + 1)) : ℝ := Real.exp (-u iac) * Phif u

/-- Orthant test function `e^{-a} χ_r(|x|²) Φ`. -/
noncomputable def Hf (r : ℝ) (u : SDEState (d + d + 1)) : ℝ :=
  Real.exp (-u iac) * (cutoff r (Nxf u) * Phif u)

theorem Phif_contDiff : ContDiff ℝ 2 (Phif (d := d)) := by
  unfold Phif
  exact ContDiff.sum fun k _ => phi3_contDiff.comp (coord_contDiff _)

theorem Phif_nonneg (u : SDEState (d + d + 1)) : 0 ≤ Phif u :=
  Finset.sum_nonneg fun k _ => phi3_nonneg _

theorem H0f_contDiff : ContDiff ℝ 2 (H0f (d := d)) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul Phif_contDiff

theorem Hf_contDiff (r : ℝ) : ContDiff ℝ 2 (Hf (d := d) r) :=
  (Real.contDiff_exp.comp (coord_contDiff _).neg).mul
    (((cutoff_contDiff r).comp Nxf_contDiff).mul Phif_contDiff)

theorem Hf_nonneg (r : ℝ) (u : SDEState (d + d + 1)) : 0 ≤ Hf r u :=
  mul_nonneg (Real.exp_pos _).le (mul_nonneg (cutoff_nonneg _ _) (Phif_nonneg u))

theorem Hf_eq_H0f_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : Nxf u < r) :
    Hf r =ᶠ[𝓝 u] H0f := by
  have hc : ContinuousAt (Nxf (d := d)) u := (Nxf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (gt_mem_nhds hu)] with w hw
  simp only [Hf, H0f, cutoff_eq_one hw.le, one_mul]

theorem Hf_zero_nhds {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nxf u) :
    Hf r =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
  have hc : ContinuousAt (Nxf (d := d)) u := (Nxf_contDiff (n := 0)).continuous.continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hu)] with w hw
  simp only [Hf, cutoff_eq_zero hw.le, zero_mul, mul_zero]

theorem Hf_fderiv_zero {r : ℝ} {u : SDEState (d + d + 1)} (hu : r + 1 < Nxf u) :
    fderiv ℝ (Hf r) u = 0 ∧ fderiv ℝ (fderiv ℝ (Hf r)) u = 0 := by
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (Hf_zero_nhds hu)
  refine ⟨h1.trans (fderiv_const_apply _), h2.trans ?_⟩
  rw [show (fderiv ℝ fun _ : SDEState (d + d + 1) => (0 : ℝ)) = fun _ => 0 from
    funext fun w => fderiv_const_apply _]
  exact fderiv_const_apply _

theorem Hf_translate (r c : ℝ) (w : SDEState (d + d + 1)) :
    Hf r (w + c • (eac (d := d))) = Real.exp (-c) * Hf r w := by
  have hx : ∀ k, (w + c • (eac (d := d))) (ixc k) = w (ixc k) := fun k => by
    have : (eac (d := d)) (ixc k) = 0 := by (first | simp only [eac, pack_ixc, PiLp.zero_apply] | simp [eac])
    (first | simp only [PiLp.add_apply, PiLp.smul_apply, this, smul_eq_mul, mul_zero, add_zero] | simp [this])
  have ha : (w + c • (eac (d := d))) iac = w iac + c := by
    have : (eac (d := d)) iac = 1 := by (first | simp only [eac, pack_iac] | simp [eac])
    (first | simp only [PiLp.add_apply, PiLp.smul_apply, this, smul_eq_mul, mul_one] | simp [this])
  simp only [Hf, Nxf, Phif, hx, ha]
  rw [show -(w iac + c) = -c + -w iac by ring, Real.exp_add]
  ring

/-- `Hf` does not see the `y` block. -/
theorem Hf_translate_y (r : ℝ) (c : SDEState d) (w : SDEState (d + d + 1)) :
    Hf r (w + pack 0 c 0) = 1 * Hf r w := by
  have hx : ∀ k, (w + pack 0 c 0) (ixc k) = w (ixc k) := fun k => by (first | simp only [PiLp.add_apply, pack_ixc, PiLp.zero_apply, add_zero] | simp)
  have ha : (w + pack 0 c 0) iac = w iac := by (first | simp only [PiLp.add_apply, pack_iac, add_zero] | simp)
  simp only [Hf, Nxf, Phif, hx, ha, one_mul]

theorem Hf_fderiv_pack (r : ℝ) (x y : SDEState d) (a : ℝ) :
    fderiv ℝ (Hf r) (pack x y a) = Real.exp (-a) • fderiv ℝ (Hf r) (pack x 0 0) ∧
      fderiv ℝ (fderiv ℝ (Hf r)) (pack x y a) =
        Real.exp (-a) • fderiv ℝ (fderiv ℝ (Hf r)) (pack x 0 0) := by
  have h := fderiv12_translate (Hf_contDiff r) (a • (eac (d := d))) (Real.exp (-a))
    (fun w => Hf_translate r a w) (pack x y 0)
  have h' := fderiv12_translate (Hf_contDiff r) (pack 0 y 0) 1
    (fun w => Hf_translate_y r y w) (pack x 0 0)
  have e1 : pack x y 0 + a • (eac (d := d)) = pack x y a := by rw [pack_add_eac, zero_add]
  have e2 : pack x 0 0 + pack 0 y 0 = pack x y 0 := (pack_split x y).symm
  first
  | have k1 : fderiv ℝ (Hf r) (pack x y 0) = fderiv ℝ (Hf r) (pack x 0 0) :=
      ((congrArg (fderiv ℝ (Hf r)) e2).symm.trans h'.1).trans (one_smul ℝ _)
    have k2 : fderiv ℝ (fderiv ℝ (Hf r)) (pack x y 0) = fderiv ℝ (fderiv ℝ (Hf r)) (pack x 0 0) :=
      ((congrArg (fderiv ℝ (fderiv ℝ (Hf r))) e2).symm.trans h'.2).trans (one_smul ℝ _)
    exact ⟨((congrArg (fderiv ℝ (Hf r)) e1).symm.trans h.1).trans (congrArg _ k1),
      ((congrArg (fderiv ℝ (fderiv ℝ (Hf r))) e1).symm.trans h.2).trans (congrArg _ k2)⟩
  | rw [e1] at h; rw [e2, one_smul, one_smul] at h'
    rw [h.1, h.2, h'.1, h'.2]
    exact ⟨rfl, rfl⟩

theorem Hf_fderiv_eac (r : ℝ) (u : SDEState (d + d + 1)) :
    fderiv ℝ (Hf r) u (eac (d := d)) = -Hf r u := by
  refine fderiv_eq_of_line ((Hf_contDiff r).differentiable (by norm_num)) u _ ?_
  have e : (fun s : ℝ => Hf r (u + s • (eac (d := d)))) = fun s => Real.exp (-s) * Hf r u :=
    funext fun s => Hf_translate r s u
  rw [e]
  have := ((hasDerivAt_id (0 : ℝ)).neg.exp).mul_const (Hf r u)
  simpa only [Pi.neg_apply, id_eq, neg_zero, Real.exp_zero, mul_neg, mul_one, neg_mul, one_mul] using this

/-- `D H0(u) v = e^{-a} (Σ φ'(x_k) v_k - v_a Φ)`. -/
theorem H0f_fderiv (u v : SDEState (d + d + 1)) :
    fderiv ℝ H0f u v = Real.exp (-u iac) *
      ((∑ k, deriv phi3 (u (ixc k)) * v (ixc k)) - v iac * Phif u) := by
  refine fderiv_eq_of_line (H0f_contDiff.differentiable (by norm_num)) u v ?_
  have he := (((hasDerivAt_mul_const (v iac)).const_add (u iac)).neg (x := (0 : ℝ))).exp
  have hs : HasDerivAt (fun s : ℝ => ∑ k, phi3 (u (ixc k) + s * v (ixc k)))
      (∑ k, deriv phi3 (u (ixc k)) * v (ixc k)) 0 := by
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (v (ixc k))).const_add (u (ixc k))
    have h2 := (hasDerivAt_phi3 (u (ixc k) + id 0 * v (ixc k))).comp (0 : ℝ) h1
    rw [deriv_phi3]
    refine h2.congr_deriv ?_
    simp only [id, zero_mul, add_zero, one_mul]
  have e : (fun s : ℝ => H0f (u + s • v)) =
      fun s => Real.exp (-(u iac + s * v iac)) * ∑ k, phi3 (u (ixc k) + s * v (ixc k)) := by
    funext s; (first | simp only [H0f, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, neg_add_rev, Phif] | simp [H0f, Phif])
  rw [e]
  refine (he.mul hs).congr_deriv ?_
  simp only [Phif, Pi.neg_apply, zero_mul, add_zero, mul_zero]
  ring

/-- `D² H0(u)(v,v) = e^{-a} Σ φ''(x_k) v_k²` when `v_a = 0`. -/
theorem H0f_fderiv2 (u v : SDEState (d + d + 1)) (hv : v iac = 0) :
    fderiv ℝ (fderiv ℝ H0f) u v v = Real.exp (-u iac) *
      ∑ k, deriv (deriv phi3) (u (ixc k)) * v (ixc k) ^ 2 := by
  refine fderiv2_eq_of_line H0f_contDiff u v
    (φ' := fun s => Real.exp (-u iac) * ∑ k, (-3 * mneg (u (ixc k) + s * v (ixc k)) ^ 2) *
      v (ixc k)) (fun s => ?_) ?_
  · have e : (fun r : ℝ => H0f (u + r • v)) =
        fun r => Real.exp (-u iac) * ∑ k, phi3 (u (ixc k) + r * v (ixc k)) := by
      funext r; (first | simp only [H0f, PiLp.add_apply, PiLp.smul_apply, hv, smul_eq_mul, mul_zero, add_zero, Phif] | simp [H0f, Phif, hv])
    rw [e]
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun k _ => ?_)
    have h1 := ((hasDerivAt_id s).mul_const (v (ixc k))).const_add (u (ixc k))
    have h2 := (hasDerivAt_phi3 (u (ixc k) + id s * v (ixc k))).comp s h1
    exact h2.congr_deriv (by simp only [id, one_mul])
  · refine HasDerivAt.const_mul _ ?_
    rw [deriv2_phi3]
    refine HasDerivAt.fun_sum fun k _ => ?_
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (v (ixc k))).const_add (u (ixc k))
    have h2 := ((hasDerivAt_dphi3 (u (ixc k) + 0 * v (ixc k))).comp (0 : ℝ) h1).mul_const
      (v (ixc k))
    refine h2.congr_deriv ?_
    simp only [Function.comp_apply, zero_mul, add_zero, id, one_mul]
    ring

end M10k

section M10l
/-! M10l (b10 drift): generator of `Hf r` inside the ball and its global bound. -/
variable {d : ℕ}

theorem Phif_pack (x y : SDEState d) (a : ℝ) : Phif (pack x y a) = ∑ k, phi3 (x k) := by
  (first | simp only [Phif, pack_ixc] | simp [Phif])

theorem scol_apply' (s : SDEDiffusion d) (j k : Fin d) : scol s j k = s (k, j) := rfl

theorem Hf_drift_inside {r κ : ℝ} (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d)
    (by' : SDEState d) (x y : SDEState d) (a : ℝ) (hx : ‖x‖ ^ 2 < r) :
    driftGen (Hf r) κ σx bx σy by' x y a = Real.exp (-a) * ((∑ k, deriv phi3 (x k) * bx k) -
      κ * (∑ k, phi3 (x k)) + (1 / 2) * ∑ j, ∑ k, deriv (deriv phi3) (x k) * σx (k, j) ^ 2) := by
  have hN : Nxf (pack x y a) < r := by rw [Nxf_pack]; exact hx
  obtain ⟨h1, h2⟩ := fderiv12_congr_nhds (Hf_eq_H0f_nhds hN)
  unfold driftGen
  rw [h1, h2, H0f_fderiv, Finset.sum_congr rfl (fun j _ => H0f_fderiv2 _ _ (by (first | simp only [pack_iac] | simp)))]
  simp only [pack_ixc, pack_iac, Phif_pack, scol_apply']
  rw [← Finset.mul_sum]
  ring

theorem Hf_drift_inside_le {r κ c₀ : ℝ} (σx : SDEDiffusion d) (bx : SDEState d)
    (σy : SDEDiffusion d) (by' : SDEState d) (x y : SDEState d) (a : ℝ) (hx : ‖x‖ ^ 2 < r)
    (hk : ∀ k, deriv phi3 (x k) * bx k + (1 / 2) * ∑ j, deriv (deriv phi3) (x k) * σx (k, j) ^ 2
      ≤ c₀ * phi3 (x k)) :
    driftGen (Hf r) κ σx bx σy by' x y a ≤ Real.exp (-a) * ((c₀ - κ) * ∑ k, phi3 (x k)) := by
  rw [Hf_drift_inside σx bx σy by' x y a hx]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have hc : ∑ j, ∑ k, deriv (deriv phi3) (x k) * σx (k, j) ^ 2 =
      ∑ k, ∑ j, deriv (deriv phi3) (x k) * σx (k, j) ^ 2 := Finset.sum_comm
  have h2 : (1 / 2 : ℝ) * ∑ k, ∑ j, deriv (deriv phi3) (x k) * σx (k, j) ^ 2 =
      ∑ k, (1 / 2) * ∑ j, deriv (deriv phi3) (x k) * σx (k, j) ^ 2 := Finset.mul_sum _ _ _
  have hsum : ∑ k, (deriv phi3 (x k) * bx k +
      (1 / 2) * ∑ j, deriv (deriv phi3) (x k) * σx (k, j) ^ 2) ≤ ∑ k, c₀ * phi3 (x k) :=
    Finset.sum_le_sum fun k _ => hk k
  rw [Finset.sum_add_distrib] at hsum
  have h3 : ∑ k, c₀ * phi3 (x k) = c₀ * ∑ k, phi3 (x k) := (Finset.mul_sum _ _ _).symm
  rw [hc, h2]
  first | linarith only [hsum, h3] | nlinarith

/-- The Kolmogorov form of the coefficient condition. -/
theorem phi3_coef_le (v F G : ℝ) (Γc : Fin d → ℝ) {c₀ : ℝ}
    (hc : 3 * |F| + 3 * G ^ 2 * ∑ j, Γc j ^ 2 ≤ c₀) :
    deriv phi3 v * (v * F) + (1 / 2) * ∑ j, deriv (deriv phi3) v * (v * G * Γc j) ^ 2
      ≤ c₀ * phi3 v := by
  have e1 : deriv phi3 v * (v * F) = 3 * phi3 v * F := by
    rw [← mul_assoc, phi3_d1]
  have e2 : ∀ j, deriv (deriv phi3) v * (v * G * Γc j) ^ 2 = 6 * phi3 v * (G ^ 2 * Γc j ^ 2) := by
    intro j
    rw [show deriv (deriv phi3) v * (v * G * Γc j) ^ 2 =
      (deriv (deriv phi3) v * v ^ 2) * (G ^ 2 * Γc j ^ 2) by ring, phi3_d2]
  rw [e1, Finset.sum_congr rfl fun j _ => e2 j, ← Finset.mul_sum]
  have hφ := phi3_nonneg v
  have hF := le_abs_self F
  have h3 : 3 * phi3 v * F ≤ 3 * phi3 v * |F| := mul_le_mul_of_nonneg_left hF (by positivity)
  have h4 : ∑ j, G ^ 2 * Γc j ^ 2 = G ^ 2 * ∑ j, Γc j ^ 2 := by rw [Finset.mul_sum]
  rw [h4]
  have h5 := mul_le_mul_of_nonneg_left hc hφ
  first | linarith only [h3, h5] | nlinarith

theorem norm_pack0_le (u v : SDEState d) : ‖pack u v 0‖ ≤ ((d : ℝ) + d + 1) * (‖u‖ + ‖v‖) := by
  calc ‖pack u v 0‖ ≤ ∑ i, |pack u v 0 i| := euc_norm_le_sum' _
    _ ≤ ∑ _i : Fin (d + d + 1), (‖u‖ + ‖v‖) := Finset.sum_le_sum fun i _ => abs_pack0_le u v i
    _ = ((d : ℝ) + d + 1) * (‖u‖ + ‖v‖) := by (first | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_add] | simp [mul_add])

theorem norm_packcol_le (σx σy : SDEDiffusion d) (j : Fin d) :
    ‖pack (scol σx j) (scol σy j) 0‖ ≤ ((d : ℝ) + d + 1) * (‖σx‖ + ‖σy‖) := by
  calc ‖pack (scol σx j) (scol σy j) 0‖ ≤ ∑ i, |pack (scol σx j) (scol σy j) 0 i| :=
        euc_norm_le_sum' _
    _ ≤ ∑ _i : Fin (d + d + 1), (‖σx‖ + ‖σy‖) :=
        Finset.sum_le_sum fun i _ => abs_packcol_le σx σy j i
    _ = ((d : ℝ) + d + 1) * (‖σx‖ + ‖σy‖) := by (first | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_add, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_add] | simp [mul_add])

theorem Hf_deriv_bound (r : ℝ) : ∃ B1 B2 : ℝ, 0 ≤ B1 ∧ 0 ≤ B2 ∧ ∀ x : SDEState d,
    ‖fderiv ℝ (Hf r) (pack x 0 0)‖ ≤ B1 ∧ ∀ i i' : Fin (d + d + 1),
      |fderiv ℝ (fderiv ℝ (Hf r)) (pack x 0 0) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1)| ≤ B2 := by
  set ρ : ℝ := |r| + 2 with hρ
  have hD1 : Continuous (fderiv ℝ (Hf (d := d) r)) :=
    (Hf_contDiff r).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (Hf (d := d) r))) :=
    ((Hf_contDiff r).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hp1 : Continuous fun x : SDEState d => pack x (0 : SDEState d) 0 :=
    pack_continuous continuous_id continuous_const continuous_const
  have K2 := isCompact_closedBall (0 : SDEState d) ρ
  obtain ⟨B1, hB1⟩ := K2.exists_bound_of_continuousOn (hD1.comp hp1).continuousOn
  have hB2e : ∀ i i' : Fin (d + d + 1), ∃ B, ∀ x ∈ Metric.closedBall (0 : SDEState d) ρ,
      ‖fderiv ℝ (fderiv ℝ (Hf r)) (pack x 0 0) (EuclideanSpace.single i 1)
        (EuclideanSpace.single i' 1)‖ ≤ B := fun i i' =>
    K2.exists_bound_of_continuousOn
      (f := fun x : SDEState d => fderiv ℝ (fderiv ℝ (Hf r)) (pack x 0 0)
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
  · obtain ⟨h1, h2⟩ := Hf_fderiv_zero (r := r) (u := pack x 0 0) (by rw [Nxf_pack]; exact hN)
    rw [h1, h2]
    exact ⟨by first | exact norm_zero.trans_le (le_max_right _ _) | (rw [norm_zero]; exact le_max_right _ _),
      fun i i' => by simpa only [zero_apply, abs_zero] using hB20⟩
  · have hxρ : ‖x‖ ≤ ρ := by
      by_contra hc
      replace hc := not_le.1 hc
      have hr0 := abs_nonneg r
      have hr1 := le_abs_self r
      have hxn := norm_nonneg x
      have hc' : |r| + 2 < ‖x‖ := hc
      first | linarith only [mul_lt_mul'' hc' hc' (add_nonneg (abs_nonneg r) zero_le_two) (add_nonneg (abs_nonneg r) zero_le_two), not_lt.1 hN, hr0, hr1, mul_nonneg hr0 hr0] | nlinarith
    have hmem : x ∈ Metric.closedBall (0 : SDEState d) ρ := mem_closedBall_zero_iff.2 hxρ
    refine ⟨(hB1 x hmem).trans (le_max_left _ _), fun i i' => ?_⟩
    have := hBc i i' x hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (hBc2 i i'))

/-- Global bound of the generator of `Hf r` (the clock term only helps). -/
theorem Hf_drift_bound (r S : ℝ) (hS : 0 ≤ S) : ∃ B : ℝ, 0 ≤ B ∧ ∀ κ : ℝ, 0 ≤ κ →
    ∀ (σx : SDEDiffusion d) (bx : SDEState d) (σy : SDEDiffusion d) (by' : SDEState d)
      (x y : SDEState d) (a : ℝ),
      (‖x‖ ^ 2 ≤ r + 1 → ‖σx‖ ≤ S ∧ ‖bx‖ ≤ S ∧ ‖σy‖ ≤ S ∧ ‖by'‖ ≤ S) →
      driftGen (Hf r) κ σx bx σy by' x y a ≤ Real.exp (-a) * B := by
  obtain ⟨B1, B2, hB1, hB2, hB⟩ := Hf_deriv_bound (d := d) r
  set D : ℝ := ((d : ℝ) + d + 1) * (S + S) with hD
  have hD0 : 0 ≤ D := by positivity
  have hd1 : (0 : ℝ) ≤ (d : ℝ) + d + 1 := by positivity
  have hBB : 0 ≤ B1 * D + (1 / 2) * (d * (B2 * D ^ 2)) :=
    add_nonneg (mul_nonneg hB1 hD0) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hB2 (pow_nonneg hD0 2))))
  refine ⟨B1 * D + (1 / 2) * (d * (B2 * D ^ 2)), hBB, fun κ hκ σx bx σy by' x y a hS' => ?_⟩
  have hea := Real.exp_pos (-a)
  by_cases hN : r + 1 < ‖x‖ ^ 2
  · obtain ⟨h1, h2⟩ := Hf_fderiv_zero (r := r) (u := pack x y a) (by rw [Nxf_pack]; exact hN)
    unfold driftGen
    rw [h1, h2]
    simp only [ContinuousLinearMap.zero_apply, Finset.sum_const_zero, mul_zero, add_zero]
    first | exact mul_nonneg hea.le hBB | positivity
  · obtain ⟨hσx, hbx, hσy, hby⟩ := hS' (not_lt.1 hN)
    obtain ⟨hL1, hL2⟩ := hB x
    obtain ⟨e1, e2⟩ := Hf_fderiv_pack r x y a
    unfold driftGen
    have hsplit : pack bx by' κ = pack bx by' 0 + κ • (eac (d := d)) := by
      rw [pack_add_eac, zero_add]
    have hk : fderiv ℝ (Hf r) (pack x y a) (κ • (eac (d := d))) ≤ 0 := by
      rw [map_smul, Hf_fderiv_eac, smul_eq_mul]
      have := Hf_nonneg r (pack x y a)
      first | linarith only [mul_nonneg hκ this] | nlinarith
    rw [hsplit, map_add]
    have t1 : fderiv ℝ (Hf r) (pack x y a) (pack bx by' 0) ≤ Real.exp (-a) * (B1 * D) := by
      rw [e1, ContinuousLinearMap.smul_apply, smul_eq_mul]
      refine mul_le_mul_of_nonneg_left ?_ hea.le
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      refine mul_le_mul hL1 ((norm_pack0_le _ _).trans ?_) (norm_nonneg _) hB1
      exact mul_le_mul_of_nonneg_left (add_le_add hbx hby) hd1
    have t2 : ∀ j, fderiv ℝ (fderiv ℝ (Hf r)) (pack x y a) (pack (scol σx j) (scol σy j) 0)
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
              first
              | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
              | simp [mul_add]
          _ ≤ D := mul_le_mul_of_nonneg_left (add_le_add hσx hσy) hd1
      have hcs0 : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      rw [clm2_coord]
      calc ∑ i, ∑ i', c i * c i' * fderiv ℝ (fderiv ℝ (Hf r)) (pack x 0 0)
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
        _ ≤ B2 * D ^ 2 := by
          first | exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcs0 hcs 2) hB2 | gcongr
    have t3 : ∑ j, fderiv ℝ (fderiv ℝ (Hf r)) (pack x y a) (pack (scol σx j) (scol σy j) 0)
        (pack (scol σx j) (scol σy j) 0) ≤ d * (Real.exp (-a) * (B2 * D ^ 2)) := by
      calc _ ≤ ∑ _j : Fin d, Real.exp (-a) * (B2 * D ^ 2) := Finset.sum_le_sum fun j _ => t2 j
        _ = _ := by
          first | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] | simp
    first | linarith only [t1, hk, t3] | nlinarith

end M10l

section M10m
/-! M10m (b10 expectation): `E Hf_r(X_t) ≤ Hf_r(x₀) + B/M` along `(X, X, A)`. -/
variable {Ω : Type*} {d : ℕ}

theorem Hf_integrand_ok (r : ℝ) {X Y : ℝ≥0 → Ω → SDEState d} {HX HY : ℝ≥0 → Ω → SDEDiffusion d}
    (hHb : ∃ C, ∀ s ω, ‖X s ω‖ ^ 2 ≤ r + 1 → ‖HX s ω‖ ≤ C ∧ ‖HY s ω‖ ≤ C) :
    ∀ (i : Fin (d + d + 1)) (j : Fin d), ∃ C, ∀ s ω (a : ℝ), 0 ≤ a →
      |fderiv ℝ (Hf r) (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1) *
        pack (scol (HX s ω) j) (scol (HY s ω) j) 0 i| ≤ C := by
  intro i j
  obtain ⟨B, B2', hB0, -, hB⟩ := Hf_deriv_bound (d := d) r
  obtain ⟨C₀, hC₀⟩ := hHb
  refine ⟨B * (2 * |C₀|), fun s ω a ha => ?_⟩
  by_cases hN : r + 1 < ‖X s ω‖ ^ 2
  · have h0 := (Hf_fderiv_zero (r := r) (u := pack (X s ω) (Y s ω) a)
      (by rw [Nxf_pack]; exact hN)).1
    rw [h0]
    simp only [ContinuousLinearMap.zero_apply, zero_mul, abs_zero]
    exact mul_nonneg hB0 (by positivity)
  · obtain ⟨h1, h2⟩ := hC₀ s ω (not_lt.1 hN)
    have hea := Real.exp_pos (-a)
    have he := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
    have hd' : |fderiv ℝ (Hf r) (pack (X s ω) (Y s ω) a) (EuclideanSpace.single i 1)| ≤ B := by
      rw [(Hf_fderiv_pack r (X s ω) (Y s ω) a).1]
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

theorem Hf_drift_continuous (r : ℝ) {α : Type*} [TopologicalSpace α] {κ a : α → ℝ}
    {σx σy : α → SDEDiffusion d} {bx by' x y : α → SDEState d}
    (hκ : Continuous κ) (hσx : Continuous σx) (hbx : Continuous bx) (hσy : Continuous σy)
    (hby : Continuous by') (hx : Continuous x) (hy : Continuous y) (ha : Continuous a) :
    Continuous fun p => driftGen (Hf r) (κ p) (σx p) (bx p) (σy p) (by' p) (x p) (y p) (a p) := by
  have hD1 : Continuous (fderiv ℝ (Hf (d := d) r)) :=
    (Hf_contDiff r).continuous_fderiv two_ne_zero
  have hD2 : Continuous (fderiv ℝ (fderiv ℝ (Hf (d := d) r))) :=
    ((Hf_contDiff r).fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hpk := pack_continuous hx hy ha
  unfold driftGen
  refine ((hD1.comp hpk).clm_apply (pack_continuous hbx hby hκ)).add
    (continuous_const.mul (continuous_finsetSum _ fun j _ => ?_))
  have hv := pack_continuous (scol_continuous hσx j) (scol_continuous hσy j)
    (continuous_const (y := (0 : ℝ)))
  exact ((hD2.comp hpk).clm_apply hv).clm_apply hv

/-- Pointwise: inside the ball the drift is `≤ 0`, outside the clock rate is `≥ M`. -/
theorem Hf_drift_le_kap {r c R B M : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hR : 0 ≤ R) (hc : 0 ≤ c) (hM : 0 < M) (hB : 0 ≤ B)
    (hr : r = (R + 1) ^ 2 + 1)
    (hk : ∀ x : SDEState d, ‖x‖ ^ 2 < r → ∀ k, deriv phi3 (x k) * b₀ x k +
      (1 / 2) * ∑ j, deriv (deriv phi3) (x k) * σ₀ x (k, j) ^ 2 ≤ c * phi3 (x k))
    {x y : SDEState d} {σy : SDEDiffusion d} {by' : SDEState d} (a : ℝ)
    (hBd : ∀ κ, 0 ≤ κ → driftGen (Hf r) κ (σ₀ x) (b₀ x) σy by' x y a ≤ Real.exp (-a) * B) :
    driftGen (Hf r) (kapX c M R x) (σ₀ x) (b₀ x) σy by' x y a ≤
      B * (1 / M) * (Real.exp (-a) * kapX c M R x) := by
  have hk0 : 0 ≤ kapX c M R x := kapX_nonneg hc hM.le x
  have hea := Real.exp_pos (-a)
  have hfirst : 0 ≤ B * (1 / M) * (Real.exp (-a) * kapX c M R x) :=
    mul_nonneg (mul_nonneg hB (one_div_nonneg.2 hM.le)) (mul_nonneg hea.le hk0)
  by_cases hin : ‖x‖ ^ 2 < r
  · refine (Hf_drift_inside_le (c₀ := c) _ _ _ _ x y a hin (hk x hin)).trans (le_trans ?_ hfirst)
    have hkc : c ≤ kapX c M R x := by
      unfold kapX; have := mul_nonneg hM.le (distB_nonneg R x); linarith
    have hΦ : 0 ≤ ∑ k, phi3 (x k) := Finset.sum_nonneg fun k _ => phi3_nonneg _
    have := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hkc) hΦ
    first | exact mul_nonpos_of_nonneg_of_nonpos hea.le this | nlinarith
  · have hx1 : R + 1 < ‖x‖ := by
      have h1 : (R + 1) ^ 2 < ‖x‖ ^ 2 := by rw [hr] at hin; (first | linarith only [not_lt.1 hin] | linarith [not_lt.1 hin])
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg x) h1
    have hdist : 1 ≤ distB R x := by unfold distB; exact le_max_of_le_right (by (first | linarith only [hx1] | linarith))
    have hkM : M ≤ kapX c M R x := by
      unfold kapX; have := mul_le_mul_of_nonneg_left hdist hM.le; (first | linarith only [this] | linarith)
    refine (hBd _ hk0).trans ?_
    have : B ≤ B * (1 / M) * kapX c M R x := by
      have h1 : 1 ≤ kapX c M R x / M := (one_le_div hM).2 hkM
      rw [show B * (1 / M) * kapX c M R x = B * (kapX c M R x / M) by ring]
      first | exact le_mul_of_one_le_right hB h1 | nlinarith
    calc Real.exp (-a) * B ≤ Real.exp (-a) * (B * (1 / M) * kapX c M R x) :=
          mul_le_mul_of_nonneg_left this hea.le
      _ = _ := by ring

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

/-- Pathwise: the `Hf`-generator integral is at most `B / M`. -/
theorem Hf_drift_integral_le {r c R B M : ℝ} {σ₀ : SDEState d → SDEDiffusion d}
    {b₀ : SDEState d → SDEState d} (hσ : Continuous σ₀) (hb : Continuous b₀)
    (hR : 0 ≤ R) (hc : 0 ≤ c) (hM : 0 < M) (hB : 0 ≤ B) (hr : r = (R + 1) ^ 2 + 1)
    (hk : ∀ x : SDEState d, ‖x‖ ^ 2 < r → ∀ k, deriv phi3 (x k) * b₀ x k +
      (1 / 2) * ∑ j, deriv (deriv phi3) (x k) * σ₀ x (k, j) ^ 2 ≤ c * phi3 (x k))
    {x : ℝ → SDEState d} (hx : Continuous x)
    (hBd : ∀ u κ, 0 ≤ κ → ∀ a, driftGen (Hf r) κ (σ₀ (x u)) (b₀ (x u)) (σ₀ (x u)) (b₀ (x u))
      (x u) (x u) a ≤ Real.exp (-a) * B)
    (t : ℝ) (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t, driftGen (Hf r) (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u)) (σ₀ (x u))
        (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kapX c M R (x v)) ≤
      B * (1 / M) := by
  have hgc : Continuous fun v => kapX c M R (x v) := kapX_comp_continuous c M R hx
  have hpc : Continuous fun u => ∫ v in (0 : ℝ)..u, kapX c M R (x v) :=
    continuous_iff_continuousAt.2 fun u => (hgc.integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hcongr : ∫ u in (0 : ℝ)..t, driftGen (Hf r) (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
        (σ₀ (x u)) (b₀ (x u)) (x u) (x u)
        (∫ v in (0 : ℝ)..((u.toNNReal : ℝ≥0) : ℝ), kapX c M R (x v)) =
      ∫ u in (0 : ℝ)..t, driftGen (Hf r) (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
        (σ₀ (x u)) (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..u, kapX c M R (x v)) := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by rw [Set.uIcc_of_le ht] at hu; exact hu.1
    simp only [Real.coe_toNNReal _ hu0]
  rw [hcongr]
  have hLc : Continuous fun u => driftGen (Hf r) (kapX c M R (x u)) (σ₀ (x u)) (b₀ (x u))
      (σ₀ (x u)) (b₀ (x u)) (x u) (x u) (∫ v in (0 : ℝ)..u, kapX c M R (x v)) :=
    Hf_drift_continuous r hgc (hσ.comp hx) (hb.comp hx) (hσ.comp hx) (hb.comp hx) hx hx hpc
  have hRc : Continuous fun u => B * (1 / M) *
      (Real.exp (-(∫ v in (0 : ℝ)..u, kapX c M R (x v))) * kapX c M R (x u)) :=
    continuous_const.mul ((Real.continuous_exp.comp hpc.neg).mul hgc)
  calc _ ≤ ∫ u in (0 : ℝ)..t, (B * (1 / M) *
        (Real.exp (-(∫ v in (0 : ℝ)..u, kapX c M R (x v))) * kapX c M R (x u))) :=
        intervalIntegral.integral_mono_on ht (hLc.intervalIntegrable _ _)
          (hRc.intervalIntegrable _ _) fun u _ =>
          Hf_drift_le_kap hR hc hM hB hr hk _ (fun κ hκ => hBd u κ hκ _)
    _ = B * (1 / M) * (1 - Real.exp (-(∫ v in (0 : ℝ)..t, kapX c M R (x v)))) := by
        rw [intervalIntegral.integral_const_mul, integral_exp_neg_primitive hgc]
    _ ≤ B * (1 / M) := by
        have h1 := Real.exp_pos (-(∫ v in (0 : ℝ)..t, kapX c M R (x v)))
        have h2 : 0 ≤ B * (1 / M) := mul_nonneg hB (one_div_nonneg.2 hM.le)
        first | linarith only [mul_nonneg h2 h1.le] | nlinarith

set_option maxHeartbeats 1000000 in
theorem lintegral_Hf_le [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (x₀ : SDEState d)
    {σ₀ : SDEState d → SDEDiffusion d} {b₀ : SDEState d → SDEState d}
    (hσ : Continuous σ₀) (hb : Continuous b₀) {X : ℝ≥0 → Ω → SDEState d}
    (hX : SolvesBrownianSDE P (fun p => σ₀ p.2) (fun p => b₀ p.2) W (fun _ => x₀) X)
    {r c R B M S : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c) (hM : 0 < M) (hr : r = (R + 1) ^ 2 + 1)
    (hk : ∀ x : SDEState d, ‖x‖ ^ 2 < r → ∀ k, deriv phi3 (x k) * b₀ x k +
      (1 / 2) * ∑ j, deriv (deriv phi3) (x k) * σ₀ x (k, j) ^ 2 ≤ c * phi3 (x k))
    (hS0 : ∀ x : SDEState d, ‖x‖ ^ 2 ≤ r + 1 → ‖σ₀ x‖ ≤ S ∧ ‖b₀ x‖ ≤ S)
    (hB : 0 ≤ B) (hBd : ∀ κ, 0 ≤ κ → ∀ (σx : SDEDiffusion d) (bx : SDEState d)
      (σy : SDEDiffusion d) (by' : SDEState d) (x y : SDEState d) (a : ℝ),
      (‖x‖ ^ 2 ≤ r + 1 → ‖σx‖ ≤ S ∧ ‖bx‖ ≤ S ∧ ‖σy‖ ≤ S ∧ ‖by'‖ ≤ S) →
      driftGen (Hf r) κ σx bx σy by' x y a ≤ Real.exp (-a) * B)
    (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (Hf r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω)))) ∂P ≤
      ENNReal.ofReal (Hf r (pack x₀ x₀ 0) + B * (1 / M)) := by
  obtain ⟨hXm, hXc, hXa, hX0, JX, -, -, hJX, -, hXeq⟩ := hX
  have hFb := Hf_integrand_ok (Ω := Ω) r (X := X) (Y := X) (HX := fun s ω => σ₀ (X s ω))
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
    (fun x _ => kapX_nonneg hc hM.le x) (Hf_contDiff r) hFb t
  have h := lintegral_le_of_ito (E := fun _ => (0 : ℝ)) (β := B * (1 / M))
    (ae_of_all _ fun ω => Hf_nonneg _ _) hZi hZ0 hZeq
    (ae_of_all _ fun ω => ?_) (integrable_const _)
  · simpa only [NNReal.val_eq_coe, one_div, ge_iff_le, integral_zero, add_zero] using h
  · rw [add_zero]
    exact Hf_drift_integral_le hσ hb hR hc hM hB hr hk
      (x := fun u => X u.toNNReal ω) ((hXc ω).comp continuous_real_toNNReal)
      (fun u κ hκ a => hBd κ hκ _ _ _ _ _ _ a
        (fun h => ⟨(hS0 _ h).1, (hS0 _ h).2, (hS0 _ h).1, (hS0 _ h).2⟩)) t.val t.2

theorem measurable_Hf_path [MeasurableSpace Ω] {X : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hXc : ∀ ω, Continuous fun s => X s ω) (r c M R : ℝ)
    (t : ℝ≥0) :
    Measurable fun ω => Hf r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω))) := by
  have hA : Measurable fun ω => ∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω) :=
    measurable_intervalIntegral_of_continuous _ t
      (fun s _ => (kapX_comp_continuous c M R continuous_id).measurable.comp (hXm s))
      (fun ω => kapX_comp_continuous c M R (hXc ω))
  exact (Hf_contDiff (d := d) r).continuous.measurable.comp
    ((pack_continuous continuous_fst (continuous_fst.comp continuous_snd)
      (continuous_snd.comp continuous_snd)).measurable.comp
      ((hXm t).prodMk ((hXm t).prodMk hA)))

/-- Markov step for the orthant functional `Φ(x) = Σ_k (x_k⁻)³`. -/
theorem prob_neg_le [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → SDEState d}
    (hXm : ∀ s, Measurable (X s)) (hXc : ∀ ω, Continuous fun s => X s ω)
    {r c M R K ε : ℝ} (hr : r = (R + 1) ^ 2 + 1) (hR : 0 ≤ R) (hε : 0 < ε) (t : ℝ≥0)
    (hI : ∫⁻ ω, ENNReal.ofReal (Hf r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω)))) ∂P ≤ ENNReal.ofReal K) :
    P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, phi3 (X t ω k)} ≤
      ENNReal.ofReal (K / (Real.exp (-(c * t.val)) * ε)) := by
  set δ : ℝ := Real.exp (-(c * t.val)) * ε with hδ
  have hδ0 : 0 < δ := mul_pos (Real.exp_pos _) hε
  have hsub : {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, phi3 (X t ω k)} ⊆
      {ω | ENNReal.ofReal δ ≤ ENNReal.ofReal (Hf r (pack (X t ω) (X t ω)
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
      rw [hr]; first | linarith only [this, hR] | nlinarith
    simp only [Hf, Nxf_pack, pack_iac, cutoff_eq_one hXt, one_mul, Phif_pack]
    rw [hδ, show t.val * c = c * t.val by ring]
    exact mul_le_mul_of_nonneg_left hQ.le (Real.exp_pos _).le
  have hmeas : AEMeasurable (fun ω => ENNReal.ofReal (Hf r (pack (X t ω) (X t ω)
      (∫ u in (0 : ℝ)..t.val, kapX c M R (X u.toNNReal ω))))) P :=
    (ENNReal.measurable_ofReal.comp (measurable_Hf_path hXm hXc r c M R t)).aemeasurable
  have h1 : ENNReal.ofReal δ * P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, phi3 (X t ω k)} ≤
      ENNReal.ofReal K :=
    ((mul_le_mul' le_rfl (measure_mono hsub)).trans
      (mul_meas_ge_le_lintegral₀ hmeas _)).trans hI
  have hne : ENNReal.ofReal δ ≠ 0 := by simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using hδ0
  calc P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, phi3 (X t ω k)}
      = (ENNReal.ofReal δ)⁻¹ * (ENNReal.ofReal δ *
          P {ω | (∀ s ≤ t, ‖X s ω‖ ≤ R) ∧ ε < ∑ k, phi3 (X t ω k)}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]
    _ ≤ (ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal K := mul_le_mul' le_rfl h1
    _ = ENNReal.ofReal (K / δ) := by
        rw [ENNReal.ofReal_div_of_pos hδ0, ENNReal.div_eq_inv_mul]

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

/-- The Kolmogorov coefficient condition on the ball `‖x‖² < r`, for some constant `c ≥ 0`. -/
theorem kolm_phi3_coef (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {r : ℝ} (hr : 2 ≤ r) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : SDEState n, ‖x‖ ^ 2 < r → ∀ k,
      deriv phi3 (x k) * drift C (0, x) k +
        (1 / 2) * ∑ j, deriv (deriv phi3) (x k) * diffusion C (0, x) (k, j) ^ 2 ≤
          c * phi3 (x k) := by
  have hr0 : 0 ≤ r := by linarith
  choose Lf Gf hLf hGf hf using fun k => locLip_posPart_box (hC k).1 hr0
  choose Lg Gg hLg hGg hg using fun k => locLip_posPart_box (hC k).2 hr0
  set T : Fin n → ℝ := fun k => 3 * Gf k + 3 * Gg k ^ 2 * ∑ j, C.Γ j k ^ 2 with hT
  have hT0 : ∀ k, 0 ≤ T k := fun k => by
    simp only [hT]; have := hGf k; positivity
  refine ⟨∑ k, T k, Finset.sum_nonneg fun k _ => hT0 k, fun x hx k => ?_⟩
  have hxr : ‖x‖ ≤ r := by first | linarith only [hx, hr, sq_nonneg (‖x‖ - 1)] | nlinarith [norm_nonneg x]
  have hbox : ∀ i, |x i| ≤ r := fun i => by
    have := PiLp.norm_apply_le x i
    rw [Real.norm_eq_abs] at this
    linarith
  have hF := (hf k x x hbox hbox).2
  have hG := (hg k x x hbox hbox).2
  have hG2 : C.g k (posPart x) ^ 2 ≤ Gg k ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hG 2
  have hS : 0 ≤ ∑ j, C.Γ j k ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hck : 3 * |C.f k (posPart x)| + 3 * C.g k (posPart x) ^ 2 * ∑ j, C.Γ j k ^ 2 ≤
      ∑ k, T k := by
    refine le_trans ?_ (Finset.single_le_sum (fun k _ => hT0 k) (Finset.mem_univ k))
    simp only [hT]
    have := mul_le_mul_of_nonneg_right hG2 hS
    first | linarith only [hF, this] | nlinarith
  exact phi3_coef_le (x k) (C.f k (posPart x)) (C.g k (posPart x)) (fun j => C.Γ j k) hck

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

/-- The `y`-block of a packed vector, as a continuous linear map. -/
noncomputable def yOfL : SDEState (d + d + 1) →L[ℝ] SDEState d :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun k => v (iyc k))
      map_add' := fun u v => by ext k; (first | simp only [PiLp.add_apply] | simp)
      map_smul' := fun r v => by ext k; simp }

@[simp] theorem yOfL_apply (v : SDEState (d + d + 1)) (k : Fin d) : yOfL v k = v (iyc k) := rfl

theorem yOfL_pack (x y : SDEState d) (a : ℝ) : yOfL (pack x y a) = y := by
  ext k; (first | simp only [yOfL_apply, pack_iyc] | simp)

theorem yOfL_line (x y : SDEState d) (a r : ℝ) (v : SDEState (d + d + 1)) :
    yOfL (pack x y a + r • v) = y + r • yOfL v := by
  rw [map_add, map_smul, yOfL_pack]

theorem iac_line (x y : SDEState d) (a r : ℝ) (v : SDEState (d + d + 1)) :
    (pack x y a + r • v) iac = a + r * v iac := by
  (first | simp only [PiLp.add_apply, pack_iac, PiLp.smul_apply, smul_eq_mul] | simp)

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
  (first | simp only [FG, pack_iac, yOfL_pack] | simp [FG, yOfL_pack])

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
    simpa only [neg_add_rev, mul_neg, neg_mul, zero_mul, add_zero, one_mul, zero_smul] using this
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
    congr 1; ext k; (first | simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero] | simp [EuclideanSpace.single_apply])
  have hiac : (EuclideanSpace.single i c : SDEState (d + d + 1)) iac = 0 := by
    rw [EuclideanSpace.single_apply]
    split_ifs with h
    · rw [hc, ← h]; (first | simp only [pack_iac] | simp)
    · rfl
  have hy : ‖yOfL (EuclideanSpace.single i c : SDEState (d + d + 1))‖ ≤ ‖w‖ := by
    refine qf_norm_mono fun k => ?_
    rw [yOfL_apply, EuclideanSpace.single_apply]
    split_ifs with h
    · rw [hc, ← h]; (first | simp only [pack_iyc, Std.le_refl] | simp)
    · (first | simp only [abs_zero, abs_nonneg] | simp)
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
    fun h => by (first | simp only [WithTop.one_ne_top] at h | simp at h), ?_⟩
  rw [hsat_deriv]
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem hsat_d2 (m u : ℝ) :
    HasDerivAt (fun v => 1 - Real.smoothTransition (v - m))
      (-(deriv Real.smoothTransition (u - m))) u := by
  have h : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (u - m)) (u - m) :=
    (Real.smoothTransition.contDiff (n := 1)).differentiable one_ne_zero |>.differentiableAt
      |>.hasDerivAt
  have h2 := (h.comp u ((hasDerivAt_id u).sub_const m)).const_sub 1
  simpa only [id_eq, Function.comp_apply, mul_one] using h2

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
  · (first | simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] | simp)
  · have : s ≤ m := by
      rcases Set.mem_uIcc.1 hs with h | h
      · linarith [h.2]
      · linarith [h.2]
    (first | simp only [Real.smoothTransition.zero_of_nonpos (by linarith : s - m ≤ 0), sub_zero] | simp [Real.smoothTransition.zero_of_nonpos (by linarith : s - m ≤ 0)])

theorem hsat_const {m u : ℝ} (hu : m + 1 ≤ u) : hsat m u = hsat m (m + 1) := by
  unfold hsat
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun s : ℝ => 1 - Real.smoothTransition (s - m))
      MeasureTheory.volume a b := fun a b => (hsat_integrand_continuous m).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (m + 1)) (hi (m + 1) u)]
  have h0 : ∫ s in (m + 1)..u, (1 - Real.smoothTransition (s - m)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun s hs => ?_]
    · (first | simp only [intervalIntegral.integral_zero] | simp)
    · rw [Set.uIcc_of_le hu] at hs
      (first | simp only [Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ s - m), sub_self] | simp [Real.smoothTransition.one_of_one_le (by linarith [hs.1] : 1 ≤ s - m)])
  rw [h0, add_zero]

theorem hsat_nonneg (m : ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ hsat m u :=
  intervalIntegral.integral_nonneg hu fun s _ => (hsat_d1_mem m s).1

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
  (first | simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] | simp)

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
  have : openOrthant n = ⋂ i, {x : SDEState n | 0 < x i} := by ext x; (first | simp only [openOrthant, mem_ofPred_eq, mem_iInter] | simp [openOrthant])
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i)

theorem ell_hasDerivAt {c p y w : SDEState n} {s : ℝ} (hS : 0 < Sf c (y + s • w))
    (hy : ∀ i, 0 < (y + s • w) i) :
    HasDerivAt (fun r : ℝ => ellf c p (y + r • w)) (ell1 c p (y + s • w) w) s := by
  have h1 : HasDerivAt (fun r : ℝ => Sf c (y + r • w)) (∑ i, c i * w i) s := by
    simp only [Sf_line]
    simpa only [hasDerivAt_const_add_iff, id_eq, one_mul] using ((hasDerivAt_id s).mul_const (∑ i, c i * w i)).const_add (Sf c y)
  have h2 : ∀ i, HasDerivAt (fun r : ℝ => (y + r • w) i) (w i) s := fun i => by
    simp only [line_apply]
    simpa only [hasDerivAt_const_add_iff, id_eq, one_mul] using ((hasDerivAt_id s).mul_const (w i)).const_add (y i)
  have h3 := (h1.log hS.ne').sub
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => ((h2 i).log (hy i).ne').const_mul (p i))
  exact h3

theorem ell1_hasDerivAt {c p y w : SDEState n} {s : ℝ} (hS : 0 < Sf c (y + s • w))
    (hy : ∀ i, 0 < (y + s • w) i) :
    HasDerivAt (fun r : ℝ => ell1 c p (y + r • w) w) (ell2 c p (y + s • w) w) s := by
  have h1 : HasDerivAt (fun r : ℝ => Sf c (y + r • w)) (∑ i, c i * w i) s := by
    simp only [Sf_line]
    simpa only [hasDerivAt_const_add_iff, id_eq, one_mul] using ((hasDerivAt_id s).mul_const (∑ i, c i * w i)).const_add (Sf c y)
  have h2 : ∀ i, HasDerivAt (fun r : ℝ => (y + r • w) i) (w i) s := fun i => by
    simp only [line_apply]
    simpa only [hasDerivAt_const_add_iff, id_eq, one_mul] using ((hasDerivAt_id s).mul_const (w i)).const_add (y i)
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

theorem Sf_contDiff (c : SDEState n) : ContDiff ℝ 2 (Sf c) :=
  contDiff_const.add (ContDiff.sum fun i _ => contDiff_const.mul (coord_contDiff i))

theorem line_eventually {z w : SDEState n} (hz : z ∈ openOrthant n) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∀ᶠ r in 𝓝 s, z + r • w ∈ openOrthant n := by
  have ho : IsOpen {s : ℝ | z + s • w ∈ openOrthant n} :=
    openOrthant_isOpen.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : (0 : ℝ) ∈ {s : ℝ | z + s • w ∈ openOrthant n} := by simpa only [mem_ofPred_eq, zero_smul, add_zero] using hz
  exact Filter.eventually_of_mem (ho.mem_nhds h0) fun s hs => ho.mem_nhds hs

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
    (first | linarith only [this, neg_abs_le (c i * z i / Sf c z * C.f i z)] | linarith [neg_abs_le (c i * z i / Sf c z * C.f i z)])
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
  (first | linarith only [h1, h2] | linarith)

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
    rw [Finset.sum_eq_single i0 (fun j _ hj => by (first | simp only [hx, ne_eq, hj, not_false_eq_true, PiLp.single_eq_of_ne, abs_zero] | simp [hx, EuclideanSpace.single_apply, hj]))
      (by (first | simp only [Finset.mem_univ, not_true_eq_false, abs_eq_zero, IsEmpty.forall_iff] | simp))]
    rw [show x i0 = |R| + 1 by (first | simp only [hx, PiLp.single_eq_same] | simp [hx]), abs_of_pos (by positivity)]
    (first | linarith only [le_abs_self R] | linarith [le_abs_self R])
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
  have hγ1 : 1 ≤ γb := by (first | linarith only [hδγ, h1] | linarith)
  have p1 : F ≤ γb * F := le_mul_of_one_le_left hF hγ1
  have p2 : T ≤ δ₀ * T := le_mul_of_one_le_left hT h1
  first | linarith only [hA1, hD, hcb, p1, p2, hε, hγ, hT, hT', mul_nonneg hδ0.le hG] | nlinarith

theorem p_le_l1 {p : SDEState n} (hp : p ∈ openOrthant n) (i : Fin n) : p i ≤ l1 p := by
  unfold l1
  have := Finset.single_le_sum (f := fun j => |p j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  simp only at this
  rwa [abs_of_pos (hp i)] at this

theorem sum_p_eq {p : SDEState n} (hp : p ∈ openOrthant n) : ∑ i, p i = l1 p := by
  unfold l1; exact Finset.sum_congr rfl fun i _ => (abs_of_pos (hp i)).symm

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
-- ===== PA =====
section FlatM_PA
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace P41L
open ItoLib EthierKurtz StochKolmogorov.Persist

section Gen
/-! Generic saturation `G = hsat m ∘ φ` of a coercive `C²` function `φ` on the open orthant. -/
variable {n : ℕ}

open scoped Classical in
noncomputable def Gphi (φ : SDEState n → ℝ) (m : ℝ) (y : SDEState n) : ℝ :=
  if y ∈ openOrthant n then hsat m (φ y) else hsat m (m + 1)

variable {φ : SDEState n → ℝ} {m : ℝ} {K : Set (SDEState n)}

theorem Gphi_out (hbig : ∀ z ∈ openOrthant n, z ∉ K → m + 1 ≤ φ z) {z : SDEState n}
    (hz : z ∉ K) : Gphi φ m z = hsat m (m + 1) := by
  by_cases ho : z ∈ openOrthant n
  · rw [Gphi, if_pos ho]; exact hsat_const (hbig z ho hz)
  · rw [Gphi, if_neg ho]

theorem Gphi_nonneg (hm : 0 ≤ m) (hφ0 : ∀ z ∈ openOrthant n, 0 ≤ φ z) (z : SDEState n) :
    0 ≤ Gphi φ m z := by
  unfold Gphi; split_ifs with h
  · exact hsat_nonneg m (hφ0 z h)
  · exact hsat_nonneg m (by linarith)

theorem Gphi_eq_nhds {z : SDEState n} (hz : z ∈ openOrthant n) :
    Gphi φ m =ᶠ[𝓝 z] fun y => hsat m (φ y) :=
  Filter.eventually_of_mem (openOrthant_isOpen.mem_nhds hz) fun y hy => by rw [Gphi, if_pos hy]

theorem Gphi_const_nhds (hK : IsCompact K) (hbig : ∀ z ∈ openOrthant n, z ∉ K → m + 1 ≤ φ z)
    {z : SDEState n} (hz : z ∉ K) : Gphi φ m =ᶠ[𝓝 z] fun _ => hsat m (m + 1) :=
  Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hz) fun _ hy => Gphi_out hbig hy

theorem Gphi_contDiff (hK : IsCompact K) (hKs : K ⊆ openOrthant n)
    (hbig : ∀ z ∈ openOrthant n, z ∉ K → m + 1 ≤ φ z)
    (hφ : ∀ z ∈ openOrthant n, ContDiffAt ℝ 2 φ z) : ContDiff ℝ 2 (Gphi φ m) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ openOrthant n
  · exact ((hsat_contDiff m).contDiffAt.comp z (hφ z hz)).congr_of_eventuallyEq (Gphi_eq_nhds hz)
  · exact contDiffAt_const.congr_of_eventuallyEq (Gphi_const_nhds hK hbig fun h => hz (hKs h))

theorem Gphi_fderiv_out (hK : IsCompact K) (hbig : ∀ z ∈ openOrthant n, z ∉ K → m + 1 ≤ φ z)
    {z : SDEState n} (hz : z ∉ K) :
    fderiv ℝ (Gphi φ m) z = 0 ∧ fderiv ℝ (fderiv ℝ (Gphi φ m)) z = 0 := by
  have h1 : fderiv ℝ (Gphi φ m) =ᶠ[𝓝 z] fun _ => 0 := by
    have hU : ∀ᶠ y in 𝓝 z, y ∉ K := hK.isClosed.isOpen_compl.mem_nhds hz
    refine hU.mono fun y hy => ?_
    rw [(Gphi_const_nhds hK hbig hy).fderiv_eq]
    exact fderiv_const_apply _
  refine ⟨h1.eq_of_nhds, ?_⟩
  rw [h1.fderiv_eq]
  exact fderiv_const_apply _

variable {φ1 φ2 : SDEState n → SDEState n → ℝ}

theorem Gphi_line
    (hφ1 : ∀ z w : SDEState n, ∀ s : ℝ, z + s • w ∈ openOrthant n →
      HasDerivAt (fun r : ℝ => φ (z + r • w)) (φ1 (z + s • w) w) s)
    {z w : SDEState n} {s : ℝ} (hs : ∀ᶠ r in 𝓝 s, z + r • w ∈ openOrthant n) :
    HasDerivAt (fun r : ℝ => Gphi φ m (z + r • w))
      ((1 - Real.smoothTransition (φ (z + s • w) - m)) * φ1 (z + s • w) w) s := by
  have h := (hsat_hasDerivAt m (φ (z + s • w))).comp s (hφ1 z w s hs.self_of_nhds)
  refine HasDerivAt.congr_of_eventuallyEq h (hs.mono fun r hr => ?_)
  show Gphi φ m (z + r • w) = hsat m (φ (z + r • w))
  rw [Gphi, if_pos hr]

theorem Gphi_line2
    (hφ1 : ∀ z w : SDEState n, ∀ s : ℝ, z + s • w ∈ openOrthant n →
      HasDerivAt (fun r : ℝ => φ (z + r • w)) (φ1 (z + s • w) w) s)
    (hφ2 : ∀ z ∈ openOrthant n, ∀ w,
      HasDerivAt (fun s : ℝ => φ1 (z + s • w) w) (φ2 z w) 0)
    {z w : SDEState n} (hz : z ∈ openOrthant n) :
    HasDerivAt (fun s : ℝ => (1 - Real.smoothTransition (φ (z + s • w) - m)) * φ1 (z + s • w) w)
      (-(deriv Real.smoothTransition (φ z - m)) * φ1 z w * φ1 z w +
        (1 - Real.smoothTransition (φ z - m)) * φ2 z w) 0 := by
  have hy : z + (0 : ℝ) • w ∈ openOrthant n := by simpa only [zero_smul, add_zero] using hz
  first
  | have hA := (hsat_d2 m (φ (z + (0 : ℝ) • w))).comp (h := fun r : ℝ => φ (z + r • w)) 0 (hφ1 z w 0 hy)
  | have hA := (hsat_d2 m (φ (z + (0 : ℝ) • w))).comp 0 (hφ1 z w 0 hy)
  have h := hA.fun_mul (hφ2 z hz w)
  simp only [Function.comp_apply, zero_smul, add_zero] at h
  refine h.congr_deriv ?_
  ring

theorem Gphi_fderiv_eq (hGc : ContDiff ℝ 2 (Gphi φ m))
    (hφ1 : ∀ z w : SDEState n, ∀ s : ℝ, z + s • w ∈ openOrthant n →
      HasDerivAt (fun r : ℝ => φ (z + r • w)) (φ1 (z + s • w) w) s)
    {z : SDEState n} (hz : z ∈ openOrthant n) (w : SDEState n) :
    fderiv ℝ (Gphi φ m) z w = (1 - Real.smoothTransition (φ z - m)) * φ1 z w := by
  have h := Gphi_line (m := m) hφ1 (w := w) ((line_eventually hz).self_of_nhds)
  simp only [zero_smul, add_zero] at h
  exact fderiv_eq_of_line (hGc.differentiable two_ne_zero) z w h

theorem Gphi_fderiv2_eq (hGc : ContDiff ℝ 2 (Gphi φ m))
    (hφ1 : ∀ z w : SDEState n, ∀ s : ℝ, z + s • w ∈ openOrthant n →
      HasDerivAt (fun r : ℝ => φ (z + r • w)) (φ1 (z + s • w) w) s)
    (hφ2 : ∀ z ∈ openOrthant n, ∀ w,
      HasDerivAt (fun s : ℝ => φ1 (z + s • w) w) (φ2 z w) 0)
    {z : SDEState n} (hz : z ∈ openOrthant n) (w : SDEState n) :
    fderiv ℝ (fderiv ℝ (Gphi φ m)) z w w =
      -(deriv Real.smoothTransition (φ z - m)) * φ1 z w * φ1 z w +
        (1 - Real.smoothTransition (φ z - m)) * φ2 z w :=
  fderiv2_eq_of_line_loc hGc z w ((line_eventually hz).mono fun _ hs => Gphi_line hφ1 hs)
    (Gphi_line2 hφ1 hφ2 hz)

/-- Drift of `e^{-a} G(y)` inside the orthant: `≤ e^{-a}(h'(φ) Lφ - κ G)`. -/
theorem driftGen_Gphi_le (hK : IsCompact K) (hKs : K ⊆ openOrthant n)
    (hbig : ∀ z ∈ openOrthant n, z ∉ K → m + 1 ≤ φ z)
    (hφ : ∀ z ∈ openOrthant n, ContDiffAt ℝ 2 φ z)
    (hφ1 : ∀ z w : SDEState n, ∀ s : ℝ, z + s • w ∈ openOrthant n →
      HasDerivAt (fun r : ℝ => φ (z + r • w)) (φ1 (z + s • w) w) s)
    (hφ2 : ∀ z ∈ openOrthant n, ∀ w,
      HasDerivAt (fun s : ℝ => φ1 (z + s • w) w) (φ2 z w) 0)
    (κ : ℝ) (σx : SDEDiffusion n) (bx x : SDEState n) (σ : SDEDiffusion n) (b z : SDEState n)
    (a : ℝ) (hz : z ∈ openOrthant n) :
    driftGen (FG (Gphi φ m)) κ σx bx σ b x z a ≤ Real.exp (-a) *
      ((1 - Real.smoothTransition (φ z - m)) * (φ1 z b + (1 / 2) * ∑ j, φ2 z (scol σ j)) -
        κ * hsat m (φ z)) := by
  have hGc := Gphi_contDiff hK hKs hbig hφ
  rw [FG_driftGen hGc]
  simp only [Gphi_fderiv_eq hGc hφ1 hz, Gphi_fderiv2_eq hGc hφ1 hφ2 hz]
  rw [Gphi, if_pos hz]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hD : 0 ≤ deriv Real.smoothTransition (φ z - m) := by (first | linarith only [hsat_d2_nonpos m (φ z)] | linarith [hsat_d2_nonpos m (φ z)])
  set h' := 1 - Real.smoothTransition (φ z - m)
  have hs : ∑ j, (-(deriv Real.smoothTransition (φ z - m)) * φ1 z (scol σ j) * φ1 z (scol σ j) +
      h' * φ2 z (scol σ j)) ≤ h' * ∑ j, φ2 z (scol σ j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := mul_nonneg hD (mul_self_nonneg (φ1 z (scol σ j)))
    have e : -(deriv Real.smoothTransition (φ z - m)) * φ1 z (scol σ j) * φ1 z (scol σ j) =
        -(deriv Real.smoothTransition (φ z - m) * (φ1 z (scol σ j) * φ1 z (scol σ j))) := by ring
    rw [e]; (first | linarith only [this] | linarith)
  have e2 : h' * (φ1 z b + (1 / 2) * ∑ j, φ2 z (scol σ j)) =
      h' * φ1 z b + (1 / 2) * (h' * ∑ j, φ2 z (scol σ j)) := by ring
  rw [e2]
  (first | linarith only [hs] | linarith)

theorem driftGen_Gphi_out (hK : IsCompact K) (hKs : K ⊆ openOrthant n)
    (hbig : ∀ z ∈ openOrthant n, z ∉ K → m + 1 ≤ φ z)
    (hφ : ∀ z ∈ openOrthant n, ContDiffAt ℝ 2 φ z)
    (κ : ℝ) (σx : SDEDiffusion n) (bx x : SDEState n) (σ : SDEDiffusion n) (b z : SDEState n)
    (a : ℝ) (hz : z ∉ openOrthant n) :
    driftGen (FG (Gphi φ m)) κ σx bx σ b x z a = Real.exp (-a) * (-(κ * hsat m (m + 1))) := by
  have hGc := Gphi_contDiff hK hKs hbig hφ
  have hzK : z ∉ K := fun h => hz (hKs h)
  obtain ⟨h0, h2⟩ := Gphi_fderiv_out hK hbig hzK
  rw [FG_driftGen hGc, h0, h2, Gphi_out hbig hzK]
  simp only [ContinuousLinearMap.zero_apply, Finset.sum_const_zero, mul_zero, zero_add, zero_sub]

theorem Gphi_integrand_bound (hK : IsCompact K) (hKs : K ⊆ openOrthant n)
    (hbig : ∀ z ∈ openOrthant n, z ∉ K → m + 1 ≤ φ z)
    (hφ : ∀ z ∈ openOrthant n, ContDiffAt ℝ 2 φ z)
    {σ : SDEState n → SDEDiffusion n} (hσ : Continuous σ) (j : Fin n) :
    ∃ B, ∀ y, ‖fderiv ℝ (Gphi φ m) y‖ * ‖scol (σ y) j‖ ≤ B := by
  have hGc := Gphi_contDiff hK hKs hbig hφ
  have hg : Continuous fun y => ‖fderiv ℝ (Gphi φ m) y‖ * ‖scol (σ y) j‖ :=
    (hGc.continuous_fderiv (by norm_num)).norm.mul (scol_continuous hσ j).norm
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max B 0, fun y => ?_⟩
  by_cases hy : y ∈ K
  · have := hB y hy
    rw [Real.norm_eq_abs] at this
    exact ((le_abs_self _).trans this).trans (le_max_left _ _)
  · rw [(Gphi_fderiv_out hK hbig hy).1]
    (first | simp only [norm_zero, zero_mul, le_sup_right] | simp)

end Gen

section C1
/-! (4.11): `E V̂^δ₀(X_t) ≤ e^{δ₀Ht} V̂^δ₀(x)` via `φ_ε = U_δ₀(-p) + ε U_δ₀(p)`. -/
variable {n : ℕ}

end C1

end P41L

end FlatM_PA
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
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  have hX' : SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => x₀) Y := hY
  have hXm : ∀ s, Measurable (Y s) := hX'.1
  have hXc : ∀ ω, Continuous fun s => Y s ω := hX'.2.1
  -- the per-radius, per-level null events
  have hnull : ∀ R m : ℕ, P {ω | (∀ s ≤ t, ‖Y s ω‖ ≤ (R : ℝ)) ∧
      1 / ((m : ℝ) + 1) < ∑ k, phi3 (Y t ω k)} = 0 := by
    intro R m
    set r : ℝ := ((R : ℝ) + 1) ^ 2 + 1 with hr
    have hr2 : 2 ≤ r := by
      have : (0 : ℝ) ≤ R := R.cast_nonneg
      first | linarith only [hr, this, sq_nonneg (R : ℝ)] | nlinarith
    obtain ⟨c, hc0, hk⟩ := kolm_phi3_coef C hC hr2
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
        rw [mem_closedBall_zero_iff]
        first | linarith only [hx, hr2, sq_nonneg (‖x‖ - 1)] | nlinarith [norm_nonneg x]
      exact ⟨(hCσ x hxb).trans ((le_max_left _ _).trans (le_max_left _ _)),
        (hCb x hxb).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
    obtain ⟨Bc, hBc0, hBd⟩ := Hf_drift_bound (d := n) r S hS
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hH0 : Hf r (pack x₀ x₀ 0) = 0 := by
      simp only [Hf, Phif_pack, (phi3_eq_zero_iff _).2 (hx₀ _), Finset.sum_const_zero,
        mul_zero]
    set K0 : ℝ := Bc / (Real.exp (-(c * t.val)) * (1 / ((m : ℝ) + 1))) with hK0
    have hbound : ∀ N : ℕ, P {ω | (∀ s ≤ t, ‖Y s ω‖ ≤ (R : ℝ)) ∧
        1 / ((m : ℝ) + 1) < ∑ k, phi3 (Y t ω k)} ≤
          ENNReal.ofReal (K0 * (1 / ((N : ℝ) + 1))) := by
      intro N
      have hM : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hI := lintegral_Hf_le hB x₀ hσc hbc hX' (R := (R : ℝ)) (M := (N : ℝ) + 1)
        R.cast_nonneg hc0 hM hr (fun x hx k => hk x hx k) hS0 hBc0
        (fun κ hκ σx bx σy by' x y a h => hBd κ hκ σx bx σy by' x y a h) t
      have h := prob_neg_le hXm hXc hr R.cast_nonneg hε t hI
      refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
      rw [hH0, zero_add, hK0]
      ring
    have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (K0 * (1 / ((N : ℝ) + 1)))) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K0)
      rw [mul_zero] at this
      simpa only [one_div, ENNReal.ofReal_zero] using (ENNReal.tendsto_ofReal this)
    exact le_antisymm (ge_of_tendsto' hlim hbound) zero_le
  -- every bad path lies in one of the null events
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null fun R => measure_iUnion_null fun m => hnull R m)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω
  have hneg : ∃ k, Y t ω k < 0 := by
    by_contra h
    push Not at h
    exact hω h
  obtain ⟨k, hk⟩ := hneg
  have hpos : 0 < phi3 (Y t ω k) :=
    lt_of_le_of_ne (phi3_nonneg _) (fun h => (not_le.2 hk) ((phi3_eq_zero_iff _).1 h.symm))
  have hsum : 0 < ∑ k, phi3 (Y t ω k) :=
    lt_of_lt_of_le hpos (Finset.single_le_sum (fun k _ => phi3_nonneg _) (Finset.mem_univ k))
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hsum
  obtain ⟨Cp, hCp⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := t)).exists_bound_of_continuousOn
    (hXc ω).continuousOn
  obtain ⟨R, hR⟩ := exists_nat_ge Cp
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨R, m, fun s hs => (hCp s ⟨zero_le, hs⟩).trans hR, hm⟩


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
    have : (eac (d := d)) (ixc k) = 0 := by (first | simp only [eac, pack_ixc, PiLp.zero_apply] | simp [eac])
    (first | simp only [PiLp.add_apply, PiLp.smul_apply, this, smul_eq_mul, mul_zero, add_zero] | simp [this])
  have ha : (w + c • (eac (d := d))) iac = w iac + c := by
    have : (eac (d := d)) iac = 1 := by (first | simp only [eac, pack_iac] | simp [eac])
    (first | simp only [PiLp.add_apply, PiLp.smul_apply, this, smul_eq_mul, mul_one] | simp [this])
  simp only [HfL, Nxf, PhifL, hx, ha]
  rw [show -(w iac + c) = -c + -w iac by ring, Real.exp_add]
  ring

/-- `(HfL ψ cv)` does not see the `y` block. -/
theorem HfL_translate_y (r : ℝ) (c : SDEState d) (w : SDEState (d + d + 1)) :
    (HfL ψ cv) r (w + pack 0 c 0) = 1 * (HfL ψ cv) r w := by
  have hx : ∀ k, (w + pack 0 c 0) (ixc k) = w (ixc k) := fun k => by (first | simp only [PiLp.add_apply, pack_ixc, PiLp.zero_apply, add_zero] | simp)
  have ha : (w + pack 0 c 0) iac = w iac := by (first | simp only [PiLp.add_apply, pack_iac, add_zero] | simp)
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
  first
  | have k1 : fderiv ℝ ((HfL ψ cv) r) (pack x y 0) = fderiv ℝ ((HfL ψ cv) r) (pack x 0 0) :=
      ((congrArg (fderiv ℝ ((HfL ψ cv) r)) e2).symm.trans h'.1).trans (one_smul ℝ _)
    have k2 : fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x y 0) = fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x 0 0) :=
      ((congrArg (fderiv ℝ (fderiv ℝ ((HfL ψ cv) r))) e2).symm.trans h'.2).trans (one_smul ℝ _)
    exact ⟨((congrArg (fderiv ℝ ((HfL ψ cv) r)) e1).symm.trans h.1).trans (congrArg _ k1),
      ((congrArg (fderiv ℝ (fderiv ℝ ((HfL ψ cv) r))) e1).symm.trans h.2).trans (congrArg _ k2)⟩
  | rw [e1] at h; rw [e2, one_smul, one_smul] at h'
    rw [h.1, h.2, h'.1, h'.2]
    exact ⟨rfl, rfl⟩

theorem HfL_fderiv_eac (r : ℝ) (u : SDEState (d + d + 1)) :
    fderiv ℝ ((HfL ψ cv) r) u (eac (d := d)) = -(HfL ψ cv) r u := by
  refine fderiv_eq_of_line ((HfL_contDiff (ψ := ψ) (cv := cv) r).differentiable (by norm_num)) u _ ?_
  have e : (fun s : ℝ => (HfL ψ cv) r (u + s • (eac (d := d)))) = fun s => Real.exp (-s) * (HfL ψ cv) r u :=
    funext fun s => HfL_translate (ψ := ψ) (cv := cv) r s u
  rw [e]
  have := ((hasDerivAt_id (0 : ℝ)).neg.exp).mul_const ((HfL ψ cv) r u)
  simpa only [Pi.neg_apply, id_eq, neg_zero, Real.exp_zero, mul_neg, mul_one, neg_mul, one_mul] using this


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
    (first | simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, neg_add_rev] | simp)
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
      (first | simp only [PiLp.add_apply, PiLp.smul_apply, hv, smul_eq_mul, mul_zero, add_zero] | simp [hv])
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
    first | ring1 | ring_nf

theorem PhifL_pack (x y : SDEState d) (a : ℝ) :
    (PhifL ψ cv) (pack x y a) = ψ (∑ k, cv k * x k) := by
  (first | simp only [PhifL, pack_ixc] | simp [PhifL])

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
    Finset.sum_congr rfl (fun j _ => H0fL_fderiv2 (ψ := ψ) (cv := cv) _ _ (by (first | simp only [pack_iac] | simp)))]
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
    exact ⟨by first | exact norm_zero.trans_le (le_max_right _ _) | (rw [norm_zero]; exact le_max_right _ _),
      fun i i' => by simpa only [zero_apply, abs_zero] using hB20⟩
  · have hxρ : ‖x‖ ≤ ρ := by
      by_contra hc
      replace hc := not_le.1 hc
      have hr0 := abs_nonneg r
      have hr1 := le_abs_self r
      have hxn := norm_nonneg x
      have hc' : |r| + 2 < ‖x‖ := hc
      first | linarith only [mul_lt_mul'' hc' hc' (add_nonneg (abs_nonneg r) zero_le_two) (add_nonneg (abs_nonneg r) zero_le_two), not_lt.1 hN, hr0, hr1, mul_nonneg hr0 hr0] | nlinarith
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
    add_nonneg (mul_nonneg hB1 hD0) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hB2 (pow_nonneg hD0 2))))
  refine ⟨B1 * D + (1 / 2) * (d * (B2 * D ^ 2)), hBB, fun κ hκ σx bx σy by' x y a hS' => ?_⟩
  have hea := Real.exp_pos (-a)
  by_cases hN : r + 1 < ‖x‖ ^ 2
  · obtain ⟨h1, h2⟩ := HfL_fderiv_zero (ψ := ψ) (cv := cv) (r := r) (u := pack x y a) (by rw [Nxf_pack]; exact hN)
    unfold driftGen
    rw [h1, h2]
    simp only [ContinuousLinearMap.zero_apply, Finset.sum_const_zero, mul_zero, add_zero]
    first | exact mul_nonneg hea.le hBB | positivity
  · obtain ⟨hσx, hbx, hσy, hby⟩ := hS' (not_lt.1 hN)
    obtain ⟨hL1, hL2⟩ := hB x
    obtain ⟨e1, e2⟩ := HfL_fderiv_pack (ψ := ψ) (cv := cv) r x y a
    unfold driftGen
    have hsplit : pack bx by' κ = pack bx by' 0 + κ • (eac (d := d)) := by
      rw [pack_add_eac, zero_add]
    have hk : fderiv ℝ ((HfL ψ cv) r) (pack x y a) (κ • (eac (d := d))) ≤ 0 := by
      rw [map_smul, HfL_fderiv_eac (ψ := ψ) (cv := cv), smul_eq_mul]
      have := HfL_nonneg (ψ := ψ) (cv := cv) r (pack x y a)
      first | linarith only [mul_nonneg hκ this] | nlinarith
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
              first
              | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
              | simp [mul_add]
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
        _ ≤ B2 * D ^ 2 := by
          first | exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hcs0 hcs 2) hB2 | gcongr
    have t3 : ∑ j, fderiv ℝ (fderiv ℝ ((HfL ψ cv) r)) (pack x y a) (pack (scol σx j) (scol σy j) 0)
        (pack (scol σx j) (scol σy j) 0) ≤ d * (Real.exp (-a) * (B2 * D ^ 2)) := by
      calc _ ≤ ∑ _j : Fin d, Real.exp (-a) * (B2 * D ^ 2) := Finset.sum_le_sum fun j _ => t2 j
        _ = _ := by
          first | simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] | simp
    first | linarith only [t1, hk, t3] | nlinarith



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
  (first | simp only [cutR, distB_eq_zero h, sub_zero, zero_le_one, sup_of_le_right] | simp [cutR, distB_eq_zero h])

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
    (first | linarith only [h1, h2, h3, hBk] | linarith)
  · have hx1 : R + 1 < ‖x‖ := by
      have h1 : (R + 1) ^ 2 < ‖x‖ ^ 2 := by rw [hr] at hin'; (first | linarith only [not_lt.1 hin'] | linarith [not_lt.1 hin'])
      exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg x) h1
    have hdist : 1 ≤ distB R x := by unfold distB; exact le_max_of_le_right (by (first | linarith only [hx1] | linarith))
    have hcut : cutR R x = 0 := by unfold cutR; exact max_eq_left (by (first | linarith only [hx1] | linarith))
    have hkM : M ≤ kapX 0 M R x := by
      unfold kapX; have := mul_le_mul_of_nonneg_left hdist hM.le; (first | linarith only [this] | linarith)
    refine (hBd _ hk0).trans ?_
    have : B ≤ B * (1 / M) * kapX 0 M R x := by
      have h1 : 1 ≤ kapX 0 M R x / M := (one_le_div hM).2 hkM
      rw [show B * (1 / M) * kapX 0 M R x = B * (kapX 0 M R x / M) by ring]
      first | exact le_mul_of_one_le_right hB h1 | nlinarith
    rw [hcut, mul_zero, mul_zero, sub_zero]
    exact mul_le_mul_of_nonneg_left (by (first | linarith only [this, hK] | linarith)) hea.le

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
            first | linarith only [this] | linarith
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
                    first | exact mul_le_of_le_one_left hK this | nlinarith
            _ = K * t := by rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
        have e2 := integral_exp_neg_primitive hgc t
        have e3 := Real.exp_pos (-(∫ v in (0 : ℝ)..t, kapX 0 M R (x v)))
        have e4 : 0 ≤ B * (1 / M) := mul_nonneg hB (one_div_nonneg.2 hM.le)
        rw [e2]
        first | linarith only [e1, mul_nonneg e4 e3.le] | nlinarith

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
  · exact h.trans (le_of_eq (by (first | simp only [NNReal.val_eq_coe, one_div, integral_zero, add_zero] | simp)))
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
    first | linarith only [hpath, hFn] | linarith

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
    first | linarith only [mul_lt_mul'' h1 h1 (by linarith) (by linarith), hx, hr, mul_nonneg hr hr] | nlinarith [norm_nonneg x]
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
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      simp only [hMf]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hn1]
      first | linarith only [hn1, hb0] | nlinarith
    first | linarith only [h1, h2] | linarith
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
        simpa only [NNReal.val_eq_coe, one_div, add_zero] using this

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
  · first | linarith only [mul_nonneg hs h0] | nlinarith
  · push Not at hs
    by_cases hs2 : s < -1 / 2
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; norm_num
    · push Not at hs2
      first | linarith only [mul_nonneg_of_nonpos_of_nonpos hs.le (sub_nonpos.2 h1), hs2] | nlinarith

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
  have h := (((hasDerivAt_id s).const_add 1).log (by (first | simp only [id_eq, ne_eq] | simp); linarith)).add_const (Real.log 2)
  exact h.deriv.trans (by (first | simp only [id_eq, one_div] | simp))

theorem deriv2_psiK {s : ℝ} (hs : -1 / 4 < s) : deriv (deriv psiK) s = -((1 + s) ^ 2)⁻¹ := by
  have hev : deriv psiK =ᶠ[𝓝 s] fun s => (1 + s)⁻¹ := by
    filter_upwards [Ioi_mem_nhds hs] with s' hs' using deriv_psiK hs'
  rw [hev.deriv_eq]
  have h := ((hasDerivAt_id s).const_add 1).inv (by (first | simp only [id_eq, ne_eq] | simp); linarith)
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

/-- The weight `w = γb + δ₀ Σᵢ (|fᵢ| + gᵢ²)`, read at `x⁺`. -/
noncomputable def wK (C : Coeffs n) (γb δ₀ : ℝ) (x : SDEState n) : ℝ :=
  γb + δ₀ * ∑ i, (|C.f i (posPart x)| + C.g i (posPart x) ^ 2)

theorem wK_continuous (C : Coeffs n) (γb δ₀ : ℝ)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (wK C γb δ₀) := by
  have hf : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hg : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  exact continuous_const.add (continuous_const.mul
    (continuous_finset_sum _ fun i _ => (hf i).abs.add ((hg i).pow 2)))

theorem wK_nonneg (C : Coeffs n) {γb δ₀ : ℝ} (hγ : 0 ≤ γb) (hδ : 0 ≤ δ₀) (x : SDEState n) :
    0 ≤ wK C γb δ₀ x :=
  add_nonneg hγ (mul_nonneg hδ (Finset.sum_nonneg fun i _ => add_nonneg (abs_nonneg _) (sq_nonneg _)))

theorem cBracket_add_wK_le (C : Coeffs n) (c : SDEState n) (γb δ₀ : ℝ)
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) {x : SDEState n} (hx : x ∈ orthant n) :
    cBracket C c x + wK C γb δ₀ x ≤ max (Hconst C c γb δ₀) 0 := by
  have hb := le_csSup (bracket35_bddAbove C c γb δ₀ hA hδ) (Set.mem_image_of_mem _ hx)
  refine le_trans ?_ (hb.trans (le_max_left _ _))
  unfold wK bracket35
  rw [posPart_of_mem hx]
  have hδ0 := hδ.1
  have h1 : ∑ i, (|C.f i x| + C.g i x ^ 2) ≤ ∑ i, (2 * |C.f i x| + C.g i x ^ 2) :=
    Finset.sum_le_sum fun i _ => by have := abs_nonneg (C.f i x); linarith
  have h2 : 0 ≤ ∑ i, ∑ j, |C.g i x * C.g j x * C.sig i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  first | linarith only [mul_le_mul_of_nonneg_left h1 hδ0.le, mul_nonneg hδ0.le h2] | nlinarith

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

/-- `E ∫₀ᵗ w(X_u) du ≤ ψ(cᵀx₀) + K t` for the Kolmogorov system (1.1). -/
theorem lintegral_wK_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (C : Coeffs n)
    (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hfam : IsSolutionFamily P C B X) (c : SDEState n) (γb δ₀ : ℝ) (hA : Assumption11 C c γb)
    (hδ : IsDelta0 C γb δ₀) {x₀ : SDEState n} (hx₀ : x₀ ∈ orthant n) (t : ℝ≥0) :
    ∫⁻ ω, ENNReal.ofReal (∫ u in (0 : ℝ)..t.val, wK C γb δ₀ (X x₀ u.toNNReal ω)) ∂P ≤
      ENNReal.ofReal (psiK (∑ k, c k * x₀ k) + max (Hconst C c γb δ₀) 0 * t.val) := by
  obtain ⟨hP, hBm, hX⟩ := hfam
  have := hP
  have : Fact (ContDiff ℝ 2 psiK) := ⟨psiK_contDiff⟩
  have : Fact (∀ v, 0 ≤ psiK v) := ⟨psiK_nonneg⟩
  have hC := hA.2.1
  have hc := hA.2.2.1
  have hγ := hA.2.2.2.1
  obtain ⟨hσc, hbc, -⟩ := kolm_trunc C hC
  have hX' : SolvesBrownianSDE P (fun p => (fun x => diffusion C (0, x)) p.2)
      (fun p => (fun x => drift C (0, x)) p.2) B (fun _ => x₀) (X x₀) := hX x₀ hx₀
  have hall := orthant_inv_all P C B hBm hC hx₀ (hX x₀ hx₀)
  refine lintegral_w_le (ψ := psiK) (cv := c) hBm x₀ hσc hbc hX' (wK_continuous C γb δ₀ hC)
    (wK_nonneg C hγ.le hδ.1.le) (le_max_right _ _) ?_ t
  filter_upwards [hall] with ω hω u
  rw [genL_kolm C hc (hω u)]
  have := cBracket_add_wK_le C c γb δ₀ hA hδ (hω u)
  linarith

end M12b

end ItoLib

end FlatM_Y
-- ===== PB =====
section FlatM_PB
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
set_option autoImplicit false

namespace P41L
open ItoLib EthierKurtz StochKolmogorov.Persist

section C2a
/-! C2 ingredients: `ℓ = ln V + A`, its generator `Φ`, the cut-off drift bound `gm`. -/
variable {n : ℕ}

noncomputable def lphi (c p y : SDEState n) : ℝ := ellf c p y + Acst c p

theorem Acst_nonneg (c p : SDEState n) : 0 ≤ Acst c p := by
  unfold Acst; exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => abs_nonneg _)

theorem lphi_nonneg {c p : SDEState n} (hc : c ∈ openOrthant n) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i ≤ 1) : ∀ z ∈ openOrthant n, 0 ≤ lphi c p z := by
  intro z hz
  have h1 := ellf_ge_S hc hz hp
  have h2 : 0 ≤ Real.log (Sf c z) := Real.log_nonneg (one_le_Sf hc (openOrthant_sub hz))
  have h3 : 0 ≤ (1 - ∑ i, p i) * Real.log (Sf c z) := mul_nonneg (by linarith) h2
  unfold lphi; linarith

theorem lphi_contDiffAt {c p : SDEState n} (hc : c ∈ openOrthant n) :
    ∀ z ∈ openOrthant n, ContDiffAt ℝ 2 (lphi c p) z := by
  intro z hz
  have hS : ContDiffAt ℝ 2 (fun y => Real.log (Sf c y)) z :=
    (Sf_contDiff c).contDiffAt.log (by linarith [one_le_Sf hc (openOrthant_sub hz)])
  have hl : ContDiffAt ℝ 2 (fun y : SDEState n => ∑ i, p i * Real.log (y i)) z :=
    ContDiffAt.sum fun i _ => contDiffAt_const.mul
      ((coord_contDiff i).contDiffAt.log (hz i).ne')
  exact (hS.sub hl).add contDiffAt_const

theorem lphi_line {c p : SDEState n} (hc : c ∈ openOrthant n) :
    ∀ z w : SDEState n, ∀ s : ℝ, z + s • w ∈ openOrthant n →
      HasDerivAt (fun r : ℝ => lphi c p (z + r • w)) (ell1 c p (z + s • w) w) s := by
  intro z w s hy
  have hS : 0 < Sf c (z + s • w) := by linarith [one_le_Sf hc (openOrthant_sub hy)]
  exact (ell_hasDerivAt (p := p) hS hy).add_const (Acst c p)

theorem lphi_line2 {c p : SDEState n} (hc : c ∈ openOrthant n) :
    ∀ z ∈ openOrthant n, ∀ w,
      HasDerivAt (fun s : ℝ => ell1 c p (z + s • w) w) (ell2 c p z w) 0 := by
  intro z hz w
  have hy : z + (0 : ℝ) • w ∈ openOrthant n := by simpa only [zero_smul, add_zero] using hz
  have hS : 0 < Sf c (z + (0 : ℝ) • w) := by linarith [one_le_Sf hc (openOrthant_sub hy)]
  have h := ell1_hasDerivAt (p := p) (w := w) hS hy
  simp only [zero_smul, add_zero] at h
  exact h

theorem lphi_big {c p : SDEState n} {m : ℝ} (hm : 0 ≤ m) (hc : c ∈ openOrthant n)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1) :
    ∀ z ∈ openOrthant n, z ∉ boxK 1 (Real.exp (m + 1) - 1) c p → m + 1 ≤ lphi c p z := by
  intro z hz hout
  have hm' : 0 ≤ Real.exp (m + 1) - 1 := by
    have := Real.add_one_le_exp (m + 1); linarith
  have h1 := U_big_of_out one_pos hm' hc hp hp1 hz hout
  have h2 : Real.exp (m + 1) ≤ Real.exp (1 * ellf c p z) := by unfold Uf at h1; linarith
  have h3 := Real.exp_le_exp.1 h2
  have := Acst_nonneg c p
  unfold lphi; linarith

theorem log_Vfun {c p y : SDEState n} (hc : c ∈ openOrthant n) (hy : y ∈ openOrthant n) :
    Real.log (Vfun c p y) = ellf c p y := by
  have hS : 0 < Sf c y := lt_of_lt_of_le one_pos (one_le_Sf hc (openOrthant_sub hy))
  have hP : 0 < ∏ i, y i ^ p i := Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hy i) _
  have hVe : Vfun c p y = Sf c y / ∏ i, y i ^ p i := rfl
  rw [hVe, Real.log_div hS.ne' hP.ne',
    Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hy i) _).ne'), ellf]
  simp only [Real.log_rpow (hy _)]
  try ring

/-- The generator of `ℓ = ln V` is `Φ` (p. 17). -/
theorem gen_ell (C : Coeffs n) {c p z : SDEState n} (hc : c ∈ openOrthant n)
    (hz : z ∈ openOrthant n) :
    ell1 c p z (drift C (0, z)) + (1 / 2) * ∑ j, ell2 c p z (scol (diffusion C (0, z)) j) =
      Phi C c p z := by
  have hzo := openOrthant_sub hz
  have hpp : posPart z = z := posPart_self hzo
  have hS : Sf c z ≠ 0 := by linarith [one_le_Sf hc hzo]
  have hb : ∀ i, (drift C (0, z)) i = z i * C.f i z := fun i => by
    simp only [StochKolmogorov.Persist.drift, PiLp.toLp_apply, hpp]
  have hs : ∀ j i, (scol (diffusion C (0, z)) j) i = z i * C.g i z * C.Γ j i := fun j i => by
    simp only [scol, StochKolmogorov.Persist.diffusion, PiLp.toLp_apply, hpp]
  unfold Phi
  rw [cBracket_form C hc hzo]
  set a : Fin n → ℝ := fun i => c i * z i / Sf c z with ha
  have Q1 : ell1 c p z (drift C (0, z)) = ∑ i, a i * C.f i z - ∑ i, p i * C.f i z := by
    unfold ell1; simp only [hb]
    congr 1
    · rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by simp only [ha]; ring
    · exact Finset.sum_congr rfl fun i _ => by rw [mul_div_cancel_left₀ _ (hz i).ne']
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
  have hsum : ∑ j, ell2 c p z (scol (diffusion C (0, z)) j) =
      -(∑ i, ∑ i', (a i * C.g i z) * (a i' * C.g i' z) * C.sig i i') +
        ∑ i, (p i * C.g i z ^ 2) * C.sig i i := by
    simp only [Q3]
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, quad_sig, diag_sig]
    rfl
  rw [Q1, hsum]
  have e : ∑ i, p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2) =
      ∑ i, p i * C.f i z - (1 / 2) * ∑ i, (p i * C.g i z ^ 2) * C.sig i i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  have e2 : ∑ i, a i * C.f i z = ∑ i, c i * z i / Sf c z * C.f i z := rfl
  have e3 : ∑ i, ∑ i', (a i * C.g i z) * (a i' * C.g i' z) * C.sig i i' =
      ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) * C.sig i i' := rfl
  rw [e2, e3]
  ring

noncomputable def PhiT (C : Coeffs n) (c p y : SDEState n) : ℝ := Phi C c p (posPart y)

theorem PhiT_continuous (C : Coeffs n) {c : SDEState n} (p : SDEState n) (hc : c ∈ openOrthant n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i)) :
    Continuous (PhiT C c p) := by
  have hf : ∀ i, Continuous fun x => C.f i (posPart x) := fun i =>
    (hC i).1.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hg : ∀ i, Continuous fun x => C.g i (posPart x) := fun i =>
    (hC i).2.continuousOn.comp_continuous continuous_posPart posPart_mem_orthant
  have hx : ∀ i, Continuous fun x : SDEState n => posPart x i := fun i =>
    (PiLp.continuous_apply 2 _ i).comp continuous_posPart
  have hS : Continuous fun x : SDEState n => 1 + ∑ i, c i * posPart x i :=
    continuous_const.add (continuous_finsetSum _ fun i _ => continuous_const.mul (hx i))
  have hS0 : ∀ x : SDEState n, 1 + ∑ i, c i * posPart x i ≠ 0 := fun x => by
    have := one_le_Sf hc (posPart_mem_orthant x); unfold Sf at this; linarith
  have h1 : Continuous fun x : SDEState n => (∑ i, c i * posPart x i * C.f i (posPart x)) /
      (1 + ∑ i, c i * posPart x i) :=
    (continuous_finsetSum _ fun i _ => (continuous_const.mul (hx i)).mul (hf i)).div hS hS0
  have h2 : Continuous fun x : SDEState n => (1 / 2) * (∑ i, ∑ j, C.sig i j * c i * c j *
      posPart x i * posPart x j * C.g i (posPart x) * C.g j (posPart x)) /
        (1 + ∑ i, c i * posPart x i) ^ 2 :=
    (continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (((((continuous_const.mul continuous_const).mul continuous_const).mul (hx i)).mul
        (hx j)).mul (hg i)).mul (hg j))).div (hS.pow 2) fun x => pow_ne_zero 2 (hS0 x)
  have h3 : Continuous fun x : SDEState n => ∑ i, p i * (C.f i (posPart x) -
      C.sig i i * C.g i (posPart x) ^ 2 / 2) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul ((hf i).sub
      ((continuous_const.mul ((hg i).pow 2)).div_const 2))
  exact (h1.sub h2).sub h3

/-- `|Φ| ≤ K wK`. -/
theorem PhiT_abs_le (hn : 0 < n) {C : Coeffs n} {c p : SDEState n} {γb δ₀ : ℝ}
    (hA : Assumption11 C c γb) (hδ : IsDelta0 C γb δ₀) (hp : p ∈ openOrthant n)
    (hpl : l1 p ≤ δ₀) (y : SDEState n) :
    |PhiT C c p y| ≤ (2 / δ₀ + γb / (3 * δ₀ ^ 2)) * wK C γb δ₀ y := by
  have hc := hA.2.2.1
  have hγ := hA.2.2.2.1
  have hδ0 := hδ.1
  have hδ1 := delta0_lt_one hn hA hδ
  have hzo : posPart y ∈ orthant n := posPart_mem_orthant y
  have hpd : ∀ i, p i ≤ δ₀ := fun i => (p_le_l1 hp i).trans hpl
  set z := posPart y with hzdef
  set F := ∑ i, |C.f i z| with hF
  set T := ∑ i, ∑ i', |C.g i z * C.g i' z * C.sig i i'| with hT
  set G2 := ∑ i, C.g i z ^ 2 with hG2
  have hF0 : 0 ≤ F := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ => abs_nonneg _
  have hG0 : 0 ≤ G2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcb_up : cBracket C c z ≤ F := by
    rw [cBracket_form C hc hzo]
    have h1 : ∑ i, c i * z i / Sf c z * C.f i z ≤ F := Finset.sum_le_sum fun i _ => by
      obtain ⟨h0, h1⟩ := a_mem hc hzo i
      have : |c i * z i / Sf c z * C.f i z| ≤ |C.f i z| := by
        rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg _) h1
      exact (le_abs_self _).trans this
    have h2 : 0 ≤ ∑ i, ∑ i', (c i * z i / Sf c z * C.g i z) * (c i' * z i' / Sf c z * C.g i' z) *
        C.sig i i' := by
      have h0 := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
        sq_nonneg (∑ i, (c i * z i / Sf c z * C.g i z) * C.Γ j i))
      rw [quad_sig] at h0
      exact h0
    first | linarith only [h1, h2] | linarith
  have hcb_lo := cBracket_ge C hc hzo
  have hdiag : ∑ i, |C.g i z * C.g i z * C.sig i i| ≤ T :=
    Finset.sum_le_sum fun i _ => dsum_le (fun i => C.g i z) C.sig i
  have hd : ∀ i, |p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2)| ≤
      δ₀ * (|C.f i z| + (1 / 2) * |C.g i z * C.g i z * C.sig i i|) := fun i => by
    rw [abs_mul, abs_of_pos (hp i)]
    have : |C.f i z - C.sig i i * C.g i z ^ 2 / 2| ≤
        |C.f i z| + (1 / 2) * |C.g i z * C.g i z * C.sig i i| := by
      have e : C.sig i i * C.g i z ^ 2 / 2 = (1 / 2) * (C.g i z * C.g i z * C.sig i i) := by ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul (hpd i) this (abs_nonneg _) hδ0.le
  have hPs : |∑ i, p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2)| ≤ δ₀ * (F + (1 / 2) * T) := by
    calc _ ≤ ∑ i, |p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, δ₀ * (|C.f i z| + (1 / 2) * |C.g i z * C.g i z * C.sig i i|) :=
          Finset.sum_le_sum fun i _ => hd i
      _ = δ₀ * (F + (1 / 2) * ∑ i, |C.g i z * C.g i z * C.sig i i|) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ δ₀ * (F + (1 / 2) * T) :=
          mul_le_mul_of_nonneg_left (by first | linarith only [hdiag] | linarith) hδ0.le
  have hDel := hδ.2.2 z hzo
  have hTb : 3 * δ₀ * T ≤ γb * G2 := by
    have : 0 ≤ δ₀ * G2 := mul_nonneg hδ0.le hG0
    first | linarith only [hDel, this, hT, hG2] | linarith
  have hw : wK C γb δ₀ y = γb + δ₀ * (F + G2) := by
    unfold wK; rw [Finset.sum_add_distrib]
  have hk : (2 / δ₀ + γb / (3 * δ₀ ^ 2)) * δ₀ = 2 + γb / (3 * δ₀) := by
    field_simp
  set Kc := 2 / δ₀ + γb / (3 * δ₀ ^ 2) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have hKw : (2 + γb / (3 * δ₀)) * (F + G2) ≤ Kc * wK C γb δ₀ y := by
    rw [hw]
    have : Kc * (γb + δ₀ * (F + G2)) = Kc * γb + (Kc * δ₀) * (F + G2) := by ring
    rw [this, hk]
    have := mul_nonneg hKc0 hγ.le
    first | linarith only [this] | linarith
  have hq : γb / (3 * δ₀) * (3 * δ₀ * T) = γb * T := by field_simp
  have hTb2 : T ≤ γb / (3 * δ₀) * G2 := by
    have h1 := mul_le_mul_of_nonneg_left hTb (by positivity : (0 : ℝ) ≤ γb / (3 * δ₀))
    have h2 : γb / (3 * δ₀) * (γb * G2) = γb * (γb / (3 * δ₀) * G2) := by ring
    rw [hq, h2] at h1
    exact le_of_mul_le_mul_left h1 hγ
  have hX : 0 ≤ γb / (3 * δ₀) * F := by
    first | exact mul_nonneg (div_nonneg hγ.le (mul_nonneg zero_le_three hδ0.le)) hF0 | positivity
  have hY : 0 ≤ 2 * G2 := by first | exact mul_nonneg zero_le_two hG0 | positivity
  have hδF : δ₀ * F ≤ F := mul_le_of_le_one_left hF0 hδ1.le
  have hδT : δ₀ * T ≤ T := mul_le_of_le_one_left hT0 hδ1.le
  have hPhi : PhiT C c p y = cBracket C c z - ∑ i, p i * (C.f i z - C.sig i i * C.g i z ^ 2 / 2) :=
    rfl
  rw [hPhi, abs_le]
  obtain ⟨hs1, hs2⟩ := abs_le.1 hPs
  have hZ : 0 ≤ γb / (3 * δ₀) * G2 := by
    first | exact mul_nonneg (div_nonneg hγ.le (mul_nonneg zero_le_three hδ0.le)) hG0 | positivity
  constructor
  · linarith only [hKw, hX, hY, hZ, hTb2, hs1, hs2, hcb_up, hcb_lo, hδF, hδT, hF0, hT0, hG0]
  · linarith only [hKw, hX, hY, hZ, hTb2, hs1, hs2, hcb_up, hcb_lo, hδF, hδT, hF0, hT0, hG0]

open scoped Classical in
noncomputable def gm (C : Coeffs n) (c p : SDEState n) (m : ℝ) (y : SDEState n) : ℝ :=
  if y ∈ openOrthant n then (1 - Real.smoothTransition (lphi c p y - m)) * PhiT C c p y else 0

theorem gm_continuous (C : Coeffs n) {c p : SDEState n} (hc : c ∈ openOrthant n)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {m : ℝ} (hm : 0 ≤ m) : Continuous (gm C c p m) := by
  have hK := boxK_isCompact 1 (Real.exp (m + 1) - 1) c p
  have hKs := boxK_sub 1 (Real.exp (m + 1) - 1) c p
  have hbig := lphi_big hm hc hp hp1
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ openOrthant n
  · have he : (fun y => (1 - Real.smoothTransition (lphi c p y - m)) * PhiT C c p y) =ᶠ[𝓝 z]
        gm C c p m :=
      Filter.eventually_of_mem (openOrthant_isOpen.mem_nhds hz) fun y hy => by rw [gm, if_pos hy]
    refine ContinuousAt.congr ?_ he
    exact (continuousAt_const.sub (Real.smoothTransition.continuous.continuousAt.comp
      ((lphi_contDiffAt hc z hz).continuousAt.sub continuousAt_const))).mul
      (PhiT_continuous C p hc hC).continuousAt
  · have hzK : z ∉ boxK 1 (Real.exp (m + 1) - 1) c p := fun h => hz (hKs h)
    have he : (fun _ => (0 : ℝ)) =ᶠ[𝓝 z] gm C c p m := by
      refine Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hzK) fun y hy => ?_
      show 0 = gm C c p m y
      by_cases hyo : y ∈ openOrthant n
      · rw [gm, if_pos hyo, Real.smoothTransition.one_of_one_le (by linarith [hbig y hyo hy])]
        ring
      · rw [gm, if_neg hyo]
    exact continuousAt_const.congr he

theorem gm_abs_le (C : Coeffs n) (c p : SDEState n) (m : ℝ) (y : SDEState n) :
    |gm C c p m y| ≤ |PhiT C c p y| := by
  unfold gm; split_ifs
  · rw [abs_mul]
    obtain ⟨h0, h1⟩ := hsat_d1_mem m (lphi c p y)
    rw [abs_of_nonneg h0]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  · (first | simp only [abs_zero, abs_nonneg] | simp)

theorem gm_tendsto (C : Coeffs n) (c p : SDEState n) {y : SDEState n} (hy : y ∈ openOrthant n) :
    Tendsto (fun m : ℕ => gm C c p (m : ℝ) y) atTop (𝓝 (PhiT C c p y)) := by
  apply tendsto_atTop_of_eventually_const (i₀ := ⌈lphi c p y⌉₊)
  intro m hm
  have h1 : lphi c p y ≤ m := (Nat.le_ceil _).trans (Nat.cast_le.2 hm)
  rw [gm, if_pos hy, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

noncomputable def drG (C : Coeffs n) (G : SDEState n → ℝ) (y : SDEState n) : ℝ :=
  fderiv ℝ G y (drift C (0, y)) + (1 / 2) * ∑ j, fderiv ℝ (fderiv ℝ G) y
    (scol (diffusion C (0, y)) j) (scol (diffusion C (0, y)) j)

theorem drG_continuous (C : Coeffs n)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {G : SDEState n → ℝ} (hG : ContDiff ℝ 2 G) : Continuous (drG C G) := by
  obtain ⟨hσ, hb, -⟩ := kolm_trunc C hC
  have h1 : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  have h2 : Continuous (fderiv ℝ (fderiv ℝ G)) :=
    (hG.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  exact (h1.clm_apply hb).add (continuous_const.mul (continuous_finsetSum _ fun j _ =>
    (h2.clm_apply (scol_continuous hσ j)).clm_apply (scol_continuous hσ j)))

theorem driftGen_FG_zero (C : Coeffs n) {G : SDEState n → ℝ} (hG : ContDiff ℝ 2 G)
    (y : SDEState n) (a : ℝ) :
    driftGen (FG G) 0 (diffusion C (0, y)) (drift C (0, y)) (diffusion C (0, y)) (drift C (0, y))
      y y a = Real.exp (-a) * drG C G y := by
  rw [FG_driftGen hG]; unfold drG; ring

theorem drG_le (C : Coeffs n) {c p : SDEState n} (hc : c ∈ openOrthant n)
    (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1) {m : ℝ} (hm : 0 ≤ m) (y : SDEState n) :
    drG C (Gphi (lphi c p) m) y ≤ gm C c p m y := by
  have hK := boxK_isCompact 1 (Real.exp (m + 1) - 1) c p
  have hKs := boxK_sub 1 (Real.exp (m + 1) - 1) c p
  have hbig := lphi_big hm hc hp hp1
  have hGc := Gphi_contDiff hK hKs hbig (lphi_contDiffAt hc)
  have e := driftGen_FG_zero C hGc y 0
  simp only [neg_zero, Real.exp_zero, one_mul] at e
  by_cases hz : y ∈ openOrthant n
  · have h := driftGen_Gphi_le hK hKs hbig (lphi_contDiffAt hc) (lphi_line hc) (lphi_line2 hc) 0
      (diffusion C (0, y)) (drift C (0, y)) y (diffusion C (0, y)) (drift C (0, y)) y 0 hz
    rw [e, gen_ell C hc hz] at h
    simp only [neg_zero, Real.exp_zero, one_mul, zero_mul, sub_zero] at h
    rw [gm, if_pos hz, PhiT, posPart_self (openOrthant_sub hz)]
    exact h
  · have h := driftGen_Gphi_out hK hKs hbig (lphi_contDiffAt hc) 0 (diffusion C (0, y))
      (drift C (0, y)) y (diffusion C (0, y)) (drift C (0, y)) y 0 hz
    rw [e] at h
    simp only [neg_zero, Real.exp_zero, one_mul, zero_mul] at h
    rw [gm, if_neg hz]
    exact h.le

end C2a

section C2b
variable {n : ℕ}

theorem real_le_of_ito {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F Z D E : Ω → ℝ} {c β : ℝ} (hF0 : ∀ᵐ ω ∂P, 0 ≤ F ω) (hFm : AEStronglyMeasurable F P)
    (hZi : Integrable Z P) (hZ0 : ∫ ω, Z ω ∂P = 0) (hEq : ∀ᵐ ω ∂P, F ω = c + Z ω + D ω)
    (hD : ∀ᵐ ω ∂P, D ω ≤ β + E ω) (hE : Integrable E P) :
    ∫ ω, F ω ∂P ≤ c + β + ∫ ω, E ω ∂P := by
  have hle : ∀ᵐ ω ∂P, F ω ≤ Z ω + (c + β) + E ω := by
    filter_upwards [hEq, hD] with ω h1 h2
    rw [h1]; linarith
  have hi : Integrable (fun ω => Z ω + (c + β) + E ω) P :=
    (hZi.add (integrable_const _)).add hE
  have hFi : Integrable F P := hi.mono' hFm (by
    filter_upwards [hle, hF0] with ω h h0
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h)
  calc ∫ ω, F ω ∂P ≤ ∫ ω, (Z ω + (c + β) + E ω) ∂P := integral_mono_ae hFi hi hle
    _ = c + β + ∫ ω, E ω ∂P := by
      have e1 : ∫ ω, (Z ω + (c + β) + E ω) ∂P = ∫ ω, (Z ω + (c + β)) ∂P + ∫ ω, E ω ∂P :=
        integral_add (hZi.add (integrable_const _)) hE
      have e2 : ∫ ω, (Z ω + (c + β)) ∂P = ∫ ω, Z ω ∂P + ∫ _ω, (c + β) ∂P :=
        integral_add hZi (integrable_const _)
      rw [e1, e2, hZ0, integral_const]
      (first | simp only [probReal_univ, smul_eq_mul, one_mul, zero_add] | simp)

theorem meas_path_int {Ω : Type*} [MeasurableSpace Ω] {Y : ℝ≥0 → Ω → SDEState n}
    (hm : ∀ s, Measurable (Y s)) (hc : ∀ ω, Continuous fun s => Y s ω) {h : SDEState n → ℝ}
    (hh : Continuous h) (t : ℝ≥0) :
    Measurable (fun ω => ∫ u in (0 : ℝ)..t.val, h (Y u.toNNReal ω)) :=
  measurable_intervalIntegral_of_continuous _ t (H := fun s ω => h (Y s ω))
    (fun s _ => hh.measurable.comp (hm s)) (fun ω => hh.comp (hc ω))

theorem path_cont {Ω : Type*} {Y : ℝ≥0 → Ω → SDEState n} (hc : ∀ ω, Continuous fun s => Y s ω)
    {h : SDEState n → ℝ} (hh : Continuous h) (ω : Ω) :
    Continuous (fun u : ℝ => h (Y u.toNNReal ω)) :=
  hh.comp ((hc ω).comp continuous_real_toNNReal)

theorem lphi_measurable (c p : SDEState n) : Measurable (lphi c p) := by
  unfold lphi ellf
  refine Measurable.add_const (Measurable.sub ?_ ?_) _
  · exact Real.measurable_log.comp (Sf_contDiff c).continuous.measurable
  · exact Finset.measurable_sum _ fun i _ => measurable_const.mul
      (Real.measurable_log.comp (PiLp.continuous_apply 2 _ i).measurable)

set_option maxHeartbeats 1000000 in
/-- The Ito step for `ℓ` with saturation level `m`: real and `ℝ≥0∞` forms. -/
theorem ito_lphi_m {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {C : Coeffs n} {B : ℝ≥0 → Ω → SDEState n} (hB : IsStandardBrownian P B)
    (hC : ∀ i, LocallyLipschitzOn (orthant n) (C.f i) ∧ LocallyLipschitzOn (orthant n) (C.g i))
    {c p : SDEState n} (hc : c ∈ openOrthant n) (hp : ∀ i, 0 < p i) (hp1 : ∑ i, p i < 1)
    {x : SDEState n} {Y : ℝ≥0 → Ω → SDEState n}
    (hY : SolvesBrownianSDE P (diffusion C) (drift C) B (fun _ => x) Y) (t : ℝ≥0) {m : ℝ}
    (hm : 0 ≤ m)
    (hEi : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, gm C c p m (Y u.toNNReal ω)) P) :
    ∫ ω, Gphi (lphi c p) m (Y t ω) ∂P ≤
        Gphi (lphi c p) m x + 0 + ∫ ω, (∫ u in (0 : ℝ)..t.val, gm C c p m (Y u.toNNReal ω)) ∂P ∧
      ∫⁻ ω, ENNReal.ofReal (Gphi (lphi c p) m (Y t ω)) ∂P ≤ ENNReal.ofReal
        (Gphi (lphi c p) m x + 0 + ∫ ω, (∫ u in (0 : ℝ)..t.val, gm C c p m (Y u.toNNReal ω)) ∂P) := by
  have hK := boxK_isCompact 1 (Real.exp (m + 1) - 1) c p
  have hKs := boxK_sub 1 (Real.exp (m + 1) - 1) c p
  have hbig := lphi_big hm hc hp hp1
  have hφ := lphi_contDiffAt (p := p) hc
  have hGc := Gphi_contDiff hK hKs hbig hφ
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hp i).le
  obtain ⟨hσ, hb, -⟩ := kolm_trunc C hC
  have hY' : SolvesBrownianSDE P (fun q => (fun z => diffusion C (0, z)) q.2)
      (fun q => (fun z => drift C (0, z)) q.2) B (fun _ => x) Y := hY
  obtain ⟨hXm, hXc, hXa, hX0, JX, -, -, hJX, -, hXeq⟩ := hY'
  have hX0' : ∀ᵐ ω ∂P, Y 0 ω = x := by filter_upwards [hX0] with ω h using h
  have hFb : ∀ (i : Fin (n + n + 1)) (j : Fin n), ∃ K, ∀ s ω (a : ℝ), 0 ≤ a →
      |fderiv ℝ (FG (Gphi (lphi c p) m)) (pack (Y s ω) (Y s ω) a) (EuclideanSpace.single i 1) *
        pack (scol (diffusion C (0, Y s ω)) j) (scol (diffusion C (0, Y s ω)) j) 0 i| ≤ K := by
    intro i j
    obtain ⟨K, hK⟩ := Gphi_integrand_bound hK hKs hbig hφ hσ j
    exact ⟨K, fun s ω a ha => (FG_integrand_le hGc _ _ ha i _ _).trans (hK _)⟩
  obtain ⟨Z, hZi, hZ0, hZeq⟩ := ito_coupled_F hB x (X := Y) (Y := Y)
    (HX := fun s ω => diffusion C (0, Y s ω)) (HY := fun s ω => diffusion C (0, Y s ω))
    (JX := JX) (JY := JX)
    (bX := fun s ω => drift C (0, Y s ω)) (bY := fun s ω => drift C (0, Y s ω)) hXm hXm hXc hXc
    hXa hXa
    (fun s => (hσ.measurable.comp (hXa s) :)) (fun s => (hσ.measurable.comp (hXa s) :))
    (fun ω => hσ.comp (hXc ω)) (fun ω => hσ.comp (hXc ω))
    (fun s => (hb.measurable.comp (hXa s) :)) (fun s => (hb.measurable.comp (hXa s) :))
    (fun ω => hb.comp (hXc ω)) (fun ω => hb.comp (hXc ω)) hJX hJX hXeq hXeq
    hX0' hX0' (κ := fun _ _ => 0) continuous_const (fun _ _ => le_refl 0) (FG_contDiff hGc) hFb t
  have hEq : ∀ᵐ ω ∂P, Gphi (lphi c p) m (Y t ω) = Gphi (lphi c p) m x + Z ω +
      ∫ u in (0 : ℝ)..t.val, drG C (Gphi (lphi c p) m) (Y u.toNNReal ω) := by
    filter_upwards [hZeq] with ω h
    simp only [intervalIntegral.integral_zero, FG_pack, driftGen_FG_zero C hGc, neg_zero,
      Real.exp_zero, one_mul] at h
    exact h
  have hD : ∀ᵐ ω ∂P, ∫ u in (0 : ℝ)..t.val, drG C (Gphi (lphi c p) m) (Y u.toNNReal ω) ≤
      0 + ∫ u in (0 : ℝ)..t.val, gm C c p m (Y u.toNNReal ω) := ae_of_all _ fun ω => by
    rw [zero_add]
    exact intervalIntegral.integral_mono_on t.2
      ((path_cont hXc (drG_continuous C hC hGc) ω).intervalIntegrable _ _)
      ((path_cont hXc (gm_continuous C hc hp hp1 hC hm) ω).intervalIntegrable _ _)
      (fun u _ => drG_le C hc hp hp1 hm _)
  have hF0 : ∀ᵐ ω ∂P, 0 ≤ Gphi (lphi c p) m (Y t ω) :=
    ae_of_all _ fun ω => Gphi_nonneg hm (lphi_nonneg hc hp0 hp1.le) _
  have hFm : AEStronglyMeasurable (fun ω => Gphi (lphi c p) m (Y t ω)) P :=
    (hGc.continuous.measurable.comp (hXm t)).aestronglyMeasurable
  exact ⟨real_le_of_ito hF0 hFm hZi hZ0 hEq hD hEi, lintegral_le_of_ito hF0 hZi hZ0 hEq hD hEi⟩

end C2b

section C2c
variable {n : ℕ}

theorem occ_lint' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) (T : ℝ) (g : SDEState n → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂(occMean P X x T) =
      (ENNReal.ofReal T)⁻¹ * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, g (X x s.toNNReal ω)) ∂P := by
  have hF : Measurable (fun q : ℝ × Ω => X x q.1.toNNReal q.2) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ) (ω : Ω) => X x s.toNNReal ω)
      (fun ω => (hc ω).comp continuous_real_toNNReal) (fun s => hm _)
  unfold occMean
  rw [lintegral_smul_measure, lintegral_map hg hF,
    lintegral_prod_symm (fun q : ℝ × Ω => g (X x q.1.toNNReal q.2)) ((hg.comp hF).aemeasurable),
    smul_eq_mul]

theorem occ_ae' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) (T : ℝ)
    (hinv : ∀ᵐ ω ∂P, ∀ t, X x t ω ∈ orthant n) :
    ∀ᵐ y ∂(occMean P X x T), y ∈ orthant n := by
  have hS : MeasurableSet (orthant n)ᶜ := orthant_isClosed.measurableSet.compl
  have := occ_lint' P X x hm hc T ((orthant n)ᶜ.indicator 1) (measurable_one.indicator hS)
  rw [lintegral_indicator_one hS] at this
  rw [ae_iff]
  change occMean P X x T (orthant n)ᶜ = 0
  rw [this]
  have h0 : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (orthant n)ᶜ.indicator 1 (X x s.toNNReal ω)) =ᵐ[P] 0 := by
    filter_upwards [hinv] with ω hω
    (first | simp only [mem_compl_iff, hω, not_true_eq_false, not_false_eq_true, indicator_of_notMem, lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter, Real.volume_Icc, sub_zero, zero_mul, Pi.zero_apply] | simp [Set.indicator_apply, hω])
  rw [lintegral_congr_ae h0]
  (first | simp only [Pi.zero_apply, lintegral_const, measure_univ, mul_one, mul_zero] | simp)

theorem setIcc_eq_interval {h : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) :
    ∫ s in Set.Icc (0 : ℝ) T, h s = ∫ u in (0 : ℝ)..T, h u := by
  rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]

/-- `T ∫ h d(occMean) = E ∫₀ᵀ h(X_u) du` for continuous `h` with an integrable majorant path integral. -/
theorem occ_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : SDEState n → ℝ≥0 → Ω → SDEState n) (x : SDEState n) (hm : ∀ t, Measurable (X x t))
    (hc : ∀ ω, Continuous fun t => X x t ω) {T : ℝ} (hT : 0 < T) {h : SDEState n → ℝ}
    (hh : Continuous h) {w : SDEState n → ℝ} (hw : Continuous w) (hhw : ∀ y, |h y| ≤ w y)
    (hwi : Integrable (fun ω => ∫ u in (0 : ℝ)..T.toNNReal.val, w (X x u.toNNReal ω)) P) :
    T * ∫ y, h y ∂(occMean P X x T) =
      ∫ ω, (∫ u in (0 : ℝ)..T.toNNReal.val, h (X x u.toNNReal ω)) ∂P := by
  have htv : T.toNNReal.val = T := Real.coe_toNNReal T hT.le
  have hF : Measurable (fun q : ℝ × Ω => X x q.1.toNNReal q.2) :=
    measurable_uncurry_of_continuous_of_measurable (u := fun (s : ℝ) (ω : Ω) => X x s.toNNReal ω)
      (fun ω => (hc ω).comp continuous_real_toNNReal) (fun s => hm _)
  have hfm : AEStronglyMeasurable (fun q : ℝ × Ω => h (X x q.1.toNNReal q.2))
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) := (hh.measurable.comp hF).aestronglyMeasurable
  have hnorm : (fun ω => ∫ s in Set.Icc (0 : ℝ) T, ‖h (X x s.toNNReal ω)‖) =
      fun ω => ∫ u in (0 : ℝ)..T.toNNReal.val, |h (X x u.toNNReal ω)| := by
    funext ω; rw [htv, setIcc_eq_interval hT.le]; rfl
  have hint : Integrable (fun q : ℝ × Ω => h (X x q.1.toNNReal q.2))
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) := by
    rw [integrable_prod_iff' hfm]
    refine ⟨ae_of_all _ fun ω => ?_, ?_⟩
    · exact (path_cont hc hh ω).integrableOn_Icc
    · rw [hnorm]
      refine hwi.mono' (meas_path_int hm hc hh.abs _).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      have h0 : 0 ≤ ∫ u in (0 : ℝ)..T.toNNReal.val, |h (X x u.toNNReal ω)| :=
        intervalIntegral.integral_nonneg T.toNNReal.2 fun u _ => abs_nonneg _
      rw [abs_of_nonneg h0]
      exact intervalIntegral.integral_mono_on T.toNNReal.2
        ((path_cont hc hh.abs ω).intervalIntegrable _ _) ((path_cont hc hw ω).intervalIntegrable _ _)
        (fun u _ => hhw _)
  unfold occMean
  rw [integral_smul_measure, integral_map hF.aemeasurable hh.aestronglyMeasurable,
    integral_prod_symm _ hint, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hT.le,
    ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  show ∫ s in Set.Icc (0 : ℝ) T, h (X x s.toNNReal ω) = _
  rw [htv, setIcc_eq_interval hT.le]

set_option maxHeartbeats 1000000 in
/-- Child C2 (p. 17): `E ln V(X(T)) - ln V(x) ≤ T ∫ Φ d(occMean)`. -/
theorem c2_log_mean {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n)
    (hpδ : l1 p ≤ δ₀) :
    ∀ x ∈ openOrthant n, ∀ T : ℝ, 0 < T →
      ∫ ω, Real.log (Vfun c p (X x T.toNNReal ω)) ∂P - Real.log (Vfun c p x) ≤
        T * ∫ y, Phi C c p y ∂(occMean P X x T) := by
  intro x hx T hT
  obtain ⟨hP, hB, hsol⟩ := id hX
  have hc : c ∈ openOrthant n := hA.2.2.1
  have hγ : 0 < γb := hA.2.2.2.1
  have hδ0 : 0 < δ₀ := hδ₀.1
  have hδ1 : δ₀ < 1 := delta0_lt_one hn hA hδ₀
  have hp1 : ∑ i, p i < 1 := by rw [sum_p_eq hp]; linarith
  have hpos : ∀ i, 0 < p i := hp
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hp i).le
  have hC := hA.2.1
  set t : ℝ≥0 := T.toNNReal with htdef
  have hY := hsol x (openOrthant_sub hx)
  have hY' := hY
  obtain ⟨hXm, hXc, -⟩ := hY'
  have hxf : x ∈ faceOpen (Finset.univ : Finset (Fin n)) :=
    ⟨openOrthant_sub hx, fun i hi => absurd (Finset.mem_univ i) hi, fun i _ => hx i⟩
  have hposY : ∀ᵐ ω ∂P, ∀ s, X x s ω ∈ openOrthant n := by
    filter_upwards [face_inv C hB hC hxf hY] with ω h using fun s i => (h s).2.2 i (Finset.mem_univ i)
  set Kc : ℝ := 2 / δ₀ + γb / (3 * δ₀ ^ 2) with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  have hPc := PhiT_continuous C p hc hC
  have hwc := wK_continuous C γb δ₀ hC
  have hwKc : Continuous fun y => Kc * wK C γb δ₀ y := continuous_const.mul hwc
  have hW0 : ∀ ω, 0 ≤ ∫ u in (0 : ℝ)..t.val, wK C γb δ₀ (X x u.toNNReal ω) := fun ω =>
    intervalIntegral.integral_nonneg t.2 fun u _ => wK_nonneg C hγ.le hδ0.le _
  have hWint : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, wK C γb δ₀ (X x u.toNNReal ω)) P :=
    ⟨(meas_path_int hXm hXc hwc t).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ hW0)).2
        ((lintegral_wK_le P C B X hX c γb δ₀ hA hδ₀ (openOrthant_sub hx) t).trans_lt
          ENNReal.ofReal_lt_top)⟩
  have hKWint : Integrable (fun ω => ∫ u in (0 : ℝ)..t.val, Kc * wK C γb δ₀ (X x u.toNNReal ω)) P := by
    simp only [intervalIntegral.integral_const_mul]; exact hWint.const_mul Kc
  have hbnd : ∀ (g : SDEState n → ℝ), Continuous g → (∀ y, |g y| ≤ |PhiT C c p y|) → ∀ ω,
      ‖∫ u in (0 : ℝ)..t.val, g (X x u.toNNReal ω)‖ ≤
        ∫ u in (0 : ℝ)..t.val, Kc * wK C γb δ₀ (X x u.toNNReal ω) := fun g hg hgb ω =>
    intervalIntegral.norm_integral_le_of_norm_le t.2 (ae_of_all _ fun u _ => by
      rw [Real.norm_eq_abs]
      exact (hgb _).trans (PhiT_abs_le hn hA hδ₀ hp hpδ _))
      ((path_cont hXc hwKc ω).intervalIntegrable _ _)
  have hgmc : ∀ m : ℕ, Continuous (gm C c p (m : ℝ)) := fun m =>
    gm_continuous C hc hpos hp1 hC (Nat.cast_nonneg m)
  have hEi : ∀ m : ℕ, Integrable
      (fun ω => ∫ u in (0 : ℝ)..t.val, gm C c p (m : ℝ) (X x u.toNNReal ω)) P := fun m =>
    hKWint.mono' (meas_path_int hXm hXc (hgmc m) t).aestronglyMeasurable
      (ae_of_all _ (hbnd _ (hgmc m) (gm_abs_le C c p _)))
  -- the limit of the drift integrals
  set J : ℝ := ∫ ω, (∫ u in (0 : ℝ)..t.val, PhiT C c p (X x u.toNNReal ω)) ∂P with hJ
  have hElim : Tendsto (fun m : ℕ => ∫ ω, (∫ u in (0 : ℝ)..t.val,
      gm C c p (m : ℝ) (X x u.toNNReal ω)) ∂P) atTop (𝓝 J) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ω => ∫ u in (0 : ℝ)..t.val, Kc * wK C γb δ₀ (X x u.toNNReal ω))
      (fun m => (meas_path_int hXm hXc (hgmc m) t).aestronglyMeasurable) hKWint
      (fun m => ae_of_all _ (hbnd _ (hgmc m) (gm_abs_le C c p _))) ?_
    filter_upwards [hposY] with ω hω
    exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun u => |PhiT C c p (X x u.toNNReal ω)|)
      (Eventually.of_forall fun m => (path_cont hXc (hgmc m) ω).aestronglyMeasurable)
      (Eventually.of_forall fun m => ae_of_all _ fun u _ => by
        rw [Real.norm_eq_abs]; exact gm_abs_le C c p _ _)
      ((path_cont hXc hPc.abs ω).intervalIntegrable _ _)
      (ae_of_all _ fun u _ => gm_tendsto C c p (hω _))
  have hGx : Tendsto (fun m : ℕ => Gphi (lphi c p) (m : ℝ) x) atTop (𝓝 (lphi c p x)) := by
    apply tendsto_atTop_of_eventually_const (i₀ := ⌈lphi c p x⌉₊)
    intro m hm
    rw [Gphi, if_pos hx, hsat_eq_self (Nat.cast_nonneg m)
      ((Nat.le_ceil _).trans (Nat.cast_le.2 hm))]
  have hIto := fun m : ℕ => ito_lphi_m hB hC hc hpos hp1 hY t (Nat.cast_nonneg m) (hEi m)
  have hR : Tendsto (fun m : ℕ => Gphi (lphi c p) (m : ℝ) x + 0 + ∫ ω, (∫ u in (0 : ℝ)..t.val,
      gm C c p (m : ℝ) (X x u.toNNReal ω)) ∂P) atTop (𝓝 (lphi c p x + 0 + J)) :=
    (hGx.add tendsto_const_nhds).add hElim
  have hRnn : 0 ≤ lphi c p x + 0 + J := by
    refine ge_of_tendsto hR (Eventually.of_forall fun m => ?_)
    exact (integral_nonneg fun ω => Gphi_nonneg (Nat.cast_nonneg m)
      (lphi_nonneg hc hp0 hp1.le) _).trans (hIto m).1
  -- Fatou in the saturation level
  have hfm : ∀ m : ℕ, Measurable fun ω =>
      ENNReal.ofReal (Gphi (lphi c p) (m : ℝ) (X x t ω)) := fun m =>
    ENNReal.measurable_ofReal.comp ((Gphi_contDiff (boxK_isCompact 1 (Real.exp ((m : ℝ) + 1) - 1) c p)
      (boxK_sub _ _ _ _) (lphi_big (Nat.cast_nonneg m) hc hpos hp1)
      (lphi_contDiffAt hc)).continuous.measurable.comp (hXm t))
  have hlim : ∀ᵐ ω ∂P, liminf (fun m : ℕ => ENNReal.ofReal (Gphi (lphi c p) (m : ℝ) (X x t ω)))
      atTop = ENNReal.ofReal (lphi c p (X x t ω)) := by
    filter_upwards [hposY] with ω hω
    apply Tendsto.liminf_eq
    apply tendsto_atTop_of_eventually_const (i₀ := ⌈lphi c p (X x t ω)⌉₊)
    intro m hm
    rw [Gphi, if_pos (hω t), hsat_eq_self (Nat.cast_nonneg m)
      ((Nat.le_ceil _).trans (Nat.cast_le.2 hm))]
  have hfat : ∫⁻ ω, ENNReal.ofReal (lphi c p (X x t ω)) ∂P ≤
      ENNReal.ofReal (lphi c p x + 0 + J) := by
    rw [← lintegral_congr_ae hlim]
    refine (lintegral_liminf_le hfm).trans ?_
    have hT' := ((ENNReal.continuous_ofReal.tendsto _).comp hR)
    rw [← hT'.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun m => (hIto m).2)
  have hL0 : ∀ᵐ ω ∂P, 0 ≤ lphi c p (X x t ω) := by
    filter_upwards [hposY] with ω hω using lphi_nonneg hc hp0 hp1.le _ (hω t)
  have hLm : AEStronglyMeasurable (fun ω => lphi c p (X x t ω)) P :=
    ((lphi_measurable c p).comp (hXm t)).aestronglyMeasurable
  have hLint : Integrable (fun ω => lphi c p (X x t ω)) P :=
    ⟨hLm, (hasFiniteIntegral_iff_ofReal hL0).2 (hfat.trans_lt ENNReal.ofReal_lt_top)⟩
  have hLle : ∫ ω, lphi c p (X x t ω) ∂P ≤ lphi c p x + 0 + J := by
    rw [integral_eq_lintegral_of_nonneg_ae hL0 hLm]
    exact ENNReal.toReal_le_of_le_ofReal hRnn hfat
  -- back to `ln V` and the occupation measure
  have hlogY : (fun ω => Real.log (Vfun c p (X x t ω))) =ᵐ[P]
      fun ω => lphi c p (X x t ω) - Acst c p := by
    filter_upwards [hposY] with ω hω
    rw [log_Vfun hc (hω t)]; unfold lphi; ring
  have hlogx : Real.log (Vfun c p x) = lphi c p x - Acst c p := by
    rw [log_Vfun hc hx]; unfold lphi; ring
  have hocc : T * ∫ y, Phi C c p y ∂(occMean P X x T) = J := by
    have hae := occ_ae' P X x hXm hXc T (by
      filter_upwards [hposY] with ω hω using fun s => openOrthant_sub (hω s))
    have e1 : ∫ y, Phi C c p y ∂(occMean P X x T) = ∫ y, PhiT C c p y ∂(occMean P X x T) :=
      integral_congr_ae (by filter_upwards [hae] with y hy; rw [PhiT, posPart_self hy])
    rw [e1, hJ]
    exact occ_integral P X x hXm hXc hT hPc hwKc (fun y => PhiT_abs_le hn hA hδ₀ hp hpδ y)
      hKWint
  rw [integral_congr_ae hlogY, integral_sub hLint (integrable_const _), integral_const, hlogx, hocc]
  have hu : P.real Set.univ = 1 := by (first | simp only [Measure.real, measure_univ, ENNReal.toReal_one] | simp [Measure.real, measure_univ])
  rw [hu, one_smul]
  linarith

end C2c

end P41L

end FlatM_PB
-- ===== PC =====
section FlatM_PC
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
set_option autoImplicit false

namespace P41L
open ItoLib EthierKurtz StochKolmogorov.Persist

section C3
/-! C3: continuity of `(x, T) ↦ T ∫ Φ d(occMean)` from the Feller property and the
uniform moment bound (3.8) (Lemma 3.2), by truncation of `Φ` and dominated convergence. -/
variable {n : ℕ}

end C3

section C3main

end C3main
end P41L

end FlatM_PC

end SpeedInst

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open StochKolmogorov.Persist in
open EthierKurtz in
theorem solution {n : ℕ} (hn : 0 < n) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : Coeffs n) (B : ℝ≥0 → Ω → SDEState n) (X : SDEState n → ℝ≥0 → Ω → SDEState n)
    (hX : IsSolutionFamily P C B X) (c : SDEState n) (γb : ℝ) (hA : Assumption11 C c γb)
    (δ₀ : ℝ) (hδ₀ : IsDelta0 C γb δ₀) (p : SDEState n) (hp : p ∈ openOrthant n)
    (hpδ : l1 p ≤ δ₀) :
    ∀ x ∈ openOrthant n, ∀ T : ℝ, 0 < T →
      ∫ ω, Real.log (Vfun c p (X x T.toNNReal ω)) ∂P - Real.log (Vfun c p x) ≤
        T * ∫ y, Phi C c p y ∂(occMean P X x T) := by
  exact P41L.c2_log_mean hn P C B X hX c γb hA δ₀ hδ₀ p hp hpδ
