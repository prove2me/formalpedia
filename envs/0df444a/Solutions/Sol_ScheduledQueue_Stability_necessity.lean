-- Prove2me | solution 1 for ScheduledQueue.Stability.necessity
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T22:15:15.145666+00:00
-- url     : https://prove2.me/submissions/7c973385-cd5c-4045-998d-5fce26bc4e86

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed
import Theorems.Thm_ScheduledQueue_Stability_lower_decomposition
import Theorems.Thm_ScheduledQueue_Stability_Y_gamma2_finite
import Theorems.Thm_ScheduledQueue_Stability_joint_infinitely_often

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

namespace SQNecAux

theorem bc_eventually_lt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : ℝ} (hh : 0 < h) {W : Ω → ℝ} (hW : Integrable W P)
    (Z : ℕ → Ω → ℝ) (hZ : ∀ n, IdentDistrib (Z n) W P P) :
    ∀ᵐ ω ∂P, ∀ᶠ n : ℕ in atTop, Z n ω < n * h := by
  set X : Ω → ℝ := fun ω => max (W ω / h + 1) 0
  have hXint : Integrable X P := ((hW.div_const h).add (integrable_const 1)).pos_part
  have hX0 : 0 ≤ X := fun ω => le_max_right _ _
  have hfin : (∑' n : ℕ, P {ω | X ω ∈ Ioi (n : ℝ)}) < ∞ := by
    let _ : MeasureSpace Ω := ⟨P⟩
    exact tsum_prob_mem_Ioi_lt_top hXint hX0
  have hle : ∀ n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω} ≤ P {ω | X ω ∈ Ioi (n : ℝ)} := by
    intro n
    have e : P {ω | (n : ℝ) * h ≤ Z n ω} = P {ω | (n : ℝ) * h ≤ W ω} :=
      (hZ n).measure_mem_eq (s := {x | (n : ℝ) * h ≤ x}) (measurableSet_le measurable_const measurable_id)
    rw [e]
    apply measure_mono
    intro ω hω
    simp only [mem_setOf_eq, mem_Ioi, X] at hω ⊢
    have : (n : ℝ) ≤ W ω / h := by rw [le_div_iff₀ hh]; linarith
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsum : (∑' n : ℕ, P {ω | (n : ℝ) * h ≤ Z n ω}) ≠ ∞ :=
    (lt_of_le_of_lt (ENNReal.tsum_le_tsum hle) hfin).ne
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with n hn
  simpa using hn

open ScheduledQueue.Stability

/-- Almost surely every reversed count `#{j : R_j ∈ (0,s]}` is finite. -/
theorem revCount_finite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, revCount h ξ U s ω ≠ ⊤ := by
  have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0 : ℝ) 1 := by
    rw [hin.uniform.ae_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc.mem]
    exact ae_restrict_mem measurableSet_Icc
  have h1 : ∀ K : ℕ, ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, ξ (m : ℤ) ω + K < m * h := by
    intro K
    apply bc_eventually_lt hh (W := fun ω => ξ 0 ω + K)
      (hin.integrable.add (integrable_const _))
    intro m
    exact (hin.identDistrib (m : ℤ)).comp (u := fun x : ℝ => x + (K : ℝ)) (by fun_prop)
  have h2 : ∀ᵐ ω ∂P, ∀ᶠ m : ℕ in atTop, -ξ (-(m : ℤ)) ω + h < m * h := by
    apply bc_eventually_lt hh (W := fun ω => -ξ 0 ω + h)
      (hin.integrable.neg.add (integrable_const _))
    intro m
    exact (hin.identDistrib _).comp (u := fun x => -x + h) (by fun_prop)
  rw [← ae_all_iff] at h1
  filter_upwards [h1, h2, hU] with ω h1 h2 hU
  intro s
  obtain ⟨K, hK⟩ := exists_nat_ge s
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (h1 K)
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 h2
  have hsub : {j : ℤ | revArrival h ξ U j ω ∈ Ioc 0 s} ⊆
      (Finset.Icc (-(N2 : ℤ)) N1 : Set ℤ) := by
    intro j ⟨hj1, hj2⟩
    simp only [revArrival] at hj1 hj2
    simp only [Finset.coe_Icc, mem_Icc]
    constructor
    · by_contra hc
      have hm := hN2 (-j).toNat (by omega)
      have e : (-(((-j).toNat : ℕ) : ℤ)) = j := by omega
      have e2 : (((-j).toNat : ℕ) : ℝ) = -(j : ℝ) := by
        have : (((-j).toNat : ℕ) : ℤ) = -j := by omega
        exact_mod_cast this
      rw [e, e2] at hm
      nlinarith [hU.2]
    · by_contra hc
      have hm := hN1 j.toNat (by omega)
      have e : ((j.toNat : ℕ) : ℤ) = j := by omega
      have e2 : ((j.toNat : ℕ) : ℝ) = (j : ℝ) := by exact_mod_cast e
      rw [e, e2] at hm
      nlinarith [hU.1]
  exact ((Finset.finite_toSet _).subset hsub).encard_lt_top.ne

end SQNecAux

open ScheduledQueue.Stability SQNecAux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ)
    (hin : ScheduledInput P ξ U) :
    (¬ ∃ c : ℝ, ∀ᵐ ω ∂P, ξ 0 ω ≤ c) →
      ∀ᵐ ω ∂P, ∀ C : ℝ, ∃ s : ℝ, 0 ≤ s ∧ C < Lam h ξ U s ω - s := by
  intro hunb
  have hYG := Y_gamma2_finite P h hh ξ U hin
  have hU : ∀ᵐ ω ∂P, U ω ∈ Icc (0 : ℝ) 1 := by
    rw [hin.uniform.ae_iff (p := fun x => x ∈ Icc (0 : ℝ) 1) measurableSet_Icc.mem]
    exact ae_restrict_mem measurableSet_Icc
  -- a level `l` with `P(Y₀ ≤ l) > 0`
  obtain ⟨l, hl⟩ : ∃ l : ℕ, 0 < P {ω | Y h ξ 0 ω ≤ l} := by
    by_contra hcon
    push Not at hcon
    have h0 : P (⋃ l : ℕ, {ω | Y h ξ 0 ω ≤ l}) = 0 :=
      measure_iUnion_null fun l => le_antisymm (hcon l) bot_le
    have hmem : ∀ᵐ ω ∂P, ω ∈ ⋃ l : ℕ, {ω | Y h ξ 0 ω ≤ l} := by
      filter_upwards [hYG] with ω ⟨hY, _⟩
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (hY 0).ne
      exact mem_iUnion.2 ⟨m, by simp [← hm]⟩
    have hnot : ∀ᵐ ω ∂P, ω ∉ ⋃ l : ℕ, {ω | Y h ξ 0 ω ≤ l} := measure_eq_zero_iff_ae_notMem.1 h0
    have : ∀ᵐ ω ∂P, False := by
      filter_upwards [hmem, hnot] with ω h1 h2 using h2 h1
    obtain ⟨_, hfalse⟩ := this.exists
    exact hfalse
  have hJ : ∀ᵐ ω ∂P, ∀ r : ℕ, ∃ᶠ n : ℕ in atTop, Y h ξ n ω ≤ l ∧ (r : ℕ∞) < tildeY h ξ n ω := by
    rw [ae_all_iff]
    intro r
    exact joint_infinitely_often P h hh ξ U hin hunb l r hl
  filter_upwards [hYG, hJ, revCount_finite P h hh ξ U hin, hU] with ω ⟨_, hG⟩ hJω hfin hUω
  intro C
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.1 hG.ne
  set r : ℕ := ⌈C / h⌉₊ + l + g
  obtain ⟨n, hnY, hnT⟩ := (hJω r).exists
  have hdec := lower_decomposition h hh ξ U ω hUω n
  obtain ⟨R, hR⟩ := ENat.ne_top_iff_exists.1 (hfin ((n : ℝ) * h))
  have hT1 : ((r + 1 : ℕ) : ℕ∞) ≤ tildeY h ξ n ω := by
    have := Order.add_one_le_of_lt hnT
    exact_mod_cast this
  have hineq : ((n + (r + 1) : ℕ) : ℕ∞) ≤ ((R + l + g : ℕ) : ℕ∞) := by
    calc ((n + (r + 1) : ℕ) : ℕ∞) = (n : ℕ∞) + ((r + 1 : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ (n : ℕ∞) + tildeY h ξ n ω := by gcongr
      _ ≤ revCount h ξ U (n * h) ω + Y h ξ n ω + gamma2 h ξ ω := hdec
      _ ≤ (R : ℕ∞) + (l : ℕ∞) + (g : ℕ∞) := by rw [← hR, ← hg]; gcongr
      _ = _ := by push_cast; ring
  have hnat : n + (r + 1) ≤ R + l + g := by exact_mod_cast hineq
  refine ⟨n * h, by positivity, ?_⟩
  have hLam : Lam h ξ U (n * h) ω = h * R := by
    simp only [Lam, ← hR, ENat.toNat_coe]
  rw [hLam]
  have hceil : C / h ≤ ⌈C / h⌉₊ := Nat.le_ceil _
  have hC : C ≤ ⌈C / h⌉₊ * h := by rwa [div_le_iff₀ hh] at hceil
  have hnatR : (n : ℝ) + ((⌈C / h⌉₊ + l + g : ℕ) : ℝ) + 1 ≤ R + l + g := by
    exact_mod_cast (show n + (⌈C / h⌉₊ + l + g) + 1 ≤ R + l + g by omega)
  push_cast at hnatR
  nlinarith
