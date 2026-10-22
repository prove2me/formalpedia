-- Prove2me | solution 1 for ShockWear.WearProcess.proof410_passSurv_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:08:03.296521+00:00
-- url     : https://prove2.me/submissions/7bd361aa-f3a4-4b14-95bf-39f18dde9899

import Mathlib
import Definitions.Def_ShockWear_WearProcess_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal


namespace ShockWear.WearProcess

theorem passSurv_limit_core {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (hZ : IsMonotoneWear pr Z) (x : ℝ) (t : ℝ≥0) :
    Tendsto (fun ε : ℝ≥0 => wearCdf pr Z (t + ε) x) (𝓝[>] 0)
      (𝓝 (passSurv pr Z x (t : ℝ))) := by
  set f : ℝ≥0 → ℝ := fun ε => wearCdf pr Z (t + ε) x with hf
  have hmono : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂pr, Z a ω ≤ Z b ω := by
    intro a b hab
    filter_upwards [hZ.start_mono] with ω hω
    exact hω.2 hab
  -- f is antitone
  have hanti : Antitone f := by
    intro a b hab
    simp only [hf, wearCdf]
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    filter_upwards [hmono (t + a) (t + b) (add_le_add le_rfl hab)] with ω hω h
    exact le_trans hω h
  have hlim := hanti.tendsto_nhdsGT 0
  -- sequence
  let e : ℕ → ℝ≥0 := fun n => ((n : ℝ≥0) + 1)⁻¹
  have he : Tendsto e atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · rw [← NNReal.tendsto_coe]
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      refine this.congr fun n => ?_
      simp [e, one_div]
    · simp [e]
  have h1 := hlim.comp he
  -- the sets
  let A : ℕ → Set Ω := fun n => {ω | Z (t + e n) ω ≤ x}
  let B : ℕ → Set Ω := fun n => ⋃ m ∈ Finset.range (n + 1), A m
  have heanti : Antitone e := by
    intro a b hab
    simp only [e]
    exact inv_anti₀ (by positivity) (by gcongr)
  have hBA : ∀ n, B n =ᵐ[pr] A n := by
    intro n
    refine (ae_eq_set).2 ⟨?_, ?_⟩
    · refine measure_mono_null (fun ω hω => hω) (?_ : pr (B n \ A n) = 0)
      have : B n \ A n ⊆ ⋃ m ∈ Finset.range (n + 1), (A m \ A n) := by
        intro ω ⟨hb, ha⟩
        simp only [B, Set.mem_iUnion] at hb
        obtain ⟨m, hm, hmA⟩ := hb
        simp only [Set.mem_iUnion]
        exact ⟨m, hm, hmA, ha⟩
      refine measure_mono_null this ?_
      refine (measure_biUnion_null_iff (Finset.range (n+1)).countable_toSet).2 fun m hm => ?_
      have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
      have := hmono (t + e n) (t + e m) (add_le_add le_rfl (heanti hmn))
      rw [ae_iff] at this
      refine measure_mono_null ?_ this
      intro ω ⟨h1, h2⟩ h3
      exact h2 (le_trans h3 h1)
    · have : A n \ B n = ∅ := by
        ext ω
        simp only [Set.mem_diff, Set.mem_empty_iff_false, iff_false, not_and, not_not, B,
          Set.mem_iUnion]
        intro h
        exact ⟨n, Finset.self_mem_range_succ n, h⟩
      rw [this]; simp
  have hBmono : Monotone B := by
    intro a b hab ω hω
    simp only [B, Set.mem_iUnion] at hω ⊢
    obtain ⟨m, hm, h⟩ := hω
    exact ⟨m, Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hm) (by omega)), h⟩
  have hU : (⋃ n, B n) = ⋃ n, A n := by
    ext ω
    simp only [B, Set.mem_iUnion]
    constructor
    · rintro ⟨n, m, _, h⟩; exact ⟨m, h⟩
    · rintro ⟨m, h⟩; exact ⟨m, m, Finset.self_mem_range_succ m, h⟩
  -- passage set
  have hS : {ω | ENNReal.ofReal (t : ℝ) < passTime Z x ω} =ᵐ[pr] ⋃ n, A n := by
    filter_upwards [hZ.start_mono] with ω hω
    apply propext
    change _ ↔ ω ∈ ⋃ n, A n
    rw [Set.mem_iUnion, ENNReal.ofReal_coe_nnreal]
    change _ ↔ ∃ n, Z (t + e n) ω ≤ x
    constructor
    · intro h
      obtain ⟨r, htr, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
      have htr' : t < r := by exact_mod_cast htr
      have : (0 : ℝ) < (r : ℝ) - t := by
        have : (t : ℝ) < r := by exact_mod_cast htr'
        linarith
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt this
      refine ⟨n, ?_⟩
      by_contra hc
      push_neg at hc
      have hle : passTime Z x ω ≤ ((t + e n : ℝ≥0) : ℝ≥0∞) := by
        unfold passTime
        exact iInf₂_le (f := fun (s : ℝ≥0) (_ : x < Z s ω) => (s : ℝ≥0∞)) (t + e n) hc
      have hlt : t + e n < r := by
        have : ((t + e n : ℝ≥0) : ℝ) < r := by
          simp only [e, NNReal.coe_add, NNReal.coe_inv, NNReal.coe_natCast]
          push_cast
          have : (1 : ℝ) / ((n : ℝ) + 1) = ((n : ℝ) + 1)⁻¹ := one_div _
          linarith
        exact_mod_cast this
      have : ((t + e n : ℝ≥0) : ℝ≥0∞) < r := by exact_mod_cast hlt
      exact absurd (lt_trans (lt_of_le_of_lt hle this) hr) (lt_irrefl _)
    · rintro ⟨n, hn⟩
      have hpos : (0 : ℝ≥0) < e n := by simp [e]
      have : ((t + e n : ℝ≥0) : ℝ≥0∞) ≤ passTime Z x ω := by
        unfold passTime
        refine le_iInf₂ fun s hs => ?_
        by_contra hc
        push_neg at hc
        have hc' : s ≤ t + e n := by exact_mod_cast hc.le
        exact absurd (lt_of_lt_of_le hs ((hω.2 hc').trans hn)) (lt_irrefl _)
      refine lt_of_lt_of_le ?_ this
      exact_mod_cast (lt_add_of_pos_right t hpos)
  have h2 : Tendsto (fun n => (pr (A n)).toReal) atTop
      (𝓝 (passSurv pr Z x (t : ℝ))) := by
    have := tendsto_measure_iUnion_atTop (μ := pr) hBmono
    rw [hU] at this
    have hpass : passSurv pr Z x (t : ℝ) = (pr (⋃ n, A n)).toReal := by
      unfold passSurv
      rw [if_neg (not_lt.2 (NNReal.coe_nonneg t)), measure_congr hS]
    rw [hpass]
    refine ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this).congr fun n => ?_
    simp only [Function.comp]
    rw [measure_congr (hBA n)]
  have h3 : (f ∘ e) = fun n => (pr (A n)).toReal := by
    funext n; rfl
  rw [h3] at h1
  have := tendsto_nhds_unique h1 h2
  rw [← this]
  exact hlim

end ShockWear.WearProcess

open ShockWear.WearProcess


theorem solution {Ω : Type*} [MeasurableSpace Ω] (pr : Measure Ω)
    [IsProbabilityMeasure pr] (Z : ℝ≥0 → Ω → ℝ) (hZ : IsMonotoneWear pr Z) (x : ℝ) (t : ℝ≥0) :
    Tendsto (fun ε : ℝ≥0 => wearCdf pr Z (t + ε) x) (𝓝[>] 0)
      (𝓝 (passSurv pr Z x (t : ℝ))) := by
  exact passSurv_limit_core pr Z hZ x t
