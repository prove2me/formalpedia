-- Prove2me | solution 1 for ResidualsDRO.Unified.theorem_17_combined
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:30:08.571626+00:00
-- url     : https://prove2.me/submissions/7c53302f-3e03-4fad-a554-ecab93b5a33e

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions
import Theorems.Thm_ResidualsDRO_Unified_theorem_17_first_term
import Theorems.Thm_ResidualsDRO_Unified_theorem_17_second_term
import Theorems.Thm_ResidualsDRO_Unified_theorem_17_third_term

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

theorem rdro17c_bigOp_add3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U A B C : ℕ → Ω → ℝ≥0∞) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hU : ∀ n ω, U n ω ≤ A n ω + B n ω + C n ω)
    (hA : IsBigOp P A w) (hB : IsBigOp P B w) (hC : IsBigOp P C w) : IsBigOp P U w := by
  intro δ hδ
  obtain ⟨M1, hM1, N1, h1⟩ := hA (δ / 3) (by positivity)
  obtain ⟨M2, hM2, N2, h2⟩ := hB (δ / 3) (by positivity)
  obtain ⟨M3, hM3, N3, h3⟩ := hC (δ / 3) (by positivity)
  refine ⟨M1 + M2 + M3, by positivity, max (max N1 N2) N3, fun n hn => ?_⟩
  have hn1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn3 : N3 ≤ n := le_trans (le_max_right _ _) hn
  have hsub : {ω | ENNReal.ofReal ((M1 + M2 + M3) * w n) < U n ω} ⊆
      ({ω | ENNReal.ofReal (M1 * w n) < A n ω} ∪ {ω | ENNReal.ofReal (M2 * w n) < B n ω}) ∪
        {ω | ENNReal.ofReal (M3 * w n) < C n ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨ha, hb⟩, hc⟩ := hcon
    have hwn := hw n
    have : U n ω ≤ ENNReal.ofReal ((M1 + M2 + M3) * w n) := by
      calc U n ω ≤ A n ω + B n ω + C n ω := hU n ω
        _ ≤ ENNReal.ofReal (M1 * w n) + ENNReal.ofReal (M2 * w n) + ENNReal.ofReal (M3 * w n) := by
          gcongr
        _ = ENNReal.ofReal ((M1 + M2 + M3) * w n) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
    exact absurd hω (not_lt.mpr this)
  calc P {ω | ENNReal.ofReal ((M1 + M2 + M3) * w n) < U n ω}
      ≤ P (({ω | ENNReal.ofReal (M1 * w n) < A n ω} ∪ {ω | ENNReal.ofReal (M2 * w n) < B n ω}) ∪
        {ω | ENNReal.ofReal (M3 * w n) < C n ω}) := measure_mono hsub
    _ ≤ P {ω | ENNReal.ofReal (M1 * w n) < A n ω} + P {ω | ENNReal.ofReal (M2 * w n) < B n ω} +
        P {ω | ENNReal.ofReal (M3 * w n) < C n ω} :=
          (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := by
          gcongr
          · exact h1 n hn1
          · exact h2 n hn2
          · exact h3 n hn3
    _ = ENNReal.ofReal δ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring

theorem rdro17c_bigOp_rate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (C : ℕ → Ω → ℝ≥0∞) (w w' : ℕ → ℝ) (hww : ∀ n, 1 ≤ n → w' n ≤ w n)
    (hC : IsBigOp P C w') : IsBigOp P C w := by
  intro δ hδ
  obtain ⟨M, hM, N, hN⟩ := hC δ hδ
  refine ⟨M, hM, max N 1, fun n hn => le_trans (measure_mono ?_) (hN n (le_trans (le_max_left _ _) hn))⟩
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hω
  exact mul_le_mul_of_nonneg_left (hww n (le_trans (le_max_right _ _) hn)) hM.le

end ResidualsDRO.Unified

open ResidualsDRO.Unified

theorem solution
    {dx dy dz : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx))
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) (h𝒵 : IsCompact 𝒵) (h𝒵ne : 𝒵.Nonempty)
    (h𝒴ne : D.𝒴.Nonempty) (h𝒴closed : IsClosed D.𝒴) (h𝒴convex : Convex ℝ D.𝒴)
    (hproj : IsProjection D.𝒴 D.proj)
    (hrange : ∀ (i : ℕ) (ω : Ω), D.fstar x + D.eps i ω ∈ D.𝒴)
    (hint : ∀ z ∈ 𝒵, Integrable (fun e => c z (D.fstar x + e)) Pε)
    (𝔓 : (n : ℕ) → Set (Fin n → ℝ))
    (h𝔓 : ∀ n, ∀ p ∈ 𝔓 n, (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (h𝔓ne : ∀ n, 1 ≤ n → (𝔓 n).Nonempty)
    (r Cζ Cμ : ℝ) (μ : ℕ → ℝ) (hCμ : 0 < Cμ) (hμ : ∀ n : ℕ, μ n = Cμ * (n : ℝ) ^ (-(r / 2)))
    (L : EuclideanSpace ℝ (Fin dz) → ℝ) (h9 : Assumption9 c D.𝒴 𝒵 L)
    (h12 : Assumption12 𝔓 Cζ (1 + r))
    (h13 : Assumption13 P c D x Pε 𝒵)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (V : Ω' → C(𝒵, ℝ)) (h14 : Assumption14 P c D x Pε 𝒵 P' V)
    (h15 : Assumption15 P D x r)
    :
    IsBigOp P (fun n ω => ⨆ z ∈ 𝒵,
        ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) := by
  have hA := theorem_17_first_term P D x Pε c 𝒵 h𝒵 h𝒵ne h𝒴ne h𝒴closed h𝒴convex hproj hrange hint
    𝔓 h𝔓 h𝔓ne r Cζ Cμ μ hCμ hμ L h9 h12 h15
  have hB := theorem_17_second_term P D x Pε c 𝒵 h𝒵 h𝒵ne h𝒴ne h𝒴closed h𝒴convex hproj hrange hint
    𝔓 h𝔓 h𝔓ne r Cζ h12 h13
  have hC := theorem_17_third_term P D x Pε c 𝒵 h𝒵 h𝒵ne h𝒴ne h𝒴closed h𝒴convex hproj hrange hint
    P' V h14
  have hr1 : r ≤ 1 := h15.2.1
  have hC' := rdro17c_bigOp_rate P _ (fun n : ℕ => (n : ℝ) ^ (-(r / 2)))
    (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) (fun n hn => by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
      linarith) hC
  refine rdro17c_bigOp_add3 P _ _ _ _ _ (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun n ω => ?_) hA hB hC'
  refine iSup₂_le fun z hz => ?_
  have e1 : ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z| ≤
      ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gstarS c D x 𝔓 n ω z| +
      ENNReal.ofReal |gstarS c D x 𝔓 n ω z - gstarN c D x n ω z| +
      ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z| := by
    refine le_trans (ENNReal.ofReal_le_ofReal ?_)
      ((ENNReal.ofReal_add_le).trans (add_le_add_left ENNReal.ofReal_add_le _))
    · exact le_trans (abs_sub_le _ (gstarN c D x n ω z) _)
        (add_le_add_left (abs_sub_le _ (gstarS c D x 𝔓 n ω z) _) _) |>.trans (le_of_eq (by ring))
  refine e1.trans ?_
  gcongr
  · exact le_iSup₂ (f := fun z (_ : z ∈ 𝒵) =>
      ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gstarS c D x 𝔓 n ω z|) z hz
  · exact le_iSup₂ (f := fun z (_ : z ∈ 𝒵) =>
      ENNReal.ofReal |gstarS c D x 𝔓 n ω z - gstarN c D x n ω z|) z hz
  · exact le_iSup₂ (f := fun z (_ : z ∈ 𝒵) =>
      ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z|) z hz
