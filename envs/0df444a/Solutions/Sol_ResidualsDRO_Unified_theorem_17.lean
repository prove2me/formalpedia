-- Prove2me | solution 1 for ResidualsDRO.Unified.theorem_17
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:30:07.816849+00:00
-- url     : https://prove2.me/submissions/2bd2d406-c992-413e-9953-987e2435e298

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions
import Theorems.Thm_ResidualsDRO_Unified_theorem_17_combined

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ResidualsDRO.Unified

theorem rdro17_bigOp_mono {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : ℕ → Ω → ℝ≥0∞) (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (hUV : ∀ n ω, U n ω ≤ 2 * V n ω) (hV : IsBigOp P V w) : IsBigOp P U w := by
  intro δ hδ
  obtain ⟨M, hM, N, hN⟩ := hV δ hδ
  refine ⟨2 * M, by positivity, N, fun n hn => le_trans (measure_mono ?_) (hN n hn)⟩
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hle
  push Not at hle
  have h1 : U n ω ≤ 2 * ENNReal.ofReal (M * w n) := (hUV n ω).trans (by gcongr)
  have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (M * w n) = ENNReal.ofReal (2 * M * w n) := by
    rw [mul_assoc, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]; simp
  rw [h2] at h1
  exact absurd hω (not_lt.mpr h1)

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
    (zhat : ℕ → Ω → EuclideanSpace ℝ (Fin dz))
    (hzhat : ∀ n ω, zhat n ω ∈ 𝒵 ∧
      ∀ z ∈ 𝒵, ghatER c D x 𝔓 μ n ω (zhat n ω) ≤ ghatER c D x 𝔓 μ n ω z)
    (zstar : EuclideanSpace ℝ (Fin dz))
    (hzstar : zstar ∈ 𝒵 ∧ ∀ z ∈ 𝒵, gTrue c D x Pε zstar ≤ gTrue c D x Pε z)
    :
    IsBigOp P (fun n ω => ENNReal.ofReal
        |ghatER c D x 𝔓 μ n ω (zhat n ω) - gTrue c D x Pε zstar|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) ∧
      IsBigOp P (fun n ω => ENNReal.ofReal
        |gTrue c D x Pε (zhat n ω) - gTrue c D x Pε zstar|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) := by
  have hS := theorem_17_combined P D x Pε c 𝒵 h𝒵 h𝒵ne h𝒴ne h𝒴closed h𝒴convex hproj hrange hint
    𝔓 h𝔓 h𝔓ne r Cζ Cμ μ hCμ hμ L h9 h12 h13 P' V h14 h15
  set S : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ z ∈ 𝒵,
    ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z| with hSdef
  have hw : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-(r / 2)) := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hle : ∀ n ω, ∀ z ∈ 𝒵,
      ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z| ≤ S n ω := by
    intro n ω z hz
    exact le_iSup₂ (f := fun z (_ : z ∈ 𝒵) =>
      ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z|) z hz
  have key : ∀ n ω,
      ENNReal.ofReal |ghatER c D x 𝔓 μ n ω (zhat n ω) - gTrue c D x Pε zstar| ≤ S n ω ∧
      ENNReal.ofReal |gTrue c D x Pε (zhat n ω) - gTrue c D x Pε zstar| ≤ 2 * S n ω := by
    intro n ω
    obtain ⟨hzm, hzmin⟩ := hzhat n ω
    set a := ghatER c D x 𝔓 μ n ω (zhat n ω)
    set b := ghatER c D x 𝔓 μ n ω zstar
    set ga := gTrue c D x Pε (zhat n ω)
    set gb := gTrue c D x Pε zstar
    have hab : a ≤ b := hzmin zstar hzstar.1
    have hgab : gb ≤ ga := hzstar.2 _ hzm
    have h1 := hle n ω _ hzm
    have h2 := hle n ω _ hzstar.1
    constructor
    · rcases le_total a gb with h | h
      · calc ENNReal.ofReal |a - gb| ≤ ENNReal.ofReal |a - ga| := by
              apply ENNReal.ofReal_le_ofReal
              rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
          _ ≤ S n ω := h1
      · calc ENNReal.ofReal |a - gb| ≤ ENNReal.ofReal |b - gb| := by
              apply ENNReal.ofReal_le_ofReal
              rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
          _ ≤ S n ω := h2
    · calc ENNReal.ofReal |ga - gb| ≤ ENNReal.ofReal (|a - ga| + |b - gb|) := by
            apply ENNReal.ofReal_le_ofReal
            rw [abs_of_nonneg (by linarith)]
            rw [abs_sub_comm a ga]
            linarith [le_abs_self (ga - a), le_abs_self (b - gb)]
        _ ≤ ENNReal.ofReal |a - ga| + ENNReal.ofReal |b - gb| := ENNReal.ofReal_add_le
        _ ≤ S n ω + S n ω := add_le_add h1 h2
        _ = 2 * S n ω := (two_mul _).symm
  refine ⟨rdro17_bigOp_mono P _ S _ hw (fun n ω => (key n ω).1.trans ?_) hS,
    rdro17_bigOp_mono P _ S _ hw (fun n ω => (key n ω).2) hS⟩
  calc S n ω = 1 * S n ω := (one_mul _).symm
    _ ≤ 2 * S n ω := by gcongr; norm_num
