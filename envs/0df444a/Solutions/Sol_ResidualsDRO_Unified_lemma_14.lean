-- Prove2me | solution 1 for ResidualsDRO.Unified.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:38:02.188203+00:00
-- url     : https://prove2.me/submissions/8d241595-e1b0-4185-bcef-52059297c378

import Mathlib
import Definitions.Def_ResidualsDRO_Unified_IsBigOp
import Definitions.Def_ResidualsDRO_Unified_Setting
import Definitions.Def_ResidualsDRO_Unified_Assumptions

open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace ResidualsDRO.Unified

/-- The nearest-point projection onto a convex set is nonexpansive. -/
lemma rdro17_proj_nonexp {dy : ℕ} {K : Set (EuclideanSpace ℝ (Fin dy))} (hK : Convex ℝ K)
    {proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy)} (hp : IsProjection K proj)
    (u v : EuclideanSpace ℝ (Fin dy)) : ‖proj u - proj v‖ ≤ ‖u - v‖ := by
  have hvi : ∀ u, ∀ w ∈ K, ⟪u - proj u, w - proj u⟫ ≤ 0 := by
    intro u
    have hmem := (hp u).1
    refine (norm_eq_iInf_iff_real_inner_le_zero hK hmem).mp ?_
    have : Nonempty K := ⟨⟨_, hmem⟩⟩
    refine le_antisymm (le_ciInf fun w => (hp u).2 w w.2) ?_
    have hbdd : BddBelow (Set.range fun w : K => ‖u - (w : EuclideanSpace ℝ (Fin dy))‖) :=
      ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hbdd (⟨proj u, hmem⟩ : K)
  set a := proj u
  set b := proj v
  have h1 := hvi u b (hp v).1
  have h2 := hvi v a (hp u).1
  have key : ⟪u - v, a - b⟫ - ‖a - b‖ ^ 2 = -⟪u - a, b - a⟫ - ⟪v - b, a - b⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm]
    ring
  have h3 : ‖a - b‖ ^ 2 ≤ ‖u - v‖ * ‖a - b‖ := by
    have := real_inner_le_norm (u - v) (a - b)
    linarith
  rcases (norm_nonneg (a - b)).eq_or_lt with h | h
  · rw [← h]; exact norm_nonneg _
  · nlinarith

/-- `|sup F - sup G| ≤ B` when `|F - G| ≤ B` pointwise. -/
lemma rdro17_abs_iSup_sub {ι : Type*} [Nonempty ι] (F G : ι → ℝ) (B : ℝ)
    (hG : BddAbove (Set.range G)) (h : ∀ i, |F i - G i| ≤ B) :
    |(⨆ i, F i) - ⨆ i, G i| ≤ B := by
  have hF : BddAbove (Set.range F) := by
    obtain ⟨b, hb⟩ := hG
    refine ⟨b + B, ?_⟩
    rintro _ ⟨i, rfl⟩
    have := hb ⟨i, rfl⟩
    linarith [le_abs_self (F i - G i), h i]
  rw [abs_le]
  constructor
  · have : (⨆ i, G i) ≤ (⨆ i, F i) + B := ciSup_le fun i => by
      have := le_ciSup hF i
      linarith [neg_abs_le (F i - G i), h i]
    linarith
  · have : (⨆ i, F i) ≤ (⨆ i, G i) + B := ciSup_le fun i => by
      have := le_ciSup hG i
      linarith [le_abs_self (F i - G i), h i]
    linarith

/-- Weighted average bound: `∑ pᵢ aᵢ ≤ √((1/n)∑ aᵢ²) + √(S ∑ aᵢ²)`. -/
lemma rdro17_weighted {n : ℕ} (hn : 1 ≤ n) (p a : Fin n → ℝ) (hp1 : ∑ i, p i = 1)
    (S : ℝ) (hS : ∑ i, (p i - (n : ℝ)⁻¹) ^ 2 ≤ S) :
    ∑ i, p i * a i ≤ Real.sqrt ((n : ℝ)⁻¹ * ∑ i, a i ^ 2) + Real.sqrt (S * ∑ i, a i ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have heq : ∑ i, p i * a i = (n : ℝ)⁻¹ * ∑ i, a i + ∑ i, (p i - (n : ℝ)⁻¹) * a i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    congr 1; ext i; ring
  rw [heq]
  have hA : (n : ℝ)⁻¹ * ∑ i, a i ≤ Real.sqrt ((n : ℝ)⁻¹ * ∑ i, a i ^ 2) := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := a)
    simp only [Finset.card_univ, Fintype.card_fin] at hcs
    rw [mul_pow]
    calc (n : ℝ)⁻¹ ^ 2 * (∑ i, a i) ^ 2 ≤ (n : ℝ)⁻¹ ^ 2 * (n * ∑ i, a i ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (by positivity)
      _ = (n : ℝ)⁻¹ * ∑ i, a i ^ 2 := by field_simp
  have hB : ∑ i, (p i - (n : ℝ)⁻¹) * a i ≤ Real.sqrt (S * ∑ i, a i ^ 2) := by
    refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
    calc (∑ i, (p i - (n : ℝ)⁻¹) * a i) ^ 2
        ≤ (∑ i, (p i - (n : ℝ)⁻¹) ^ 2) * ∑ i, a i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ S * ∑ i, a i ^ 2 :=
          mul_le_mul_of_nonneg_right hS (Finset.sum_nonneg fun i _ => sq_nonneg _)
  linarith

/-- Inner robust supremum versus the true-scenario cost. -/
lemma rdro17_inner {dx dy dz : ℕ} {Ω : Type*} (D : ERData dx dy Ω) (x : EuclideanSpace ℝ (Fin dx))
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (h𝒴convex : Convex ℝ D.𝒴) (hproj : IsProjection D.𝒴 D.proj)
    (hrange : ∀ (i : ℕ) (ω : Ω), D.fstar x + D.eps i ω ∈ D.𝒴)
    (z : EuclideanSpace ℝ (Fin dz)) (Lz : ℝ) (hLz : 0 ≤ Lz)
    (hlip : ∀ y ∈ D.𝒴, ∀ y' ∈ D.𝒴, |c z y - c z y'| ≤ Lz * ‖y - y'‖)
    (μ : ℝ) (hμ : 0 ≤ μ) (n : ℕ) (ω : Ω) (i : Fin n) :
    |(⨆ y : scenarioBall D x μ n ω i, c z y) - c z (D.fstar x + D.eps i ω)| ≤
      Lz * (μ + ‖epsTilde D x n ω i‖) := by
  set ys := D.fstar x + D.eps i ω
  have hys : ys ∈ D.𝒴 := hrange i ω
  set sc := scenario D x n ω i
  have hsc : ‖sc - ys‖ ≤ ‖epsTilde D x n ω i‖ := by
    have hpy : D.proj ys = ys := by
      have := (hproj ys).2 ys hys
      simp only [sub_self, norm_zero] at this
      exact (sub_eq_zero.mp (norm_le_zero_iff.mp this)).symm
    calc ‖sc - ys‖ = ‖D.proj (D.fhat n ω x + residual D n ω i) - D.proj ys‖ := by
          rw [hpy]; rfl
      _ ≤ ‖(D.fhat n ω x + residual D n ω i) - ys‖ := rdro17_proj_nonexp h𝒴convex hproj _ _
      _ = ‖epsTilde D x n ω i‖ := by
          congr 1; simp only [residual, epsTilde, ys]; abel
  have hscmem : sc ∈ scenarioBall D x μ n ω i := ⟨(hproj _).1, by simp [sc, hμ]⟩
  have hup : ∀ y : scenarioBall D x μ n ω i, c z y ≤ c z ys + Lz * (μ + ‖epsTilde D x n ω i‖) := by
    rintro ⟨y, hy𝒴, hyb⟩
    have h1 := hlip y hy𝒴 ys hys
    have h2 : ‖y - ys‖ ≤ μ + ‖epsTilde D x n ω i‖ := by
      calc ‖y - ys‖ = ‖(y - sc) + (sc - ys)‖ := by congr 1; abel
        _ ≤ ‖y - sc‖ + ‖sc - ys‖ := norm_add_le _ _
        _ ≤ μ + ‖epsTilde D x n ω i‖ := add_le_add hyb hsc
    have := mul_le_mul_of_nonneg_left h2 hLz
    simp only
    linarith [le_abs_self (c z y - c z ys)]
  have hbdd : BddAbove (Set.range fun y : scenarioBall D x μ n ω i => c z y) :=
    ⟨_, by rintro _ ⟨y, rfl⟩; exact hup y⟩
  have : Nonempty (scenarioBall D x μ n ω i) := ⟨⟨sc, hscmem⟩⟩
  rw [abs_le]
  constructor
  · have h1 := le_ciSup hbdd ⟨sc, hscmem⟩
    have h2 := hlip sc (hproj _).1 ys hys
    have h3 := mul_le_mul_of_nonneg_left hsc hLz
    have h4 : 0 ≤ Lz * μ := mul_nonneg hLz hμ
    simp only at h1
    linarith [neg_abs_le (c z sc - c z ys)]
  · have := ciSup_le hup
    linarith

lemma rdro17_dev_le {n : ℕ} (hn : 1 ≤ n) (p : Fin n → ℝ) (hp0 : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) : ∑ i, (p i - (n : ℝ)⁻¹) ^ 2 ≤ n := by
  have hpi : ∀ i, p i ≤ 1 := fun i => by
    rw [← hp1]
    exact Finset.single_le_sum (fun j _ => hp0 j) (Finset.mem_univ i)
  have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  have hinv0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
  calc ∑ i, (p i - (n : ℝ)⁻¹) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := hp0 i; have := hpi i
        nlinarith
    _ = n := by simp

end ResidualsDRO.Unified

open ResidualsDRO.Unified

theorem solution
    {dx dy dz : ℕ} {Ω : Type*}
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
    (μ : ℕ → ℝ) (hμ : ∀ n : ℕ, 0 ≤ μ n)
    (L : EuclideanSpace ℝ (Fin dz) → ℝ) (h9 : Assumption9 c D.𝒴 𝒵 L)
    (n : ℕ) (hn : 1 ≤ n) (ω : Ω)
    :
    (⨆ z ∈ 𝒵, ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z|) ≤
      ENNReal.ofReal (sSup (L '' 𝒵) *
          (μ n + Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n, ‖epsTilde D x n ω i‖ ^ 2)) *
          ⨆ p : 𝔓 n, Real.sqrt (1 + n * ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2)) +
        ENNReal.ofReal (⨆ p : 𝔓 n, Real.sqrt (n * ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2)) *
          (⨆ z ∈ 𝒵, ENNReal.ofReal
            (Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n, (c z (D.fstar x + D.eps i ω)) ^ 2))) +
        ⨆ z ∈ 𝒵, ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z| := by
  obtain ⟨hL, hLbdd⟩ := h9
  set Lbar := sSup (L '' 𝒵) with hLbardef
  have hLle : ∀ z ∈ 𝒵, L z ≤ Lbar := fun z hz => le_csSup hLbdd ⟨z, hz, rfl⟩
  have hLbar0 : 0 ≤ Lbar := by
    obtain ⟨z0, hz0⟩ := h𝒵ne
    exact (hL z0 hz0).1.trans (hLle z0 hz0)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have : Nonempty (𝔓 n) := (h𝔓ne n hn).to_subtype
  set a : Fin n → ℝ := fun i => ‖epsTilde D x n ω i‖ with hadef
  set T : ℝ := (n : ℝ)⁻¹ * ∑ i, a i ^ 2 with hTdef
  set Dv : 𝔓 n → ℝ := fun p => ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2 with hDv
  have hDv0 : ∀ p, 0 ≤ Dv p := fun p => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hDvle : ∀ p, Dv p ≤ n := fun p =>
    rdro17_dev_le hn p (h𝔓 n p p.2).1 (h𝔓 n p p.2).2
  set S1 := ⨆ p : 𝔓 n, Real.sqrt (1 + n * Dv p) with hS1
  set S2 := ⨆ p : 𝔓 n, Real.sqrt (n * Dv p) with hS2
  have hbdd1 : BddAbove (Set.range fun p : 𝔓 n => Real.sqrt (1 + n * Dv p)) :=
    ⟨Real.sqrt (1 + n * n), by
      rintro _ ⟨p, rfl⟩
      exact Real.sqrt_le_sqrt (by nlinarith [hDvle p])⟩
  have hbdd2 : BddAbove (Set.range fun p : 𝔓 n => Real.sqrt (n * Dv p)) :=
    ⟨Real.sqrt (n * n), by
      rintro _ ⟨p, rfl⟩
      exact Real.sqrt_le_sqrt (by nlinarith [hDvle p])⟩
  have hS1ge : ∀ p, Real.sqrt (1 + n * Dv p) ≤ S1 := fun p => le_ciSup hbdd1 p
  have hS2ge : ∀ p, Real.sqrt (n * Dv p) ≤ S2 := fun p => le_ciSup hbdd2 p
  have hS2nn : 0 ≤ S2 := (Real.sqrt_nonneg _).trans (hS2ge (Classical.arbitrary _))
  -- identity n ∑ pᵢ² = 1 + n Dv p
  have hsq : ∀ p : 𝔓 n, (n : ℝ) * ∑ i, (p : Fin n → ℝ) i ^ 2 = 1 + n * Dv p := by
    intro p
    have hp1 := (h𝔓 n p p.2).2
    have : Dv p = ∑ i, (p : Fin n → ℝ) i ^ 2 - 2 * (n : ℝ)⁻¹ * ∑ i, (p : Fin n → ℝ) i +
        n * (n : ℝ)⁻¹ ^ 2 := by
      simp only [hDv, sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      congr 1
      · congr 1
        refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, hp1]
    field_simp
    ring
  have hrhs : ∀ z ∈ 𝒵, ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z| ≤
      ENNReal.ofReal (Lbar * (μ n + Real.sqrt T) * S1) +
        ENNReal.ofReal S2 * ENNReal.ofReal
          (Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n, (c z (D.fstar x + D.eps i ω)) ^ 2)) +
        ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z| := by
    intro z hz
    set cv : Fin n → ℝ := fun i => c z (D.fstar x + D.eps i ω) with hcv
    set Q := (n : ℝ)⁻¹ * ∑ i : Fin n, cv i ^ 2 with hQ
    have hLz := hL z hz
    -- first term
    have hbddG : BddAbove (Set.range fun p : 𝔓 n => ∑ i, (p : Fin n → ℝ) i * cv i) := by
      refine ⟨∑ i : Fin n, |cv i|, ?_⟩
      rintro _ ⟨p, rfl⟩
      have hp := h𝔓 n p p.2
      refine Finset.sum_le_sum fun i _ => ?_
      have hpi : (p : Fin n → ℝ) i ≤ 1 := by
        rw [← hp.2]
        exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
      calc (p : Fin n → ℝ) i * cv i ≤ (p : Fin n → ℝ) i * |cv i| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (hp.1 i)
        _ ≤ 1 * |cv i| := mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
        _ = _ := one_mul _
    have hT0 : 0 ≤ T := by positivity
    have ht1 : |ghatER c D x 𝔓 μ n ω z - gstarS c D x 𝔓 n ω z| ≤
        Lbar * (μ n + Real.sqrt T) * S1 := by
      unfold ghatER gstarS
      refine rdro17_abs_iSup_sub _ _ _ hbddG fun p => ?_
      have hp := h𝔓 n p p.2
      rw [← Finset.sum_sub_distrib]
      have hpa : ∑ i, (p : Fin n → ℝ) i * a i ≤ Real.sqrt T * Real.sqrt (1 + n * Dv p) := by
        rw [← hsq p, ← Real.sqrt_mul hT0]
        refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
        calc (∑ i, (p : Fin n → ℝ) i * a i) ^ 2
            ≤ (∑ i, (p : Fin n → ℝ) i ^ 2) * ∑ i, a i ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
          _ = T * (n * ∑ i, (p : Fin n → ℝ) i ^ 2) := by rw [hTdef]; field_simp
      have hone : 1 ≤ Real.sqrt (1 + n * Dv p) := by
        rw [Real.one_le_sqrt]; nlinarith [hDv0 p]
      calc |∑ i, ((p : Fin n → ℝ) i * (⨆ y : scenarioBall D x (μ n) n ω i, c z y) -
            (p : Fin n → ℝ) i * cv i)|
          ≤ ∑ i, |(p : Fin n → ℝ) i * (⨆ y : scenarioBall D x (μ n) n ω i, c z y) -
            (p : Fin n → ℝ) i * cv i| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (p : Fin n → ℝ) i * (L z * (μ n + a i)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← mul_sub, abs_mul, abs_of_nonneg (hp.1 i)]
            exact mul_le_mul_of_nonneg_left
              (rdro17_inner D x c h𝒴convex hproj hrange z (L z) hLz.1 hLz.2 (μ n) (hμ n) n ω i)
              (hp.1 i)
        _ = L z * (μ n + ∑ i, (p : Fin n → ℝ) i * a i) := by
            have hexp : ∀ i, (p : Fin n → ℝ) i * (L z * (μ n + a i)) =
                L z * μ n * (p : Fin n → ℝ) i + L z * ((p : Fin n → ℝ) i * a i) := fun i => by ring
            simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2]
            ring
        _ ≤ Lbar * ((μ n + Real.sqrt T) * Real.sqrt (1 + n * Dv p)) := by
            have hsum0 : 0 ≤ ∑ i, (p : Fin n → ℝ) i * a i :=
              Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (norm_nonneg _)
            have hin : μ n + ∑ i, (p : Fin n → ℝ) i * a i ≤
                (μ n + Real.sqrt T) * Real.sqrt (1 + n * Dv p) := by
              have := hμ n
              nlinarith
            exact mul_le_mul (hLle z hz) hin (add_nonneg (hμ n) hsum0) hLbar0
        _ ≤ Lbar * (μ n + Real.sqrt T) * S1 := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_left (hS1ge p) (by have := hμ n; positivity)
    -- second term
    have ht2 : |gstarS c D x 𝔓 n ω z - gstarN c D x n ω z| ≤ S2 * Real.sqrt Q := by
      unfold gstarS gstarN
      have hconst : (n : ℝ)⁻¹ * ∑ i : Fin n, c z (D.fstar x + D.eps i ω) =
          ⨆ _p : 𝔓 n, (n : ℝ)⁻¹ * ∑ i : Fin n, cv i := (ciSup_const).symm
      rw [hconst]
      refine rdro17_abs_iSup_sub _ _ _ (by simp) fun p => ?_
      have heq : ∑ i, (p : Fin n → ℝ) i * cv i - (n : ℝ)⁻¹ * ∑ i, cv i =
          ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) * cv i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        congr 1; ext i; ring
      rw [heq]
      refine le_trans ?_ (mul_le_mul_of_nonneg_right (hS2ge p) (Real.sqrt_nonneg _))
      rw [← Real.sqrt_mul (mul_nonneg hnpos.le (hDv0 p))]
      apply Real.abs_le_sqrt
      calc (∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) * cv i) ^ 2
          ≤ (∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2) * ∑ i, cv i ^ 2 :=
            Finset.sum_mul_sq_le_sq_mul_sq _ _ _
        _ = n * Dv p * Q := by
            have hnn : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hnpos.ne'
            rw [hQ]
            simp only [hDv]
            linear_combination (-((∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2) *
              ∑ i, cv i ^ 2)) * hnn
    have htri : |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z| ≤
        |ghatER c D x 𝔓 μ n ω z - gstarS c D x 𝔓 n ω z| +
        |gstarS c D x 𝔓 n ω z - gstarN c D x n ω z| + |gstarN c D x n ω z - gTrue c D x Pε z| :=
      le_trans (abs_sub_le _ (gstarN c D x n ω z) _)
        (add_le_add_left (abs_sub_le _ (gstarS c D x 𝔓 n ω z) _) _) |>.trans (le_of_eq (by ring))
    calc ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gTrue c D x Pε z|
        ≤ ENNReal.ofReal (Lbar * (μ n + Real.sqrt T) * S1 + S2 * Real.sqrt Q +
            |gstarN c D x n ω z - gTrue c D x Pε z|) := ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (Lbar * (μ n + Real.sqrt T) * S1) + ENNReal.ofReal (S2 * Real.sqrt Q) +
            ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z| :=
          (ENNReal.ofReal_add_le).trans (add_le_add_left ENNReal.ofReal_add_le _)
      _ = _ := by rw [ENNReal.ofReal_mul hS2nn]
  refine iSup₂_le fun z hz => (hrhs z hz).trans ?_
  gcongr
  · exact le_iSup₂ (f := fun z (_ : z ∈ 𝒵) => ENNReal.ofReal
      (Real.sqrt ((n : ℝ)⁻¹ * ∑ i : Fin n, (c z (D.fstar x + D.eps i ω)) ^ 2))) z hz
  · exact le_iSup₂ (f := fun z (_ : z ∈ 𝒵) =>
      ENNReal.ofReal |gstarN c D x n ω z - gTrue c D x Pε z|) z hz
