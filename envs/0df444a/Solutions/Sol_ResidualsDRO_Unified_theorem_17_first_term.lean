-- Prove2me | solution 1 for ResidualsDRO.Unified.theorem_17_first_term
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:35:37.266328+00:00
-- url     : https://prove2.me/submissions/3c3a7412-9e92-4473-95bf-d280f3182504

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
    (h15 : Assumption15 P D x r)
    :
    IsBigOp P (fun n ω => ⨆ z ∈ 𝒵,
        ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gstarS c D x 𝔓 n ω z|) (fun n : ℕ => (n : ℝ) ^ (-(r / 2))) := by
  obtain ⟨hL, hLbdd⟩ := h9
  obtain ⟨_, hCζ, N12, hN12⟩ := h12
  obtain ⟨hr0, _, hA15, hB15⟩ := h15
  set Lbar := sSup (L '' 𝒵) with hLbardef
  have hLle : ∀ z ∈ 𝒵, L z ≤ Lbar := fun z hz => le_csSup hLbdd ⟨z, hz, rfl⟩
  have hLbar0 : 0 ≤ Lbar := by
    obtain ⟨z0, hz0⟩ := h𝒵ne
    exact (hL z0 hz0).1.trans (hLle z0 hz0)
  intro δ hδ
  obtain ⟨M1, hM1, N1, h1⟩ := hA15 (δ / 2) (by positivity)
  obtain ⟨M2, hM2, N2, h2⟩ := hB15 (δ / 2) (by positivity)
  set K := Real.sqrt (2 * M1 + 2 * M2) with hKdef
  set M : ℝ := Lbar * (Cμ + (1 + Real.sqrt Cζ) * K) + 1 with hMdef
  have hM : 0 < M := by positivity
  refine ⟨M, hM, max (max N1 N2) (max N12 1), fun n hn => ?_⟩
  have hn1' : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2' : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn12 : N12 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  set w : ℝ := (n : ℝ) ^ (-(r / 2)) with hwdef
  have hw : 0 ≤ w := Real.rpow_nonneg hnpos.le _
  have hwr : (n : ℝ) ^ (-r) = w ^ 2 := by
    rw [hwdef, ← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; congr 1; push_cast; ring
  have hnr : (n : ℝ) ^ (-r) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by linarith)
  have hsub : {ω | ENNReal.ofReal (M * w) < ⨆ z ∈ 𝒵,
        ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gstarS c D x 𝔓 n ω z|} ⊆
      {ω | ENNReal.ofReal (M1 * (n : ℝ) ^ (-r)) < ENNReal.ofReal (‖D.fstar x - D.fhat n ω x‖ ^ 2)} ∪
      {ω | ENNReal.ofReal (M2 * (n : ℝ) ^ (-r)) < ENNReal.ofReal ((n : ℝ)⁻¹ *
        ∑ i : Fin n, ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖ ^ 2)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    obtain ⟨hA, hB⟩ := hcon
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hA hB
    refine absurd hω (not_lt.mpr (iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal ?_))
    -- notation
    set a : Fin n → ℝ := fun i => ‖epsTilde D x n ω i‖ with hadef
    set T : ℝ := (n : ℝ)⁻¹ * ∑ i, a i ^ 2 with hTdef
    have hT : T ≤ (2 * M1 + 2 * M2) * (n : ℝ) ^ (-r) := by
      have hpt : ∀ i : Fin n, a i ^ 2 ≤ 2 * ‖D.fstar x - D.fhat n ω x‖ ^ 2 +
          2 * ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖ ^ 2 := by
        intro i
        have htri : a i ≤ ‖D.fstar x - D.fhat n ω x‖ +
            ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖ := by
          simp only [hadef, epsTilde]
          rw [← norm_neg (D.fstar x - D.fhat n ω x), neg_sub]
          exact norm_add_le _ _
        have ha0 : 0 ≤ a i := norm_nonneg _
        nlinarith [sq_nonneg (‖D.fstar x - D.fhat n ω x‖ -
          ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖)]
      calc T ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, (2 * ‖D.fstar x - D.fhat n ω x‖ ^ 2 +
            2 * ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hpt i) (by positivity)
        _ = 2 * ‖D.fstar x - D.fhat n ω x‖ ^ 2 + 2 * ((n : ℝ)⁻¹ *
            ∑ i : Fin n, ‖D.fstar (D.xs i ω) - D.fhat n ω (D.xs i ω)‖ ^ 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              ← Finset.mul_sum]
            field_simp
            ring
        _ ≤ (2 * M1 + 2 * M2) * (n : ℝ) ^ (-r) := by linarith
    have hsqT : Real.sqrt T ≤ K * w := by
      rw [hKdef, ← Real.sqrt_sq hw, ← Real.sqrt_mul (by positivity), ← hwr]
      exact Real.sqrt_le_sqrt hT
    have hT0 : 0 ≤ T := by positivity
    -- deviations bound of Assumption 12
    have hsupeq := hN12 n hn12 hn1
    have hbddS : BddAbove (Set.range fun p : 𝔓 n =>
        ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2) := by
      refine ⟨n, ?_⟩
      rintro _ ⟨p, rfl⟩
      have hp := h𝔓 n p p.2
      have hpi : ∀ i, (p : Fin n → ℝ) i ≤ 1 := fun i => by
        rw [← hp.2]
        exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
      have hinv : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn1)
      have hinv0 : 0 ≤ (n : ℝ)⁻¹ := by positivity
      calc ∑ i, ((p : Fin n → ℝ) i - (n : ℝ)⁻¹) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have := hp.1 i; have := hpi i
            nlinarith
        _ = n := by simp
    have hS : ∀ p ∈ 𝔓 n, ∑ i, (p i - (n : ℝ)⁻¹) ^ 2 ≤ Cζ * (n : ℝ) ^ (-(1 + r)) := by
      intro p hp
      rw [← hsupeq]
      exact le_ciSup hbddS (⟨p, hp⟩ : 𝔓 n)
    have hSa : Real.sqrt (Cζ * (n : ℝ) ^ (-(1 + r)) * ∑ i, a i ^ 2) ≤
        Real.sqrt Cζ * Real.sqrt T := by
      rw [← Real.sqrt_mul hCζ.le]
      apply Real.sqrt_le_sqrt
      have : Cζ * (n : ℝ) ^ (-(1 + r)) * ∑ i, a i ^ 2 = Cζ * T * (n : ℝ) ^ (-r) := by
        rw [hTdef, show -(1 + r) = -r + -1 by ring, Real.rpow_add hnpos, Real.rpow_neg_one]
        ring
      rw [this]
      have : 0 ≤ Cζ * T := mul_nonneg hCζ.le hT0
      nlinarith
    have hμn : 0 ≤ μ n := by rw [hμ n]; positivity
    -- pointwise in p
    have hLz := hL z hz
    have hpbound : ∀ p : 𝔓 n,
        |∑ i, (p : Fin n → ℝ) i * (⨆ y : scenarioBall D x (μ n) n ω i, c z y) -
          ∑ i, (p : Fin n → ℝ) i * c z (D.fstar x + D.eps i ω)| ≤
          Lbar * (μ n + (1 + Real.sqrt Cζ) * Real.sqrt T) := by
      intro p
      have hp := h𝔓 n p p.2
      rw [← Finset.sum_sub_distrib]
      calc |∑ i, ((p : Fin n → ℝ) i * (⨆ y : scenarioBall D x (μ n) n ω i, c z y) -
            (p : Fin n → ℝ) i * c z (D.fstar x + D.eps i ω))|
          ≤ ∑ i, |(p : Fin n → ℝ) i * (⨆ y : scenarioBall D x (μ n) n ω i, c z y) -
            (p : Fin n → ℝ) i * c z (D.fstar x + D.eps i ω)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (p : Fin n → ℝ) i * (L z * (μ n + a i)) := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← mul_sub, abs_mul, abs_of_nonneg (hp.1 i)]
            exact mul_le_mul_of_nonneg_left
              (rdro17_inner D x c h𝒴convex hproj hrange z (L z) hLz.1 hLz.2 (μ n) hμn n ω i)
              (hp.1 i)
        _ = L z * (μ n + ∑ i, (p : Fin n → ℝ) i * a i) := by
            have hexp : ∀ i, (p : Fin n → ℝ) i * (L z * (μ n + a i)) =
                L z * μ n * (p : Fin n → ℝ) i + L z * ((p : Fin n → ℝ) i * a i) := fun i => by ring
            simp_rw [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2]
            ring
        _ ≤ Lbar * (μ n + (1 + Real.sqrt Cζ) * Real.sqrt T) := by
            have hw' := rdro17_weighted hn1 (p : Fin n → ℝ) a hp.2 _ (hS p p.2)
            have hsum0 : 0 ≤ ∑ i, (p : Fin n → ℝ) i * a i :=
              Finset.sum_nonneg fun i _ => mul_nonneg (hp.1 i) (norm_nonneg _)
            have hin : μ n + ∑ i, (p : Fin n → ℝ) i * a i ≤
                μ n + (1 + Real.sqrt Cζ) * Real.sqrt T := by
              rw [← hTdef] at hw'
              nlinarith
            exact mul_le_mul (hLle z hz) hin (by positivity) hLbar0
    have : Nonempty (𝔓 n) := (h𝔓ne n hn1).to_subtype
    have hbddG : BddAbove (Set.range fun p : 𝔓 n =>
        ∑ i, (p : Fin n → ℝ) i * c z (D.fstar x + D.eps i ω)) := by
      refine ⟨∑ i : Fin n, |c z (D.fstar x + D.eps i ω)|, ?_⟩
      rintro _ ⟨p, rfl⟩
      have hp := h𝔓 n p p.2
      refine Finset.sum_le_sum fun i _ => ?_
      have hpi : (p : Fin n → ℝ) i ≤ 1 := by
        rw [← hp.2]
        exact Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
      calc (p : Fin n → ℝ) i * c z (D.fstar x + D.eps i ω)
          ≤ (p : Fin n → ℝ) i * |c z (D.fstar x + D.eps i ω)| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (hp.1 i)
        _ ≤ 1 * |c z (D.fstar x + D.eps i ω)| :=
            mul_le_mul_of_nonneg_right hpi (abs_nonneg _)
        _ = _ := one_mul _
    unfold ghatER gstarS
    refine (rdro17_abs_iSup_sub _ _ _ hbddG hpbound).trans ?_
    rw [hμ n, hMdef]
    have : (1 + Real.sqrt Cζ) * Real.sqrt T ≤ (1 + Real.sqrt Cζ) * (K * w) :=
      mul_le_mul_of_nonneg_left hsqT (by positivity)
    have h' : Lbar * (Cμ * w + (1 + Real.sqrt Cζ) * Real.sqrt T) ≤
        Lbar * (Cμ * w + (1 + Real.sqrt Cζ) * (K * w)) :=
      mul_le_mul_of_nonneg_left (by linarith) hLbar0
    nlinarith
  calc P {ω | ENNReal.ofReal (M * w) < ⨆ z ∈ 𝒵,
        ENNReal.ofReal |ghatER c D x 𝔓 μ n ω z - gstarS c D x 𝔓 n ω z|}
      ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add (h1 n hn1') (h2 n hn2')
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
