-- Prove2me | solution 1 for OTDRO.WorstCase.maximizers_bounded
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T07:32:27.135344+00:00
-- url     : https://prove2.me/submissions/01951d65-c0a2-478b-bef3-69696bd5d340

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

open MeasureTheory

/-- quadratic bound: from `e t² ≤ b t + D` with `e > 0`, get `|t| ≤ 1 + (|b| + |D|)/e`. -/
lemma otdro4_quad_bound (e b D t : ℝ) (he : 0 < e) (h : e * t ^ 2 ≤ b * t + D) :
    |t| ≤ 1 + (|b| + |D|) / e := by
  suffices hh : (|t| - 1) * e ≤ |b| + |D| by
    have := (le_div_iff₀ he).2 hh; linarith
  by_contra hc
  push Not at hc
  have hbt : b * t ≤ |b| * |t| := by
    rw [← abs_mul]; exact le_abs_self _
  have hD : D ≤ |D| := le_abs_self _
  have ht2 : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have h1 : 1 < |t| := by
    by_contra h1; push Not at h1
    nlinarith [abs_nonneg b, abs_nonneg D, abs_nonneg t]
  nlinarith [abs_nonneg b, abs_nonneg D, abs_nonneg t]

theorem solution {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0] (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax) (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ) (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B) :
    ∀ ε : ℝ, 0 < ε → ∀ x : EuclideanSpace ℝ (Fin d), ∀ β ∈ B, ∀ lam : ℝ,
      (OTDRO.Dual.growthKappa ℓ + ε) * Real.sqrt δ * OTDRO.Dual.quadInv A β x ≤ lam →
      ∃ C1 : ℝ, 0 < C1 ∧
        ∀ g ∈ OTDRO.Dual.maximizers ℓ A δ β lam x,
          Real.sqrt δ * |g| * OTDRO.Dual.quadInv A β x ≤ 1 + C1 * ε⁻¹ * (1 + |inner ℝ β x|) := by
  intro ε hε x β _ lam hlam
  set q := OTDRO.Dual.quadInv A β x with hq
  set a : ℝ := inner ℝ β x with ha
  have hsd : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hrhs : ∀ C1 : ℝ, 0 < C1 → 1 ≤ 1 + C1 * ε⁻¹ * (1 + |a|) := by
    intro C1 hC1
    have : 0 ≤ C1 * ε⁻¹ * (1 + |a|) := by positivity
    linarith
  rcases le_or_gt q 0 with hq0 | hq0
  · refine ⟨1, one_pos, fun g _ => ?_⟩
    have : Real.sqrt δ * |g| * q ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hq0
    linarith [hrhs 1 one_pos]
  -- choose `s` in the growth set with `s < κ + ε`
  set S := {s : ℝ | 0 ≤ s ∧ BddAbove (Set.range fun u : ℝ => ℓ u - s * u ^ 2)} with hS
  have hSne : S.Nonempty := h2.growth
  have hSbdd : BddBelow S := ⟨0, fun s hs => hs.1⟩
  obtain ⟨s, hsS, hslt⟩ : ∃ s ∈ S, s < OTDRO.Dual.growthKappa ℓ + ε :=
    exists_lt_of_csInf_lt hSne (by
      show sInf S < OTDRO.Dual.growthKappa ℓ + ε
      unfold OTDRO.Dual.growthKappa; linarith)
  obtain ⟨M, hM⟩ := hsS.2
  have hMu : ∀ u, ℓ u ≤ M + s * u ^ 2 := by
    intro u; have := hM ⟨u, rfl⟩; simp only at this; linarith
  -- r := lam / (√δ q) > s
  set r := lam / (Real.sqrt δ * q) with hr
  have hsdq : 0 < Real.sqrt δ * q := mul_pos hsd hq0
  have hrs : s < r := by
    rw [hr, lt_div_iff₀ hsdq]
    have : s * (Real.sqrt δ * q) < (OTDRO.Dual.growthKappa ℓ + ε) * Real.sqrt δ * q := by
      have := mul_lt_mul_of_pos_right hslt hsdq; linarith
    linarith
  have hrdef : r * (Real.sqrt δ * q) = lam := by
    rw [hr]; field_simp
  set D := M + s * a ^ 2 - ℓ a
  refine ⟨ε * (1 + (|2 * s * a| + |D|) / (r - s)) + 1, by
    have : 0 ≤ (|2 * s * a| + |D|) / (r - s) := by
      apply div_nonneg (by positivity); linarith
    positivity, fun g hg => ?_⟩
  -- maximality against γ = 0
  have hF := hg 0
  unfold OTDRO.Dual.Fobj at hF
  rw [← hq, ← ha] at hF
  set t := g * Real.sqrt δ * q with ht
  have hlt : lam * Real.sqrt δ * (g ^ 2 * q) = r * t ^ 2 := by
    rw [ht, ← hrdef]
    have : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
    have : q ≠ 0 := hq0.ne'
    field_simp
  have hU := hMu (a + t)
  have key : (r - s) * t ^ 2 ≤ (2 * s * a) * t + D := by
    have h0 : ℓ a - lam * Real.sqrt δ * ((0:ℝ) ^ 2 * q - 1) ≤
        ℓ (a + t) - lam * Real.sqrt δ * (g ^ 2 * q - 1) := by
      simpa using hF
    have : lam * Real.sqrt δ * (g ^ 2 * q - 1) = r * t ^ 2 - lam * Real.sqrt δ := by
      rw [mul_sub, hlt]; ring
    rw [this] at h0
    simp at h0
    simp only [D]
    nlinarith
  have hb := otdro4_quad_bound (r - s) (2 * s * a) D t (by linarith) key
  have hteq : Real.sqrt δ * |g| * q = |t| := by
    rw [ht, abs_mul, abs_mul, abs_of_pos hsd, abs_of_pos hq0]; ring
  rw [hteq]
  set K := 1 + (|2 * s * a| + |D|) / (r - s)
  have hK : ε * K * ε⁻¹ = K := by field_simp
  have : (ε * K + 1) * ε⁻¹ * (1 + |a|) ≥ K := by
    have h1 : (ε * K + 1) * ε⁻¹ * (1 + |a|) ≥ (ε * K + 1) * ε⁻¹ := by
      have : 0 ≤ (ε * K + 1) * ε⁻¹ := by
        have : 0 ≤ (|2 * s * a| + |D|) / (r - s) := by
          apply div_nonneg (by positivity); linarith
        positivity
      nlinarith [abs_nonneg a]
    have h2 : (ε * K + 1) * ε⁻¹ = K + ε⁻¹ := by rw [add_mul, hK, one_mul]
    have : 0 < ε⁻¹ := inv_pos.2 hε
    linarith
  linarith
