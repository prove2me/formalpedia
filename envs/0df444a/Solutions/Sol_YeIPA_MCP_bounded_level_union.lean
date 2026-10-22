-- Prove2me | solution 1 for YeIPA.MCP.bounded_level_union
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T19:34:38.852688+00:00
-- url     : https://prove2.me/submissions/69f90b26-25e6-4b98-b8e4-4f89fca23598

import Mathlib
import Definitions.Def_YeIPA_MCP_HomogeneousModel

open Matrix
open YeIPA.MCP

lemma g72wyb_exists_lb {n : ℕ} (g : Fin n → ℝ) (hg : ∀ i, 0 < g i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε ≤ g i := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
    exact ⟨g j, hg j, fun i => hj i (Finset.mem_univ i)⟩

lemma g72wyb_term (a b θ θ₀ θ₁ x x0 x1 s s0 s1 r : ℝ) (hb : b = 1 - a)
    (hθ : θ = a * θ₀ + b * θ₁) :
    a * ((x - x0) * ((s - θ * r) - (s0 - θ₀ * r))) + b * ((x - x1) * ((s - θ * r) - (s1 - θ₁ * r)))
      = x * s - (x * (a * s0 + b * s1) + (a * x0 + b * x1) * s) + (a * (x0 * s0) + b * (x1 * s1))
        - a * b * (θ₁ - θ₀) * ((x1 - x0) * r) := by
  subst hb hθ; ring

/-- Lemma 8.21 (Ye 1997, p. 258). Let `f` be continuous and monotone on `ℝⁿ₊₊` (standing
assumption of §8.4.1, p. 257), `r ∈ ℝⁿ` and `θ⁰ ≤ θ¹`, and assume `S₊₊(θ⁰r) ≠ ∅` and
`S₊₊(θ¹r) ≠ ∅`. Then for every `δ > 0` the union over `θ ∈ [θ⁰, θ¹]` of
`C₊₊(θr, δ) = {(x, y) ∈ S₊₊(θr) : xᵀy ≤ δ}` is bounded. -/
theorem solution {n : ℕ} (f : (Fin n → ℝ) → (Fin n → ℝ))
    (hf_cont : ContinuousOn f (posOrthant n)) (hf_mono : MonotoneOnPos f)
    (r : Fin n → ℝ) (θ₀ θ₁ : ℝ) (hθ : θ₀ ≤ θ₁)
    (h₀ : (Spp f (θ₀ • r)).Nonempty) (h₁ : (Spp f (θ₁ • r)).Nonempty) :
    ∀ δ : ℝ, 0 < δ → Bornology.IsBounded (⋃ θ ∈ Set.Icc θ₀ θ₁, Cpp f (θ • r) δ) := by
  intro δ hδ
  obtain ⟨⟨x0, s0⟩, hx0, hs0, hfs0⟩ := h₀
  obtain ⟨⟨x1, s1⟩, hx1, hs1, hfs1⟩ := h₁
  simp only at hx0 hs0 hfs0 hx1 hs1 hfs1
  obtain ⟨ε, hε, hεi⟩ := g72wyb_exists_lb (fun i => min (min (x0 i) (x1 i)) (min (s0 i) (s1 i)))
    (fun i => lt_min (lt_min (hx0 i) (hx1 i)) (lt_min (hs0 i) (hs1 i)))
  set K := |θ₁ - θ₀| * |∑ i, (x1 i - x0 i) * r i| with hK
  set M := δ + |∑ i, x0 i * s0 i| + |∑ i, x1 i * s1 i| + K with hM
  have hK0 : 0 ≤ K := by positivity
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨M / ε, ?_⟩
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨θ, hθI, ⟨hpx, hps, hpf⟩, hpd⟩ := hp
  obtain ⟨x, s⟩ := p
  simp only at hpx hps hpf hpd
  rw [← segment_eq_Icc hθ] at hθI
  obtain ⟨a, b, ha, hb, hab, hθe⟩ := hθI
  simp only [smul_eq_mul] at hθe
  have hb' : b = 1 - a := by linarith
  have hfx : ∀ i, f x i = s i - θ * r i := by
    intro i; rw [hpf]; simp [Pi.add_apply, Pi.smul_apply]
  have hfx0 : ∀ i, f x0 i = s0 i - θ₀ * r i := by
    intro i; rw [hfs0]; simp [Pi.add_apply, Pi.smul_apply]
  have hfx1 : ∀ i, f x1 i = s1 i - θ₁ * r i := by
    intro i; rw [hfs1]; simp [Pi.add_apply, Pi.smul_apply]
  have m0 := hf_mono x hpx x0 hx0
  have m1 := hf_mono x hpx x1 hx1
  simp only [dotProduct, Pi.sub_apply, hfx, hfx0, hfx1] at m0 m1
  have hsum : 0 ≤ a * ∑ i, (x i - x0 i) * ((s i - θ * r i) - (s0 i - θ₀ * r i))
      + b * ∑ i, (x i - x1 i) * ((s i - θ * r i) - (s1 i - θ₁ * r i)) := by
    have := mul_nonneg ha m0
    have := mul_nonneg hb m1
    linarith
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib] at hsum
  simp_rw [g72wyb_term a b θ θ₀ θ₁ _ _ _ _ _ _ _ hb' hθe.symm] at hsum
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hxs : ∑ i, x i * s i ≤ δ := by simpa [dotProduct] using hpd
  have hab1 : 0 ≤ a * b ∧ a * b ≤ 1 := by
    constructor
    · positivity
    · nlinarith
  have hKb : a * b * (θ₁ - θ₀) * ∑ i, (x1 i - x0 i) * r i ≥ -K := by
    have h1 : |a * b * (θ₁ - θ₀) * ∑ i, (x1 i - x0 i) * r i| ≤ K := by
      rw [abs_mul, abs_mul, abs_of_nonneg hab1.1, hK]
      have := mul_le_mul_of_nonneg_right hab1.2
        (mul_nonneg (abs_nonneg (θ₁ - θ₀)) (abs_nonneg (∑ i, (x1 i - x0 i) * r i)))
      nlinarith
    linarith [neg_abs_le (a * b * (θ₁ - θ₀) * ∑ i, (x1 i - x0 i) * r i)]
  have ht0 : a * ∑ i, x0 i * s0 i ≤ |∑ i, x0 i * s0 i| := by
    have h := le_abs_self (∑ i, x0 i * s0 i)
    have h2 : 0 ≤ |∑ i, x0 i * s0 i| := abs_nonneg _
    have ha1 : a ≤ 1 := by linarith
    rcases le_or_gt 0 (∑ i, x0 i * s0 i) with hh | hh
    · nlinarith
    · nlinarith
  have ht1 : b * ∑ i, x1 i * s1 i ≤ |∑ i, x1 i * s1 i| := by
    have h := le_abs_self (∑ i, x1 i * s1 i)
    have h2 : 0 ≤ |∑ i, x1 i * s1 i| := abs_nonneg _
    have hb1 : b ≤ 1 := by linarith
    rcases le_or_gt 0 (∑ i, x1 i * s1 i) with hh | hh
    · nlinarith
    · nlinarith
  have hmain : ∑ i, (x i * (a * s0 i + b * s1 i) + (a * x0 i + b * x1 i) * s i) ≤ M := by
    rw [hM, Finset.sum_add_distrib]; linarith
  have hlb : ∀ i, ε ≤ a * s0 i + b * s1 i ∧ ε ≤ a * x0 i + b * x1 i := by
    intro i
    have h := hεi i
    simp only [le_min_iff] at h
    constructor <;> nlinarith [h.1.1, h.1.2, h.2.1, h.2.2]
  have hnn : ∀ i, 0 ≤ x i * (a * s0 i + b * s1 i) + (a * x0 i + b * x1 i) * s i := by
    intro i
    have := hlb i
    have := hpx i; have := hps i
    have h1 : 0 ≤ x i * (a * s0 i + b * s1 i) := mul_nonneg (hpx i).le (by linarith)
    have h2 : 0 ≤ (a * x0 i + b * x1 i) * s i := mul_nonneg (by linarith) (hps i).le
    linarith
  have hcomp : ∀ i, ε * x i ≤ M ∧ ε * s i ≤ M := by
    intro i
    have hle := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    have h1 : ε * x i ≤ x i * (a * s0 i + b * s1 i) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hlb i).1 (hpx i).le
    have h2 : ε * s i ≤ (a * x0 i + b * x1 i) * s i :=
      mul_le_mul_of_nonneg_right (hlb i).2 (hps i).le
    have h3 : 0 ≤ x i * (a * s0 i + b * s1 i) := le_trans (by have := hpx i; positivity) h1
    have h4 : 0 ≤ (a * x0 i + b * x1 i) * s i := le_trans (by have := hps i; positivity) h2
    constructor <;> linarith
  have hM0 : 0 ≤ M / ε := by
    rw [hM]; positivity
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg hM0).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_of_pos (hpx i), le_div_iff₀ hε, mul_comm]
    exact (hcomp i).1
  · refine (pi_norm_le_iff_of_nonneg hM0).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_of_pos (hps i), le_div_iff₀ hε, mul_comm]
    exact (hcomp i).2
