-- Prove2me | solution 1 for ThomsonKS.Char.sigmaTilde_dense
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T12:38:31.497297+00:00
-- url     : https://prove2.me/submissions/fcaf61df-cf5f-40b1-acbe-58f17926d16a

import Mathlib
import Definitions.Def_ThomsonKS_Char_Setting

open ThomsonKS.Char Filter Topology

namespace KSDense

variable {P : Finset ℕ}

/-- The approximating problem: `x ≥ 0` dominated by some `y ∈ S` in the cone order
`x_i ≤ y_i + ε Σ_j (y_j - x_j)`. -/
def approx (S : Set (P → ℝ)) (ε : ℝ) : Set (P → ℝ) :=
  {x | 0 ≤ x ∧ ∃ y ∈ S, ∀ i, x i ≤ y i + ε * ∑ j, (y j - x j)}

lemma sum_sub_le {x y : P → ℝ} (hx : 0 ≤ x) : ∑ j, (y j - x j) ≤ ∑ j, y j :=
  Finset.sum_le_sum fun j _ => by have := hx j; simp only [Pi.zero_apply] at this; linarith

lemma sum_le_card {S : Set (P → ℝ)} {R : ℝ} (hR : ∀ x ∈ S, ∀ i, x i ≤ R) {y : P → ℝ}
    (hy : y ∈ S) : ∑ j, y j ≤ (Fintype.card P : ℝ) * R := by
  calc ∑ j, y j ≤ ∑ _j : P, R := Finset.sum_le_sum fun j _ => hR y hy j
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]

lemma approx_mem (S : Set (P → ℝ)) (hS : S ∈ DivProb P) {ε : ℝ} (hε : 0 < ε) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x ∈ S, ∀ i, x i ≤ R) : approx S ε ∈ DivProbTilde P := by
  obtain ⟨hP, hnn, hcpt, hcvx, ⟨x0, hx0, hx0p⟩, hcomp⟩ := hS
  set n : ℝ := (Fintype.card P : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  set C : ℝ := R + ε * (n * R)
  -- compactness
  have hcpt' : IsCompact (approx S ε) := by
    set K : Set ((P → ℝ) × (P → ℝ)) :=
      {p | p.2 ∈ S ∧ 0 ≤ p.1 ∧ ∀ i, p.1 i ≤ p.2 i + ε * ∑ j, (p.2 j - p.1 j)} with hK
    have hKeq : K = (Prod.snd ⁻¹' S) ∩ ({p : (P → ℝ) × (P → ℝ) | 0 ≤ p.1} ∩
        ⋂ i, {p : (P → ℝ) × (P → ℝ) | p.1 i ≤ p.2 i + ε * ∑ j, (p.2 j - p.1 j)}) := by
      ext p; simp [hK]
    have hKc : IsClosed K := by
      rw [hKeq]
      refine (hcpt.isClosed.preimage continuous_snd).inter
        ((isClosed_le continuous_const continuous_fst).inter ?_)
      refine isClosed_iInter fun i => isClosed_le ?_ ?_
      · exact (continuous_apply i).comp continuous_fst
      · refine ((continuous_apply i).comp continuous_snd).add (continuous_const.mul ?_)
        exact continuous_finset_sum _ fun j _ =>
          ((continuous_apply j).comp continuous_snd).sub ((continuous_apply j).comp continuous_fst)
    have hKsub : K ⊆ Set.Icc (0 : P → ℝ) (fun _ => C) ×ˢ S := by
      rintro ⟨x, y⟩ ⟨hy, hx0', hxy⟩
      refine ⟨⟨hx0', fun i => ?_⟩, hy⟩
      have h1 := hxy i
      have h2 : ∑ j, (y j - x j) ≤ n * R := (sum_sub_le hx0').trans (sum_le_card hR hy)
      have h3 := hR y hy i
      simp only at h1 ⊢
      nlinarith
    have hKcpt : IsCompact K :=
      (isCompact_Icc.prod hcpt).of_isClosed_subset hKc hKsub
    have : approx S ε = Prod.fst '' K := by
      ext x
      constructor
      · rintro ⟨hx, y, hy, hxy⟩
        exact ⟨(x, y), ⟨hy, hx, hxy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hy, hx, hxy⟩, rfl⟩
        exact ⟨hx, y, hy, hxy⟩
    rw [this]
    exact hKcpt.image continuous_fst
  -- convexity
  have hcvx' : Convex ℝ (approx S ε) := by
    rintro x ⟨hx, y, hy, hxy⟩ x' ⟨hx', y', hy', hxy'⟩ a b ha hb hab
    refine ⟨?_, a • y + b • y', hcvx hy hy' ha hb hab, fun i => ?_⟩
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have := hx i; have := hx' i
      simp only [Pi.zero_apply] at *
      positivity
    · have hsum : ∑ j, ((a • y + b • y') j - (a • x + b • x') j) =
          a * ∑ j, (y j - x j) + b * ∑ j, (y' j - x' j) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
      rw [hsum]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left (hxy i) ha
      have h2 := mul_le_mul_of_nonneg_left (hxy' i) hb
      nlinarith
  refine ⟨⟨hP, fun x hx i => hx.1 i, hcpt', hcvx', ⟨x0, ⟨fun i => (hx0p i).le, x0, hx0,
    fun i => by simp⟩, hx0p⟩, ?_⟩, ?_⟩
  -- comprehensive
  · rintro x ⟨hx, y, hy, hxy⟩ x' hx' hx'x
    refine ⟨hx', y, hy, fun i => ?_⟩
    have h1 : ∑ j, (y j - x j) ≤ ∑ j, (y j - x' j) :=
      Finset.sum_le_sum fun j _ => by linarith [hx'x j]
    have := hxy i
    have := hx'x i
    nlinarith
  -- condition (c)
  · rintro x ⟨hx, -, -, -⟩ x' ⟨hx', y, hy, hxy⟩ ⟨hle, hne⟩
    set D := ∑ j, (x' j - x j) with hD
    have hDpos : 0 < D := by
      obtain ⟨j, hj⟩ : ∃ j, x j ≠ x' j := by
        by_contra h; push Not at h; exact hne (funext h)
      apply Finset.sum_pos' (fun j _ => by linarith [hle j])
      exact ⟨j, Finset.mem_univ _, by linarith [lt_of_le_of_ne (hle j) hj]⟩
    have hsplit : ∑ j, (y j - x j) = ∑ j, (y j - x' j) + D := by
      rw [hD, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    set η := ε * D / (1 + ε * n) with hη
    have hden : 0 < 1 + ε * n := by positivity
    have hηpos : 0 < η := by positivity
    have hη' : η * (1 + ε * n) = ε * D := by rw [hη]; field_simp
    refine ⟨fun i => x i + η, ⟨fun i => by have := hx i; simp only [Pi.zero_apply] at this ⊢; linarith, y, hy,
      fun i => ?_⟩, fun i => by simp only; linarith⟩
    have hsum2 : ∑ j, (y j - (x j + η)) = ∑ j, (y j - x j) - n * η := by
      rw [show (fun j => y j - (x j + η)) = fun j => (y j - x j) - η from funext fun j => by ring]
      rw [Finset.sum_sub_distrib]
      simp [Finset.sum_const, Finset.card_univ, n]
    rw [hsum2, hsplit]
    have h1 := hxy i
    have h2 := hle i
    nlinarith

lemma approx_hd (S : Set (P → ℝ)) (hS : S ∈ DivProb P) {ε : ℝ} (hε : 0 < ε) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x ∈ S, ∀ i, x i ≤ R) :
    Metric.hausdorffEDist (approx S ε) S ≤
      ENNReal.ofReal (ε * ((Fintype.card P : ℝ) * R)) := by
  have hnn := hS.2.1
  have hcomp := hS.2.2.2.2.2
  apply Metric.hausdorffEDist_le_of_mem_edist
  · rintro x ⟨hx, y, hy, hxy⟩
    refine ⟨fun i => min (x i) (y i), hcomp y hy _ (fun i => le_min (hx i) (hnn y hy i))
      (fun i => min_le_right _ _), ?_⟩
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    have hsum : ∑ j, (y j - x j) ≤ (Fintype.card P : ℝ) * R :=
      (sum_sub_le hx).trans (sum_le_card hR hy)
    apply dist_pi_le_iff (by positivity) |>.mpr
    intro i
    rw [Real.dist_eq]
    have h1 := hxy i
    rcases le_total (x i) (y i) with h | h
    · rw [min_eq_left h, sub_self, abs_zero]; positivity
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      nlinarith
  · intro y hy
    refine ⟨y, ⟨fun i => hnn y hy i, y, hy, fun i => by simp⟩, ?_⟩
    simp

end KSDense

open KSDense

theorem solution : ∀ P : Finset ℕ, ∀ S ∈ DivProb P, ∃ Sk : ℕ → Set (P → ℝ),
    (∀ k, Sk k ∈ DivProbTilde P) ∧
      Tendsto (fun k => Metric.hausdorffEDist (Sk k) S) atTop (𝓝 0) := by
  intro P S hS
  obtain ⟨R₁, hR₁⟩ := hS.2.2.1.isBounded.exists_norm_le
  set R := max R₁ 0
  have hR0 : 0 ≤ R := le_max_right _ _
  have hR : ∀ x ∈ S, ∀ i, x i ≤ R := fun x hx i =>
    ((le_abs_self _).trans ((norm_le_pi_norm x i).trans (hR₁ x hx))).trans (le_max_left _ _)
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  refine ⟨fun k => approx S (ε k), fun k => approx_mem S hS (hε k) hR0 hR, ?_⟩
  set C : ℝ := (Fintype.card P : ℝ) * R
  have hlim : Tendsto (fun k => ENNReal.ofReal (ε k * C)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const C
    simp only [zero_mul] at this
    exact this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun k => approx_hd S hS (hε k) hR0 hR)
