-- Prove2me | solution 1 for ProductMixAuction.Allocate.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:45:10.841361+00:00
-- url     : https://prove2.me/submissions/26d30d27-6ea5-4e52-9370-c61ccc9c27b8

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Setting

open ProductMixAuction.Allocate

namespace PMAL9

variable {n : ℕ}

lemma le_sM (b : Bid n) (q : Fin n → ℝ) (m : Fin (n + 1)) :
    b.v m - ext q m ≤ surplusMax b q :=
  Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ m)

lemma dG_val (b : Bid n) (q : Fin n → ℝ) (g : Fin (n + 1)) (hg : g ∈ demGoods b q) :
    b.v g - ext q g = surplusMax b q := by
  simpa [demGoods] using hg

lemma dG_ne (b : Bid n) (q : Fin n → ℝ) : (demGoods b q).Nonempty := by
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (n + 1)))
    (fun i => b.v i - ext q i)
  exact ⟨m, by simp only [demGoods, Finset.mem_filter, Finset.mem_univ, true_and]; exact hm.symm⟩

lemma ext_line (p q : Fin n → ℝ) (θ : ℝ) (m : Fin (n + 1)) :
    ext (p + θ • (q - p)) m = (1 - θ) * ext p m + θ * ext q m := by
  cases m using Fin.cases <;> simp [ext] ; ring

lemma ext_close (p q : Fin n → ℝ) (r : ℝ) (hq : q ∈ Metric.ball p r) (m : Fin (n + 1)) :
    |ext q m - ext p m| < r := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hq
  cases m using Fin.cases with
  | zero => simpa [ext] using hr
  | succ i =>
    have := lt_of_le_of_lt (dist_le_pi_dist q p i) hq
    simpa [ext, Real.dist_eq] using this

/-- Observation 7: goods demanded near `p` are demanded at `p`. -/
lemma obs7 (b : Bid n) (p q : Fin n → ℝ) (ε : ℝ)
    (hgap : ∀ k ∉ demGoods b p, b.v k - ext p k ≤ surplusMax b p - ε)
    (hq : q ∈ Metric.ball p (ε / 2)) : demGoods b q ⊆ demGoods b p := by
  intro i hi
  by_contra hip
  obtain ⟨g, hg⟩ := dG_ne b p
  have h1 := hgap i hip
  have h2 := dG_val b q i hi
  have h3 := le_sM b q g
  have h4 := dG_val b p g hg
  have c1 := abs_lt.mp (ext_close p q _ hq i)
  have c2 := abs_lt.mp (ext_close p q _ hq g)
  linarith [c1.1, c1.2, c2.1, c2.2]

lemma sM_line (b : Bid n) (p q : Fin n → ℝ) (ε : ℝ)
    (hgap : ∀ k ∉ demGoods b p, b.v k - ext p k ≤ surplusMax b p - ε)
    (hq : q ∈ Metric.ball p (ε / 2)) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    surplusMax b (p + θ • (q - p)) = (1 - θ) * surplusMax b p + θ * surplusMax b q := by
  obtain ⟨i, hi⟩ := dG_ne b q
  have hip := obs7 b p q ε hgap hq hi
  apply le_antisymm
  · apply Finset.sup'_le
    intro m _
    rw [ext_line]
    have := le_sM b p m
    have := le_sM b q m
    nlinarith
  · have := le_sM b (p + θ • (q - p)) i
    rw [ext_line] at this
    have e1 := dG_val b p i hip
    have e2 := dG_val b q i hi
    nlinarith

lemma fB_line (B : List (Bid n)) (p q : Fin n → ℝ) (ε : ℝ)
    (hgap : ∀ b ∈ B, ∀ k ∉ demGoods b p, b.v k - ext p k ≤ surplusMax b p - ε)
    (hq : q ∈ Metric.ball p (ε / 2)) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    fB B (p + θ • (q - p)) = (1 - θ) * fB B p + θ * fB B q := by
  induction B with
  | nil => simp [fB]
  | cons b L ih =>
    have ih' := ih (fun b' hb' => hgap b' (List.mem_cons_of_mem _ hb'))
    simp only [fB, List.map_cons, List.sum_cons] at ih' ⊢
    rw [ih', sM_line b p q ε (hgap b List.mem_cons_self) hq θ hθ0 hθ1]
    ring

end PMAL9

open PMAL9 in
theorem solution {n : ℕ} (B : List (Bid n)) (p : Fin n → ℝ) (δ ε : ℝ) (hδ : 0 < δ)
    (hB : EpsValid B p δ)
    (hgap : ∀ b ∈ B, ∀ k ∉ demGoods b p, b.v k - ext p k ≤ surplusMax b p - ε) :
    EpsValid B p (ε / 2) := by
  unfold EpsValid at hB ⊢
  rcases le_or_gt ε 0 with hε | hε
  · rw [Metric.ball_eq_empty.mpr (by linarith)]
    exact ⟨convex_empty, fun x hx => absurd hx (Set.notMem_empty x)⟩
  refine ⟨convex_ball _ _, fun x hx y hy a b ha hb hab => ?_⟩
  set θ : ℝ := min 1 (δ / ε) with hθ
  have hθ0 : 0 < θ := lt_min one_pos (div_pos hδ hε)
  have hθ1 : θ ≤ 1 := min_le_left _ _
  have hθε : θ * (ε / 2) < δ := by
    have : θ ≤ δ / ε := min_le_right _ _
    have h2 : θ * ε ≤ δ := by rwa [le_div_iff₀ hε] at this
    nlinarith
  have hz : a • x + b • y ∈ Metric.ball p (ε / 2) := (convex_ball p (ε / 2)) hx hy ha hb hab
  have inball : ∀ w ∈ Metric.ball p (ε / 2), p + θ • (w - p) ∈ Metric.ball p δ := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw ⊢
    have : p + θ • (w - p) - p = θ • (w - p) := by abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hθ0]
    calc θ * ‖w - p‖ ≤ θ * (ε / 2) := by nlinarith [norm_nonneg (w - p)]
      _ < δ := hθε
  have key := hB.2 (inball x hx) (inball y hy) ha hb hab
  have e : a • (p + θ • (x - p)) + b • (p + θ • (y - p)) = p + θ • ((a • x + b • y) - p) := by
    funext m; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    linear_combination (p m - θ * p m) * hab
  rw [e, fB_line B p _ ε hgap hz θ hθ0.le hθ1, fB_line B p _ ε hgap hx θ hθ0.le hθ1,
    fB_line B p _ ε hgap hy θ hθ0.le hθ1] at key
  simp only [smul_eq_mul] at key ⊢
  have e2 : a * ((1 - θ) * fB B p + θ * fB B x) + b * ((1 - θ) * fB B p + θ * fB B y) =
      (1 - θ) * fB B p + θ * (a * fB B x + b * fB B y) := by
    linear_combination ((1 - θ) * fB B p) * hab
  have : θ * fB B (a • x + b • y) ≤ θ * (a * fB B x + b * fB B y) := by
    linarith
  exact le_of_mul_le_mul_left this hθ0
