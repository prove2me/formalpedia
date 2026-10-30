-- Prove2me | solution 1 for ProductMixAuction.Allocate.lemma_11
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-10-29T15:34:50.998996+00:00
-- url     : https://prove2.me/submissions/0bfd85ef-1894-4da7-85b2-edb4bd9e2048

import Mathlib
import Definitions.Def_ProductMixAuction_Allocate_Algorithm

open ProductMixAuction.Allocate

universe u_1

namespace PMAL11

noncomputable def b1 : Bid 1 := ⟨![0, 0], -1⟩
noncomputable def b2 : Bid 1 := ⟨![0, 1], 1⟩

lemma sm_eq (b : Bid 1) (q : Fin 1 → ℝ) : surplusMax b q = max (b.v 0) (b.v 1 - q 0) := by
  unfold surplusMax
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    fin_cases i
    · simp [ext]
    · simp [ext]
  · apply max_le
    · have := Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ (0 : Fin 2))
      simpa [ext] using this
    · have := Finset.le_sup' (fun i => b.v i - ext q i) (Finset.mem_univ (1 : Fin 2))
      simpa [ext] using this

lemma dg_zero (b : Bid 1) (q : Fin 1 → ℝ) (h : b.v 1 - q 0 < b.v 0) :
    demGoods b q = {0} := by
  have hs : surplusMax b q = b.v 0 := by rw [sm_eq]; exact max_eq_left h.le
  ext i
  fin_cases i
  · simp [demGoods, hs, ext]
  · simp [demGoods, hs, ext]; exact h.ne

lemma dg_both (b : Bid 1) (q : Fin 1 → ℝ) (h : b.v 1 - q 0 = b.v 0) :
    demGoods b q = Finset.univ := by
  have hs : surplusMax b q = b.v 0 := by rw [sm_eq]; exact max_eq_left h.le
  ext i
  fin_cases i
  · simp [demGoods, hs, ext]
  · simp [demGoods, hs, ext, h]

noncomputable def A : AllocProblem 1 PUnit.{u_1 + 1} where
  p := fun _ => 1
  B := fun _ => [b1, b2]
  m := 0
  r := 0

lemma fB_eq (q : Fin 1 → ℝ) (hq : 0 < q 0) : fB [b1, b2] q = max 0 (1 - q 0) := by
  simp only [fB, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sm_eq]
  simp [b1, b2]
  linarith

lemma A_alloc : IsAllocProblem A.{u_1} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j b hb
    simp only [A, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · refine ⟨by simp [b1], fun i => ⟨0, Or.inl ?_⟩⟩
      fin_cases i; simp [b1]
    · refine ⟨by simp [b2], fun i => ⟨1, Or.inl ?_⟩⟩
      fin_cases i; simp [b2]
  · intro j
    refine ⟨1 / 2, by norm_num, ?_⟩
    have hconv : ConvexOn ℝ (Metric.ball ((A.{u_1}).p) (1 / 2)) (fun q : Fin 1 → ℝ => max 0 (1 - q 0)) := by
      refine ⟨convex_ball _ _, fun x _ y _ a b ha hb hab => ?_⟩
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply max_le
      · positivity
      · have h1 : a * (1 - x 0) ≤ a * max 0 (1 - x 0) := mul_le_mul_of_nonneg_left (le_max_right _ _) ha
        have h2 : b * (1 - y 0) ≤ b * max 0 (1 - y 0) := mul_le_mul_of_nonneg_left (le_max_right _ _) hb
        nlinarith
    refine hconv.congr ?_
    intro q hq
    have hq0 : 0 < q 0 := by
      have := (Metric.mem_ball.mp hq)
      have h0 : dist (q 0) ((A.{u_1}).p 0) < 1 / 2 := lt_of_le_of_lt (dist_le_pi_dist q _ 0) this
      simp only [A, Real.dist_eq] at h0
      have := abs_lt.mp h0
      linarith
    exact (fB_eq q hq0).symm
  · intro j k; simp [A]
  · intro k; simp [A]
  · refine ⟨0, 0, ?_, by simp [A], fun j => by simp [A]⟩
    intro j
    unfold demand
    apply subset_convexHull
    refine ⟨0, ?_, by funext k; simp⟩
    intro δ hδ
    set e := min (δ / 2) (1 / 2) with he
    have he0 : 0 < e := by positivity
    have heδ : e < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have he1 : e ≤ 1 / 2 := min_le_right _ _
    refine ⟨fun _ => 1 + e, ?_, ?_, ?_⟩
    · rw [dist_pi_lt_iff hδ]
      intro i
      simp [A, Real.dist_eq, abs_of_pos he0, heδ]
    · intro b hb
      simp only [A, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · rw [dg_zero _ _ (by simp [b1]; linarith)]; rfl
      · rw [dg_zero _ _ (by simp [b2]; linarith)]; rfl
    · simp only [A, nmBundle, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      rw [dg_zero b1 _ (by simp [b1]; linarith), dg_zero b2 _ (by simp [b2]; linarith)]
      funext k
      simp [b1, b2]

lemma b1_nm : ¬ IsMarginalBid b1 (fun _ => (1 : ℝ)) := by
  unfold IsMarginalBid
  rw [dg_zero _ _ (by simp [b1])]
  simp

lemma b2_m : IsMarginalBid b2 (fun _ => (1 : ℝ)) := by
  unfold IsMarginalBid
  rw [dg_both _ _ (by simp [b2])]
  simp

lemma nm_m_neg : (nonMarginals A.{u_1}).m PUnit.unit 0 = -1 := by
  classical
  simp only [nonMarginals]
  have : ((A.{u_1}).B PUnit.unit).filter (fun b => ¬ IsMarginalBid b (A.{u_1}).p) = [b1] := by
    simp [A, b1_nm, b2_m]
  rw [this]
  have hd : demGoods b1 (A.{u_1}).p = {0} := dg_zero _ _ (by simp [b1, A])
  simp only [nmBundle, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hd,
    Finset.sum_singleton, add_zero]
  simp [A, b1]

end PMAL11

open PMAL11 in
theorem solution : ¬ (∀ {n : ℕ} {J : Type} [Fintype J] [DecidableEq J] (A : AllocProblem n J),
    IsAllocProblem A → IsReduction (nonMarginals A) A ∧ edges (nonMarginals A) = edges A) := by
  intro h
  have := ((h PMAL11.A.{0} A_alloc).1.1.2.2.1) PUnit.unit 0
  rw [nm_m_neg] at this
  norm_num at this
