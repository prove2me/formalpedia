-- Prove2me | solution 2 for SparseNLO.CWOpt.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T11:56:55.409423+00:00
-- url     : https://prove2.me/submissions/63976020-27a9-4199-8c84-93ad9cda6966

import Mathlib
import Definitions.Def_SparseNLO_CWOpt_Setting
import Theorems.Thm_SparseNLO_CWOpt_lemma_2_5
import Theorems.Thm_SparseNLO_CWOpt_eq_2_18

-- carved verbatim out of submission bdd7aba3-65fe-4f80-aff4-802dbd48dbe8, lines 269-316

section
open SparseNLO.CWOpt
open scoped RealInnerProductSpace

private lemma local_nonneg {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hL : LocalLipschitz f L) (i j : Fin n) (hij : i ≠ j) : 0 ≤ L := by
  have hh := hL i j hij 0 (EuclideanSpace.single i 1) (by
    intro k hki hkj
    simp [PiLp.single_apply, hki])
  simp only [PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one] at hh
  exact (Real.sqrt_nonneg _).trans hh

private lemma getD_nonneg (l : List ℝ) (h : ∀ a ∈ l, 0 ≤ a) (k : ℕ) :
    0 ≤ l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simpa using h a (by simp)
    | succ k => simpa using ih (fun a ha => h a (by simp [ha])) k

private lemma getD_mem_or_zero (l : List ℝ) (k : ℕ) :
    l.getD k 0 ∈ l ∨ l.getD k 0 = 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      simpa only [List.getD_cons_succ, List.mem_cons] using
        (ih k).imp (fun h => Or.inr h) id

private lemma sorted_getD_pos (l : List ℝ) (hsort : l.Pairwise (fun a b => b ≤ a))
    (k : ℕ) (hk : k < l.countP (fun a => decide (0 < a))) : 0 < l.getD k 0 := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    rcases List.pairwise_cons.mp hsort with ⟨ha, hl⟩
    cases k with
    | zero =>
      obtain ⟨b, hb, hbp⟩ := List.countP_pos_iff.mp hk
      have hb0 : 0 < b := of_decide_eq_true hbp
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa using hb0
      · simpa using hb0.trans_le (ha b hb)
    | succ k =>
      have hh : k < l.countP (fun a => decide (0 < a)) := by
        rw [List.countP_cons] at hk
        split_ifs at hk <;> omega
      simpa using ih hl k hh

private lemma ms_nonneg {n : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ Ms s x := by
  apply getD_nonneg
  intro a ha
  simp only [Multiset.mem_sort, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at ha
  obtain ⟨i, rfl⟩ := ha
  exact abs_nonneg _

private lemma ms_pos {n s : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hs : 0 < s)
    (hxs : l0 x = s) : 0 < Ms s x := by
  classical
  let l := (Finset.univ.val.map (fun i : Fin n => |x i|)).sort (fun a b : ℝ => b ≤ a)
  have hc : l.countP (fun a => decide (0 < a)) = s := by
    change Multiset.countP (fun a : ℝ => 0 < a)
      (↑((Finset.univ.val.map (fun i : Fin n => |x i|)).sort
        (fun a b : ℝ => b ≤ a)) : Multiset ℝ) = s
    rw [Multiset.sort_eq, Multiset.countP_map]
    simpa only [l0, Finset.card_def, Finset.filter_val, abs_pos] using hxs
  apply sorted_getD_pos l (Multiset.pairwise_sort _ _) (s - 1)
  rw [hc]
  omega

private lemma ms_exists {n s : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hs : 0 < s)
    (hxs : l0 x = s) : ∃ m : Fin n, x m ≠ 0 ∧ |x m| = Ms s x := by
  have hp := ms_pos x hs hxs
  rcases getD_mem_or_zero ((Finset.univ.val.map (fun i : Fin n => |x i|)).sort
      (fun a b : ℝ => b ≤ a)) (s - 1) with h | h
  · simp only [Multiset.mem_sort, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at h
    obtain ⟨m, hm⟩ := h
    refine ⟨m, ?_, hm⟩
    apply abs_pos.mp
    rw [hm]
    exact hp
  · change Ms s x = 0 at h
    linarith

theorem solution {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hcw : IsCWMin f s xstar) :
    (∀ i ∈ I0 xstar, |gradient f xstar i| ≤ L2 * Ms s xstar) ∧
      (∀ i ∈ I1 xstar, gradient f xstar i = 0) := by
  classical
  have hbf := SparseNLO.CWOpt.lemma_2_5 f hf hbdd hs hsn xstar hcw.1 hcw
  have hL0 : 0 ≤ L2 := local_nonneg f L2 hL2
    ⟨0, by omega⟩ ⟨1, by omega⟩ (by intro h; have := congrArg Fin.val h; simp at this)
  rcases hcw.2 with h | h
  · have hg := hbf.2.1 h.1
    constructor
    · intro i hi
      simpa [hg] using mul_nonneg hL0 (ms_nonneg s xstar)
    · intro i hi
      simp [hg]
  · refine ⟨?_, hbf.2.2 h.1⟩
    intro i hi
    obtain ⟨m, hm0, hm⟩ := ms_exists xstar hs h.1
    have hm1 : m ∈ I1 xstar := by simp [I1, hm0]
    let σ : ℝ := SignType.sign (xstar m * gradient f xstar i)
    have hmin := h.2 m hm1 i (-σ * xstar m)
    have heq : xstar - EuclideanSpace.single m (xstar m) +
        EuclideanSpace.single i (-σ * xstar m) =
      xstar - EuclideanSpace.single m (xstar m) - EuclideanSpace.single i (σ * xstar m) := by
      ext k
      simp [PiLp.single_apply]
      split_ifs <;> ring
    rw [heq] at hmin
    have hh := SparseNLO.CWOpt.eq_2_18 f hf hbdd hs hsn Lf hLf L2 hL2 xstar hcw h.1 i hi m hm
    change f (xstar - EuclideanSpace.single m (xstar m) - EuclideanSpace.single i (σ * xstar m))
      ≤ f xstar - σ * xstar m * gradient f xstar i + L2 * xstar m ^ 2 at hh
    have hsign : σ * xstar m * gradient f xstar i = |xstar m| * |gradient f xstar i| := by
      calc
        σ * xstar m * gradient f xstar i = σ * (xstar m * gradient f xstar i) := by ring
        _ = |xstar m * gradient f xstar i| := sign_mul_self _
        _ = |xstar m| * |gradient f xstar i| := abs_mul _ _
    rw [hsign] at hh
    have hab : 0 < |xstar m| := abs_pos.mpr hm0
    rw [← hm]
    apply (mul_le_mul_iff_right₀ hab).mp
    have hsq : xstar m ^ 2 = |xstar m| * |xstar m| := by rw [← sq, sq_abs]
    rw [hsq] at hh
    nlinarith

end
