-- Prove2me | solution 1 for PrimalDualSubgrad.DA.eq_2_18
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:57:11.068196+00:00
-- url     : https://prove2.me/submissions/c85f08d1-c0fa-43fc-b7b8-71ee7fc4ded0

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_DualAveraging
open PrimalDualSubgrad.DA Filter Asymptotics
open scoped Topology
private theorem growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : Set E} {d : E → ℝ} {σ : ℝ} (hsc : StrongConvexOn Q σ d)
    {xs x : E} (hs : xs ∈ Q) (hx : x ∈ Q)
    (hm : ∀ y ∈ Q, d xs ≤ d y) :
    d xs + σ / 2 * ‖x - xs‖ ^ 2 ≤ d x := by
  have hb : 0 ≤ d x - d xs := sub_nonneg.mpr (hm x hx)
  by_contra h
  let A := σ / 2 * ‖x - xs‖ ^ 2
  let B := d x - d xs
  have hBA : B < A := by dsimp [A, B]; linarith
  have hB : 0 ≤ B := hb
  have hA : 0 < A := lt_of_le_of_lt hB hBA
  let t := (A - B) / (2 * A)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by dsimp [t]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  have hteq : t * (2 * A) = A - B := by dsimp [t]; field_simp
  have hc := hsc.2 hs hx (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  have hmem := hsc.1 hs hx (sub_nonneg.mpr ht1) ht.le (by ring : 1 - t + t = 1)
  have hmin := hm _ hmem
  simp only [smul_eq_mul, norm_sub_rev xs x] at hc
  have hc' : 0 ≤ t * (B - (1 - t) * A) := by dsimp [A, B]; nlinarith [hc]
  have hb' : (1 - t) * A ≤ B := by nlinarith
  nlinarith

private lemma attained {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s : StrongDual ℝ E) :
    V P β s = s (π β s-P.x0)-β*P.d (π β s) := by
  apply IsGreatest.csSup_eq
  refine ⟨⟨π β s, (hπ β hβ s).1, rfl⟩, ?_⟩
  rintro _ ⟨x,hx,rfl⟩
  have hh := (hπ β hβ s).2 x hx
  simp only [map_sub]
  linarith

private lemma value_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s : StrongDual ℝ E) (x : E) (hx : x ∈ P.Q) :
    s (x-P.x0)-β*P.d x ≤ V P β s := by
  rw [attained P π hπ β hβ s]
  have hh := (hπ β hβ s).2 x hx
  simp only [map_sub]
  linarith

private lemma prox_growth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s : StrongDual ℝ E) (x : E) (hx : x ∈ P.Q) :
    -s (π β s)+β*P.d (π β s)+β*P.σ/2*‖x-π β s‖^2 ≤ -s x+β*P.d x := by
  have hs : StrongConvexOn P.Q (β*P.σ) (fun x => -s x+β*P.d x) := by
    refine ⟨P.convex_Q, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := mul_le_mul_of_nonneg_left (P.strongConvexOn_d.2 hx hy ha hb hab) hβ.le
    simp only [map_add, map_smul, smul_eq_mul] at hh ⊢
    nlinarith
  exact growth hs (hπ β hβ s).1 hx (hπ β hβ s).2


set_option autoImplicit false
open Finset

private lemma smooth_upper {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) (s t : StrongDual ℝ E) :
    V P β (s+t) ≤ V P β s+t (π β s-P.x0)+‖t‖^2/(2*β*P.σ) := by
  have hg := prox_growth P π hπ β hβ s (π β (s+t)) (hπ β hβ (s+t)).1
  have hb := (le_abs_self (t (π β (s+t)-π β s))).trans (t.le_opNorm _)
  have hk : 0 < β*P.σ := mul_pos hβ P.σ_pos
  have hc : 0 ≤ (β*P.σ*‖π β (s+t)-π β s‖-‖t‖)^2 := sq_nonneg _
  have he : ‖t‖^2/(2*β*P.σ)*(2*β*P.σ) = ‖t‖^2 := by
    field_simp [ne_of_gt P.σ_pos]
  rw [attained P π hπ β hβ (s+t), attained P π hπ β hβ s]
  simp only [ContinuousLinearMap.add_apply, map_sub] at *
  nlinarith

private lemma beta_decrease {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β β' : ℝ) (hb : 0 < β) (hbb : β ≤ β') (s : StrongDual ℝ E) :
    V P β' s ≤ V P β s := by
  have hb' : 0 < β' := lt_of_lt_of_le hb hbb
  have hx := (hπ β' hb' s).1
  have hd : 0 ≤ P.d (π β' s) := by
    have := P.x0_isMin _ hx
    simpa [P.d_x0] using this
  have hh := value_le P π hπ β hb s (π β' s) hx
  rw [attained P π hπ β' hb' s]
  nlinarith

private lemma beta_pos {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E)
    (lam β : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E)
    (hrun : IsDARun P π lam β g x) (k : ℕ) : 0 < β k := by
  induction k with
  | zero => exact hrun.1
  | succ k ih => exact lt_of_lt_of_le ih (hrun.2.1 k)

private lemma one_step {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (lam β : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E)
    (hrun : IsDARun P π lam β g x) (i : ℕ) (hi : 1 ≤ i) :
    lam i*g i (x i-P.x0) ≤ V P (β i) (-(sAgg lam g i)) -
      V P (β (i+1)) (-(sAgg lam g (i+1))) +
      1/(2*P.σ)*(lam i^2/β i*‖g i‖^2) := by
  have hb := beta_pos P π lam β g x hrun i
  have hh := smooth_upper P π hπ (β i) hb (-(sAgg lam g i)) (-(lam i • g i))
  have hd := beta_decrease P π hπ (β i) (β (i+1)) hb (hrun.2.1 i) (-(sAgg lam g (i+1)))
  have hs : -(sAgg lam g (i+1)) = -(sAgg lam g i)+ -(lam i • g i) := by
    simp [sAgg, sum_range_succ, add_comm]
  have hx : x i = π (β i) (-(sAgg lam g i)) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    exact hrun.2.2.2.2 j
  have hl := hrun.2.2.1 i
  have he : ‖-(lam i • g i)‖^2/(2*β i*P.σ) =
      1/(2*P.σ)*(lam i^2/β i*‖g i‖^2) := by
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hl.le]
    field_simp
    <;> ring
  rw [← hs, ← hx, he] at hh
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at hh
  linarith

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (lam β : ℕ → ℝ) (g : ℕ → StrongDual ℝ E) (x : ℕ → E) (hrun : IsDARun P π lam β g x)
    (k : ℕ) :
    ∑ i ∈ range (k + 1), lam i * g i (x i - P.x0) ≤
      V P (β 1) (-(sAgg lam g 1)) - V P (β (k + 1)) (-(sAgg lam g (k + 1))) +
        1 / (2 * P.σ) * ∑ i ∈ Icc 1 k, lam i ^ 2 / β i * ‖g i‖ ^ 2  := by
  classical
  induction k with
  | zero =>
    simp [hrun.2.2.2.1]
  | succ k ih =>
    have hh := one_step P π hπ lam β g x hrun (k+1) (by omega)
    rw [sum_range_succ]
    have he : Icc 1 (k+1) = insert (k+1) (Icc 1 k) := by
      ext i; simp only [mem_Icc, mem_insert]; omega
    rw [he, sum_insert (by simp)]
    linarith
#print axioms solution
