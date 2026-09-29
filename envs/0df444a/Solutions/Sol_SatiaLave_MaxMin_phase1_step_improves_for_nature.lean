-- Prove2me | solution 1 for SatiaLave.MaxMin.phase1_step_improves_for_nature
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:55:53.123275+00:00
-- url     : https://prove2.me/submissions/8d58300f-0425-43ea-9b72-b33145ebd972

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- maximum-principle lemma: if `x = e + β T x` with `T` stochastic, `0 ≤ β < 1` and `e ≤ 0`,
then `x ≤ 0`. -/
theorem aux_p1sn_le {S : Type*} [Fintype S] (T : S → S → ℝ) (hT0 : ∀ i j, 0 ≤ T i j)
    (hT1 : ∀ i, ∑ j, T i j = 1) (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (x e : S → ℝ)
    (he : ∀ i, e i ≤ 0) (hx : ∀ i, x i = e i + β * ∑ j, T i j * x j) : ∀ i, x i ≤ 0 := by
  intro i
  have hne : (Finset.univ : Finset S).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ x hne
  have hs : ∑ j, T i0 j * x j ≤ x i0 := by
    calc ∑ j, T i0 j * x j ≤ ∑ j, T i0 j * x i0 :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hi0 j (Finset.mem_univ _)) (hT0 i0 j)
      _ = x i0 := by rw [← Finset.sum_mul, hT1 i0, one_mul]
  have h1 := hx i0
  have h2 := he i0
  have h3 : β * ∑ j, T i0 j * x j ≤ β * x i0 := mul_le_mul_of_nonneg_left hs hβ0
  have hm : x i0 ≤ 0 := by nlinarith
  exact le_trans (hi0 i (Finset.mem_univ _)) hm

theorem aux_p1sn_row {S : Type*} [Fintype S] {D : S → Type*} (M : UncertainMDP S D)
    (P : Sel M) (i : S) (k : D i) : (∀ j, 0 ≤ P.1 i k j) ∧ ∑ j, P.1 i k j = 1 :=
  M.U_subset i k (P.2 i k)

theorem aux_p1sn_eq {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    ∀ i, presentValue M A P i =
      rewardVec M A P i + M.β * ∑ j, P.1 i (A i) j * presentValue M A P j := by
  set N : Matrix S S ℝ := 1 - M.β • transMat M A P with hN
  have hmul : ∀ x : S → ℝ, ∀ i, (Matrix.mulVec N x) i = x i - M.β * ∑ j, P.1 i (A i) j * x j := by
    intro x i
    simp [hN, Matrix.mulVec, dotProduct, transMat, Finset.mul_sum, sub_mul,
      Finset.sum_sub_distrib, Matrix.one_apply, mul_assoc]
  have hdet : N.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hfix : ∀ i, x i = 0 + M.β * ∑ j, P.1 i (A i) j * x j := by
      intro i
      have := congrFun hx i
      rw [hmul] at this
      simp only [Pi.zero_apply] at this
      linarith
    have hle := aux_p1sn_le (fun i j => P.1 i (A i) j) (fun i j => (aux_p1sn_row M P i (A i)).1 j)
      (fun i => (aux_p1sn_row M P i (A i)).2) M.β M.β_nonneg M.β_lt_one x (fun _ => 0)
      (fun _ => le_rfl) hfix
    have hfix' : ∀ i, (-x) i = 0 + M.β * ∑ j, P.1 i (A i) j * (-x) j := by
      intro i
      simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      rw [hfix i]; ring
    have hge := aux_p1sn_le (fun i j => P.1 i (A i) j) (fun i j => (aux_p1sn_row M P i (A i)).1 j)
      (fun i => (aux_p1sn_row M P i (A i)).2) M.β M.β_nonneg M.β_lt_one (-x) (fun _ => 0)
      (fun _ => le_rfl) hfix'
    apply hx0
    funext i
    have a := hle i
    have b := hge i
    simp only [Pi.neg_apply] at b
    simp only [Pi.zero_apply]
    linarith
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hdet
  have hv : Matrix.mulVec N (presentValue M A P) = rewardVec M A P := by
    unfold presentValue
    rw [← hN, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hu, Matrix.one_mulVec]
  intro i
  have := congrFun hv i
  rw [hmul] at this
  linarith

end SatiaLave.MaxMin

open SatiaLave.MaxMin

theorem solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P P' : Sel M)
    (hstep : IsPhase1Step M A P P') (hnot : ¬ Phase1Stops M A P P') :
    (∀ i, presentValue M A P' i ≤ presentValue M A P i) ∧
      ∃ i, presentValue M A P' i < presentValue M A P i := by
  have hveq := aux_p1sn_eq M A P
  have hv'eq := aux_p1sn_eq M A P'
  have hwv : ∀ i, ∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j)
      ≤ presentValue M A P i := by
    intro i
    have h := hstep i (P.1 i (A i)) (P.2 i (A i))
    have : ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j)
        = presentValue M A P i := by
      rw [hveq i]
      simp only [rewardVec, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun j _ => by ring
    linarith
  have hwexp : ∀ i, ∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j)
      = rewardVec M A P' i + M.β * ∑ j, P'.1 i (A i) j * presentValue M A P j := by
    intro i
    simp only [rewardVec, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => by ring
  have hdeq : ∀ i, presentValue M A P' i - presentValue M A P i =
      (∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j)
        - presentValue M A P i) +
      M.β * ∑ j, P'.1 i (A i) j * (presentValue M A P' j - presentValue M A P j) := by
    intro i
    have h1 := hv'eq i
    have h2 := hwexp i
    have h3 : ∑ j, P'.1 i (A i) j * (presentValue M A P' j - presentValue M A P j) =
        ∑ j, P'.1 i (A i) j * presentValue M A P' j
          - ∑ j, P'.1 i (A i) j * presentValue M A P j := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [h3]
    linear_combination h1 - h2
  have hdle := aux_p1sn_le (fun i j => P'.1 i (A i) j)
    (fun i j => (aux_p1sn_row M P' i (A i)).1 j)
    (fun i => (aux_p1sn_row M P' i (A i)).2) M.β M.β_nonneg M.β_lt_one
    (fun i => presentValue M A P' i - presentValue M A P i)
    (fun i => ∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j)
        - presentValue M A P i)
    (fun i => by have := hwv i; linarith) hdeq
  refine ⟨fun i => by have := hdle i; linarith, ?_⟩
  have : ∃ i, ∑ j, P'.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j)
      ≠ presentValue M A P i := by
    by_contra hcon
    push Not at hcon
    exact hnot hcon
  obtain ⟨i, hi⟩ := this
  have hlt := lt_of_le_of_ne (hwv i) hi
  refine ⟨i, ?_⟩
  have hsum : ∑ j, P'.1 i (A i) j * (presentValue M A P' j - presentValue M A P j) ≤ 0 :=
    Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos ((aux_p1sn_row M P' i (A i)).1 j) (hdle j)
  have hb : M.β * ∑ j, P'.1 i (A i) j * (presentValue M A P' j - presentValue M A P j) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos M.β_nonneg hsum
  have := hdeq i
  linarith
