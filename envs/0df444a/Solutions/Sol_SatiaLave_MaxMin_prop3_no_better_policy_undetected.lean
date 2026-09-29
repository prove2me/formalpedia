-- Prove2me | solution 1 for SatiaLave.MaxMin.prop3_no_better_policy_undetected
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:47:17.985784+00:00
-- url     : https://prove2.me/submissions/98470a3f-e61d-496b-9b34-09bd6facf8f0

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

open Finset Matrix

theorem aux_p3nb_row {S : Type*} [Fintype S] {D : S → Type*} (M : UncertainMDP S D)
    (P : Sel M) (i : S) (k : D i) : (∀ j, 0 ≤ P.1 i k j) ∧ ∑ j, P.1 i k j = 1 :=
  M.U_subset i k (P.2 i k)

theorem aux_p3nb_det {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    (1 - M.β • transMat M A P).det ≠ 0 := by
  apply det_ne_zero_of_sum_row_lt_diag
  intro k
  obtain ⟨hnn, hsum⟩ := aux_p3nb_row M P k (A k)
  have hb0 := M.β_nonneg
  have hb1 := M.β_lt_one
  have h1 : ∀ j ∈ Finset.univ.erase k,
      ‖(1 - M.β • transMat M A P) k j‖ = M.β * P.1 k (A k) j := by
    intro j hj
    have hjk : k ≠ j := (Finset.ne_of_mem_erase hj).symm
    simp only [Matrix.sub_apply, Matrix.one_apply_ne hjk, Matrix.smul_apply, transMat,
      Matrix.of_apply, smul_eq_mul, zero_sub, norm_neg, Real.norm_eq_abs]
    exact abs_of_nonneg (mul_nonneg hb0 (hnn j))
  have hle1 : P.1 k (A k) k ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ k)
  have hkk : ‖(1 - M.β • transMat M A P) k k‖ = 1 - M.β * P.1 k (A k) k := by
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.smul_apply, transMat,
      Matrix.of_apply, smul_eq_mul, Real.norm_eq_abs]
    apply abs_of_nonneg
    nlinarith [hnn k]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ _),
    hsum, hkk]
  nlinarith [hnn k]

theorem aux_p3nb_eq5 {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    SolvesEq5 M A P (presentValue M A P) := by
  have hu : IsUnit (1 - M.β • transMat M A P).det := isUnit_iff_ne_zero.mpr (aux_p3nb_det M A P)
  have key : (1 - M.β • transMat M A P) *ᵥ presentValue M A P = rewardVec M A P := by
    unfold presentValue
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  intro i
  have h := congrFun key i
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at h
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, transMat,
    Matrix.of_apply, rewardVec] at h
  have e : ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) =
      ∑ j, P.1 i (A i) j * M.r i (A i) j +
        M.β * ∑ j, P.1 i (A i) j * presentValue M A P j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  linarith

theorem aux_p3nb_lb {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    [∀ i, Fintype (D i)] (M : UncertainMDP S D) :
    ∃ c : ℝ, ∀ (A : Policy S D) (P : Sel M) (i : S), c ≤ presentValue M A P i := by
  obtain ⟨m, hm⟩ :=
    (Set.finite_range (fun x : (i : S) × D i × S => M.r x.1 x.2.1 x.2.2)).bddBelow
  have hm' : ∀ i k j, m ≤ M.r i k j := fun i k j => hm ⟨⟨i, k, j⟩, rfl⟩
  refine ⟨m / (1 - M.β), fun A P i => ?_⟩
  have hb0 := M.β_nonneg
  have hb1 := M.β_lt_one
  have : Nonempty S := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_min (presentValue M A P)
  obtain ⟨hnn, hsum⟩ := aux_p3nb_row M P i0 (A i0)
  have e5 := aux_p3nb_eq5 M A P i0
  have hge : m + M.β * presentValue M A P i0 ≤ presentValue M A P i0 := by
    calc m + M.β * presentValue M A P i0
        = ∑ j, P.1 i0 (A i0) j * (m + M.β * presentValue M A P i0) := by
          rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ ∑ j, P.1 i0 (A i0) j * (M.r i0 (A i0) j + M.β * presentValue M A P j) := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (hnn j)
          exact add_le_add (hm' _ _ _) (mul_le_mul_of_nonneg_left (hi0 j) hb0)
      _ = presentValue M A P i0 := e5.symm
  have h1 : m / (1 - M.β) ≤ presentValue M A P i0 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  exact h1.trans (hi0 i)

theorem aux_p3nb_min {S : Type*} [Fintype S] {D : S → Type*} (M : UncertainMDP S D)
    (v : S → ℝ) (i : S) (k : D i) :
    ∃ q ∈ M.U i k, test7 M v i k = ∑ j, q j * (M.r i k j + M.β * v j) ∧
      ∀ p ∈ M.U i k, ∑ j, q j * (M.r i k j + M.β * v j) ≤ ∑ j, p j * (M.r i k j + M.β * v j) := by
  have hc : IsCompact (M.U i k) :=
    (isCompact_stdSimplex ℝ S).of_isClosed_subset (M.U_closed i k) (M.U_subset i k)
  have hcont : Continuous fun p : S → ℝ => ∑ j, p j * (M.r i k j + M.β * v j) := by
    fun_prop
  obtain ⟨q, hq, hmin⟩ := hc.exists_isMinOn (M.U_nonempty i k) hcont.continuousOn
  have hmin' := isMinOn_iff.mp hmin
  refine ⟨q, hq, ?_, fun p hp => hmin' p hp⟩
  unfold test7
  apply le_antisymm
  · have hb : BddBelow (Set.range fun p : M.U i k => ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * v j)) := by
      refine ⟨∑ j, q j * (M.r i k j + M.β * v j), ?_⟩
      rintro _ ⟨p, rfl⟩
      exact hmin' p p.2
    exact ciInf_le hb ⟨q, hq⟩
  · have : Nonempty (M.U i k) := ⟨⟨q, hq⟩⟩
    exact le_ciInf fun p => hmin' p p.2

end SatiaLave.MaxMin

open SatiaLave.MaxMin

theorem solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A : Policy S D) (hterm : IsPhase2Step M A A) :
    ∀ (B : Policy S D) (i : S), robustValue M B i ≤ robustValue M A i := by
  intro B i
  obtain ⟨c, hc⟩ := aux_p3nb_lb M
  have hb0 := M.β_nonneg
  have hb1 := M.β_lt_one
  have hbdd : ∀ (C : Policy S D) (j : S), BddBelow (Set.range fun P : Sel M => presentValue M C P j) :=
    fun C j => ⟨c, by rintro _ ⟨P, rfl⟩; exact hc C P j⟩
  have hw_le : ∀ (P : Sel M) (j : S), robustValue M A j ≤ presentValue M A P j :=
    fun P j => ciInf_le (hbdd A j) P
  have : Nonempty (Sel M) :=
    ⟨⟨fun i k => (M.U_nonempty i k).some, fun i k => (M.U_nonempty i k).some_mem⟩⟩
  -- Step 1: the robust Bellman operator of `A` does not increase `robustValue M A`.
  have h1 : ∀ j, test7 M (robustValue M A) j (A j) ≤ robustValue M A j := by
    intro j
    obtain ⟨q, hq, heq, hmin⟩ := aux_p3nb_min M (robustValue M A) j (A j)
    show _ ≤ ⨅ P : Sel M, presentValue M A P j
    apply le_ciInf
    intro P
    obtain ⟨hnn, _⟩ := aux_p3nb_row M P j (A j)
    rw [heq]
    calc ∑ l, q l * (M.r j (A j) l + M.β * robustValue M A l)
        ≤ ∑ l, P.1 j (A j) l * (M.r j (A j) l + M.β * robustValue M A l) := hmin _ (P.2 j (A j))
      _ ≤ ∑ l, P.1 j (A j) l * (M.r j (A j) l + M.β * presentValue M A P l) := by
          refine Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left ?_ (hnn l)
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hw_le P l) hb0)
      _ = presentValue M A P j := (aux_p3nb_eq5 M A P j).symm
  -- Step 2: `A` is greedy, so the same holds for `B`'s operator.
  have h2 : ∀ j, test7 M (robustValue M A) j (B j) ≤ robustValue M A j := fun j =>
    ((Finset.le_sup' (test7 M (robustValue M A) j) (Finset.mem_univ (B j))).trans
      (hterm j).1.symm.le).trans (h1 j)
  -- Step 3: nature's minimizing rows against `robustValue M A`.
  choose q hq heq hmin using fun (j : S) (k : D j) => aux_p3nb_min M (robustValue M A) j k
  let P' : Sel M := ⟨q, hq⟩
  have : Nonempty S := ⟨i⟩
  have hv : ∀ j, presentValue M B P' j ≤ robustValue M A j := by
    obtain ⟨j0, hj0⟩ :=
      Finite.exists_max (fun j => presentValue M B P' j - robustValue M A j)
    have key : ∀ j, presentValue M B P' j - robustValue M A j ≤
        M.β * (presentValue M B P' j0 - robustValue M A j0) := by
      intro j
      have e5 := aux_p3nb_eq5 M B P' j
      have t := h2 j
      rw [heq j (B j)] at t
      obtain ⟨hnn, hsum⟩ := aux_p3nb_row M P' j (B j)
      have hdiff : ∑ l, q j (B j) l * (M.r j (B j) l + M.β * presentValue M B P' l) -
          ∑ l, q j (B j) l * (M.r j (B j) l + M.β * robustValue M A l) =
          M.β * ∑ l, q j (B j) l * (presentValue M B P' l - robustValue M A l) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring
      have hbound : ∑ l, q j (B j) l * (presentValue M B P' l - robustValue M A l) ≤
          presentValue M B P' j0 - robustValue M A j0 := by
        calc ∑ l, q j (B j) l * (presentValue M B P' l - robustValue M A l)
            ≤ ∑ l, q j (B j) l * (presentValue M B P' j0 - robustValue M A j0) :=
              Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hj0 l) (hnn l)
          _ = presentValue M B P' j0 - robustValue M A j0 := by
              rw [← Finset.sum_mul]
              exact (congrArg (· * _) hsum).trans (one_mul _)
      have e5' : presentValue M B P' j =
          ∑ l, q j (B j) l * (M.r j (B j) l + M.β * presentValue M B P' l) := e5
      nlinarith
    intro j
    have h0 := key j0
    have hj0' : presentValue M B P' j0 - robustValue M A j0 ≤ 0 := by nlinarith
    linarith [hj0 j]
  -- Step 4: conclude.
  exact (ciInf_le (hbdd B i) P').trans (hv i)
