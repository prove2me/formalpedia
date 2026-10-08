-- Prove2me | solution 1 for SatiaLave.MaxMin.maxMin_policyIteration_terminates_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T06:33:22.502179+00:00
-- url     : https://prove2.me/submissions/07ee57e0-bfd4-49a5-ab84-48d9205862ac

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Eq4
import Definitions.Def_SatiaLave_MaxMin_Algorithm



namespace SatiaLave.MaxMin
end SatiaLave.MaxMin

section

namespace SatiaLave.MaxMin

open Finset

section aux_p2

set_option linter.unusedSectionVars false

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}

lemma aux_p2_nonneg (M : UncertainMDP S D) (P : Sel M) (i : S) (k : D i) (j : S) :
    0 ≤ P.1 i k j :=
  (M.U_subset i k (P.2 i k)).1 j

lemma aux_p2_sum (M : UncertainMDP S D) (P : Sel M) (i : S) (k : D i) :
    ∑ j, P.1 i k j = 1 :=
  (M.U_subset i k (P.2 i k)).2

/-- Comparison principle for `x ≥ β Q x` with `Q` row-stochastic. -/
lemma aux_p2_cmp {β : ℝ} (hβ1 : β < 1) (hβ0 : 0 ≤ β) (Q : S → S → ℝ)
    (hQ0 : ∀ i j, 0 ≤ Q i j) (hQ1 : ∀ i, ∑ j, Q i j = 1) (x : S → ℝ)
    (hx : ∀ i, β * ∑ j, Q i j * x j ≤ x i) : ∀ i, 0 ≤ x i := by
  intro i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ x ⟨i, Finset.mem_univ i⟩
  have h1 : β * x i0 ≤ β * ∑ j, Q i0 j * x j := by
    apply mul_le_mul_of_nonneg_left _ hβ0
    calc x i0 = ∑ j, Q i0 j * x i0 := by rw [← Finset.sum_mul, hQ1, one_mul]
      _ ≤ ∑ j, Q i0 j * x j := Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (hi0 j (Finset.mem_univ j)) (hQ0 i0 j)
  have h2 := hx i0
  have h3 : 0 ≤ x i0 := by nlinarith
  exact le_trans h3 (hi0 i (Finset.mem_univ i))

lemma aux_p2_solves (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (i : S) :
    presentValue M A P i =
      ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) := by
  have hdet : (1 - M.β • transMat M A P).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hcomp : ∀ i, x i = M.β * ∑ j, P.1 i (A i) j * x j := by
      intro i
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at hx
      have := congrFun hx i
      simp [Matrix.mulVec, dotProduct, transMat] at this
      linarith
    apply hx0
    funext i
    have h1 := aux_p2_cmp M.β_lt_one M.β_nonneg (fun i j => P.1 i (A i) j)
      (fun i j => aux_p2_nonneg M P i (A i) j) (fun i => aux_p2_sum M P i (A i)) x
      (fun i => (hcomp i).ge) i
    have h2 := aux_p2_cmp M.β_lt_one M.β_nonneg (fun i j => P.1 i (A i) j)
      (fun i j => aux_p2_nonneg M P i (A i) j) (fun i => aux_p2_sum M P i (A i)) (-x)
      (fun i => by
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
        linarith [hcomp i]) i
    simp only [Pi.neg_apply, Left.nonneg_neg_iff] at h2
    simp only [Pi.zero_apply]
    exact le_antisymm h2 h1
  have hunit : IsUnit (1 - M.β • transMat M A P).det := isUnit_iff_ne_zero.mpr hdet
  have hv : Matrix.mulVec (1 - M.β • transMat M A P) (presentValue M A P) =
      rewardVec M A P := by
    unfold presentValue
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec] at hv
  have := congrFun hv i
  simp [Matrix.mulVec, dotProduct, transMat, rewardVec] at this
  simp only [mul_add, Finset.sum_add_distrib]
  have e : ∑ j, P.1 i (A i) j * (M.β * presentValue M A P j) =
      M.β * ∑ j, P.1 i (A i) j * presentValue M A P j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  linarith

lemma aux_p2_sub (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (u : S → ℝ)
    (hu : ∀ i, u i ≤ ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * u j)) :
    ∀ i, u i ≤ presentValue M A P i := by
  have key := aux_p2_cmp M.β_lt_one M.β_nonneg (fun i j => P.1 i (A i) j)
    (fun i j => aux_p2_nonneg M P i (A i) j) (fun i => aux_p2_sum M P i (A i))
    (fun i => presentValue M A P i - u i) (by
      intro i
      have h1 := hu i
      have h2 := aux_p2_solves M A P i
      have h3 : M.β * ∑ j, P.1 i (A i) j * (presentValue M A P j - u j) =
          ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) -
            ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * u j) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith)
  intro i
  have := key i
  beta_reduce at this
  linarith

lemma aux_p2_super (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (u : S → ℝ)
    (hu : ∀ i, ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * u j) ≤ u i) :
    ∀ i, presentValue M A P i ≤ u i := by
  have key := aux_p2_cmp M.β_lt_one M.β_nonneg (fun i j => P.1 i (A i) j)
    (fun i j => aux_p2_nonneg M P i (A i) j) (fun i => aux_p2_sum M P i (A i))
    (fun i => u i - presentValue M A P i) (by
      intro i
      have h1 := hu i
      have h2 := aux_p2_solves M A P i
      have h3 : M.β * ∑ j, P.1 i (A i) j * (u j - presentValue M A P j) =
          ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * u j) -
            ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      linarith)
  intro i
  have := key i
  beta_reduce at this
  linarith

lemma aux_p2_lb (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (i : S) :
    -(∑ a, ∑ b, |M.r a (A a) b|) / (1 - M.β) ≤ presentValue M A P i := by
  have hβ : 0 < 1 - M.β := by linarith [M.β_lt_one]
  apply aux_p2_sub M A P (fun _ => -(∑ a, ∑ b, |M.r a (A a) b|) / (1 - M.β)) _ i
  intro a
  have hr : ∀ b, -(∑ a, ∑ b, |M.r a (A a) b|) ≤ M.r a (A a) b := fun b => by
    have h1 : |M.r a (A a) b| ≤ ∑ b', |M.r a (A a) b'| :=
      Finset.single_le_sum (f := fun b' => |M.r a (A a) b'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ b)
    have h2 : ∑ b', |M.r a (A a) b'| ≤ ∑ a, ∑ b, |M.r a (A a) b| :=
      Finset.single_le_sum (f := fun a' => ∑ b', |M.r a' (A a') b'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ a)
    linarith [neg_abs_le (M.r a (A a) b)]
  set R := ∑ a, ∑ b, |M.r a (A a) b| with hR
  calc -R / (1 - M.β) = ∑ j, P.1 a (A a) j * (-R + M.β * (-R / (1 - M.β))) := by
        rw [← Finset.sum_mul, aux_p2_sum, one_mul]; field_simp; ring
    _ ≤ _ := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (by linarith [hr j]) (aux_p2_nonneg M P a (A a) j)

lemma aux_p2_selne (M : UncertainMDP S D) : Nonempty (Sel M) :=
  ⟨⟨fun i k => (M.U_nonempty i k).some, fun i k => (M.U_nonempty i k).some_mem⟩⟩

lemma aux_p2_bdd (M : UncertainMDP S D) (A : Policy S D) (i : S) :
    BddBelow (Set.range fun P : Sel M => presentValue M A P i) := by
  refine ⟨-(∑ a, ∑ b, |M.r a (A a) b|) / (1 - M.β), ?_⟩
  rintro _ ⟨P, rfl⟩
  exact aux_p2_lb M A P i

lemma aux_p2_le_pv (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (i : S) :
    robustValue M A i ≤ presentValue M A P i :=
  ciInf_le (aux_p2_bdd M A i) P

lemma aux_p2_ofRows (M : UncertainMDP S D) (A : Policy S D) (q : S → S → ℝ)
    (hq : ∀ j, q j ∈ M.U j (A j)) : ∃ P : Sel M, ∀ j, P.1 j (A j) = q j := by
  classical
  refine ⟨⟨fun j k => if k = A j then q j else (M.U_nonempty j k).some, ?_⟩, ?_⟩
  · intro j k
    by_cases h : k = A j
    · subst h; simp [hq]
    · simp only [h, if_false]; exact (M.U_nonempty j k).some_mem
  · intro j; simp

lemma aux_p2_near (M : UncertainMDP S D) (A : Policy S D) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Sel M, ∀ i, presentValue M A P i ≤ robustValue M A i + ε := by
  have := aux_p2_selne M
  have h : ∀ j, ∃ P : Sel M, presentValue M A P j < robustValue M A j + ε := by
    intro j
    exact exists_lt_of_ciInf_lt (f := fun P : Sel M => presentValue M A P j)
      (show robustValue M A j < robustValue M A j + ε by linarith)
  choose F hF using h
  have hm : ∀ l, ∃ m, ∀ j, presentValue M A (F m) l ≤ presentValue M A (F j) l := by
    intro l
    obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ
      (fun j => presentValue M A (F j) l) ⟨l, Finset.mem_univ l⟩
    exact ⟨m, fun j => hm j (Finset.mem_univ j)⟩
  choose m hm using hm
  obtain ⟨P, hP⟩ := aux_p2_ofRows M A (fun l => (F (m l)).1 l (A l))
    (fun l => (F (m l)).2 l (A l))
  refine ⟨P, fun i => ?_⟩
  have hsup := aux_p2_super M A P (fun l => presentValue M A (F (m l)) l) ?_ i
  · exact le_trans hsup (le_trans (hm i i) (hF i).le)
  · intro l
    rw [hP l]
    calc ∑ j, (F (m l)).1 l (A l) j * (M.r l (A l) j + M.β * presentValue M A (F (m j)) j)
        ≤ ∑ j, (F (m l)).1 l (A l) j *
            (M.r l (A l) j + M.β * presentValue M A (F (m l)) j) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (aux_p2_nonneg M _ l (A l) j)
          have := hm j (m l)
          nlinarith [M.β_nonneg]
      _ = presentValue M A (F (m l)) l := (aux_p2_solves M A (F (m l)) l).symm

lemma aux_p2_bge (M : UncertainMDP S D) (A : Policy S D) (i : S) (p : S → ℝ)
    (hp : p ∈ M.U i (A i)) :
    robustValue M A i ≤ ∑ j, p j * (M.r i (A i) j + M.β * robustValue M A j) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = robustValue M A i -
      ∑ j, p j * (M.r i (A i) j + M.β * robustValue M A j) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by linarith
  have hβ := M.β_lt_one
  have hβ0 := M.β_nonneg
  obtain ⟨P, hP⟩ := aux_p2_near M A (δ / 2) (by linarith)
  obtain ⟨P', hP'⟩ := aux_p2_ofRows M A (fun j => if j = i then p else P.1 j (A j)) (by
    intro j; by_cases h : j = i
    · subst h; simpa using hp
    · simpa [h] using P.2 j (A j))
  have hpsum : ∑ j, p j = 1 := (M.U_subset i (A i) hp).2
  have hp0 : ∀ j, 0 ≤ p j := (M.U_subset i (A i) hp).1
  have hest : ∑ j, p j * (M.r i (A i) j + M.β * presentValue M A P j) ≤
      robustValue M A i - δ + M.β * (δ / 2) := by
    calc ∑ j, p j * (M.r i (A i) j + M.β * presentValue M A P j)
        ≤ ∑ j, p j * (M.r i (A i) j + M.β * (robustValue M A j + δ / 2)) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (hp0 j)
          nlinarith [hP j]
      _ = ∑ j, p j * (M.r i (A i) j + M.β * robustValue M A j) +
            (∑ j, p j) * (M.β * (δ / 2)) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = robustValue M A i - δ + M.β * (δ / 2) := by rw [hpsum, hδ]; ring
  have hsup := aux_p2_super M A P' (presentValue M A P) (by
    intro l
    rw [hP' l]
    by_cases h : l = i
    · subst h
      simp only [if_true]
      have := aux_p2_le_pv M A P l
      nlinarith
    · simp only [h, if_false]
      exact (aux_p2_solves M A P l).ge)
  have h1 := aux_p2_solves M A P' i
  rw [hP' i] at h1
  simp only [if_true] at h1
  have h2 : presentValue M A P' i ≤
      ∑ j, p j * (M.r i (A i) j + M.β * presentValue M A P j) := by
    rw [h1]; apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (hp0 j)
    nlinarith [hsup j]
  have h3 := aux_p2_le_pv M A P' i
  nlinarith

lemma aux_p2_test7_le (M : UncertainMDP S D) (v : S → ℝ) (i : S) (k : D i) (p : S → ℝ)
    (hp : p ∈ M.U i k) :
    test7 M v i k ≤ ∑ j, p j * (M.r i k j + M.β * v j) := by
  refine ciInf_le (f := fun p : M.U i k => ∑ j, (p : S → ℝ) j * (M.r i k j + M.β * v j))
    ?_ ⟨p, hp⟩
  refine ⟨-∑ j, |M.r i k j + M.β * v j|, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hq := M.U_subset i k q.2
  calc -∑ j, |M.r i k j + M.β * v j|
      = ∑ j, (q : S → ℝ) j * (-∑ j', |M.r i k j' + M.β * v j'|) := by
        rw [← Finset.sum_mul, hq.2, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (by
        have := Finset.single_le_sum (f := fun j' => |M.r i k j' + M.β * v j'|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
        linarith [neg_abs_le (M.r i k j + M.β * v j)]) (hq.1 j)

lemma aux_p2_beq (M : UncertainMDP S D) (A : Policy S D) (i : S) :
    test7 M (robustValue M A) i (A i) = robustValue M A i := by
  have := aux_p2_selne M
  have : Nonempty (M.U i (A i)) := (M.U_nonempty i (A i)).to_subtype
  apply le_antisymm
  · show test7 M (robustValue M A) i (A i) ≤ ⨅ P : Sel M, presentValue M A P i
    refine le_ciInf fun P => ?_
    refine le_trans (aux_p2_test7_le M _ i (A i) _ (P.2 i (A i))) ?_
    rw [aux_p2_solves M A P i]
    apply Finset.sum_le_sum; intro j _
    apply mul_le_mul_of_nonneg_left _ (aux_p2_nonneg M P i (A i) j)
    nlinarith [aux_p2_le_pv M A P j, M.β_nonneg]
  · exact le_ciInf fun p => aux_p2_bge M A i p p.2

end aux_p2

end SatiaLave.MaxMin

open SatiaLave.MaxMin Finset

theorem p2sol_core {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A B : Policy S D) (hstep : IsPhase2Step M A B) (hne : B ≠ A) :
    (∀ i, robustValue M A i ≤ robustValue M B i) ∧ ∃ i, robustValue M A i < robustValue M B i := by
  have hBv : ∀ P : Sel M, ∀ i, robustValue M A i ≤ presentValue M B P i := by
    intro P
    apply aux_p2_sub M B P
    intro i
    calc robustValue M A i = test7 M (robustValue M A) i (A i) := (aux_p2_beq M A i).symm
      _ ≤ (Finset.univ : Finset (D i)).sup' Finset.univ_nonempty
            (test7 M (robustValue M A) i) := Finset.le_sup' _ (Finset.mem_univ _)
      _ = test7 M (robustValue M A) i (B i) := ((hstep i).1).symm
      _ ≤ _ := aux_p2_test7_le M _ i (B i) _ (P.2 i (B i))
  have := aux_p2_selne M
  refine ⟨fun i => ?_, ?_⟩
  · show robustValue M A i ≤ ⨅ P : Sel M, presentValue M B P i
    exact le_ciInf fun P => hBv P i
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hne
  have hlt : test7 M (robustValue M A) i0 (A i0) <
      (Finset.univ : Finset (D i0)).sup' Finset.univ_nonempty
        (test7 M (robustValue M A) i0) := by
    refine lt_of_le_of_ne (Finset.le_sup' _ (Finset.mem_univ _)) ?_
    intro heq; exact hi0 ((hstep i0).2 heq)
  refine ⟨i0, ?_⟩
  rw [aux_p2_beq M A i0] at hlt
  refine lt_of_lt_of_le hlt ?_
  show _ ≤ ⨅ P : Sel M, presentValue M B P i0
  refine le_ciInf fun P => ?_
  rw [← (hstep i0).1, aux_p2_solves M B P i0]
  refine le_trans (aux_p2_test7_le M _ i0 (B i0) _ (P.2 i0 (B i0))) ?_
  apply Finset.sum_le_sum; intro j _
  apply mul_le_mul_of_nonneg_left _ (aux_p2_nonneg M P i0 (B i0) j)
  nlinarith [hBv P j, M.β_nonneg]

end

section

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

theorem p3sol_core {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
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

end

section

namespace SatiaLave.MaxMin

open Finset MeasureTheory

set_option linter.unusedSectionVars false

section aux_pl

variable {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)]

/-- the linear functional `p ↦ Σ_l p_l (r_{jkl} + β v_l)` -/
noncomputable def aux_pl_f (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) (p : S → ℝ) : ℝ :=
  ∑ l, p l * (M.r j k l + M.β * v l)

/-- nature's row minimum -/
noncomputable def aux_pl_rowMin (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) : ℝ :=
  ⨅ p : M.U j k, aux_pl_f M j k v p

lemma aux_pl_U_compact (M : UncertainMDP S D) (j : S) (k : D j) : IsCompact (M.U j k) :=
  (isCompact_stdSimplex (𝕜 := ℝ) (ι := S)).of_isClosed_subset (M.U_closed j k) (M.U_subset j k)

lemma aux_pl_f_cont (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) :
    Continuous (aux_pl_f M j k v) := by
  unfold aux_pl_f
  fun_prop

lemma aux_pl_rowMin_spec (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) :
    ∃ p ∈ M.U j k, aux_pl_rowMin M j k v = aux_pl_f M j k v p ∧
      ∀ q ∈ M.U j k, aux_pl_f M j k v p ≤ aux_pl_f M j k v q := by
  obtain ⟨p, hp, hmin⟩ := (aux_pl_U_compact M j k).exists_isMinOn (M.U_nonempty j k)
    (aux_pl_f_cont M j k v).continuousOn
  have hmin' : ∀ q ∈ M.U j k, aux_pl_f M j k v p ≤ aux_pl_f M j k v q := isMinOn_iff.1 hmin
  refine ⟨p, hp, ?_, hmin'⟩
  unfold aux_pl_rowMin
  apply le_antisymm
  · exact ciInf_le ⟨aux_pl_f M j k v p, Set.forall_mem_range.2 fun (q : M.U j k) => hmin' q.1 q.2⟩ ⟨p, hp⟩
  · haveI : Nonempty (M.U j k) := ⟨⟨p, hp⟩⟩
    exact le_ciInf fun q => hmin' q.1 q.2

lemma aux_pl_rowMin_le (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) (q : S → ℝ)
    (hq : q ∈ M.U j k) : aux_pl_rowMin M j k v ≤ aux_pl_f M j k v q := by
  obtain ⟨p, _, h1, h2⟩ := aux_pl_rowMin_spec M j k v
  rw [h1]; exact h2 q hq

lemma aux_pl_inner (M : UncertainMDP S D) (j : S) (k : D j) (v : S → ℝ) :
    (⨅ α : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1},
      ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(α.1 : Measure (S → ℝ))) =
      aux_pl_rowMin M j k v := by
  obtain ⟨p0, hp0, h1, h2⟩ := aux_pl_rowMin_spec M j k v
  have hmeas : MeasurableSet (M.U j k) := (M.U_closed j k).measurableSet
  have lower : ∀ α : {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1},
      aux_pl_rowMin M j k v ≤
        ∫ p, ∑ l, p l * (M.r j k l + M.β * v l) ∂(α.1 : Measure (S → ℝ)) := by
    rintro ⟨μ, hμ⟩
    have hae : ∀ᵐ p ∂(μ : Measure (S → ℝ)), p ∈ M.U j k := by
      rw [ae_iff]
      exact (prob_compl_eq_zero_iff hmeas).2 hμ
    have hint : Integrable (fun p : S → ℝ => ∑ l, p l * (M.r j k l + M.β * v l))
        (μ : Measure (S → ℝ)) := by
      refine Integrable.of_bound ((aux_pl_f_cont M j k v).aestronglyMeasurable)
        (∑ l, |M.r j k l + M.β * v l|) ?_
      filter_upwards [hae] with p hp
      have hps := M.U_subset j k hp
      rw [Real.norm_eq_abs]
      refine (abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [abs_mul]
      have h0 : 0 ≤ p l := hps.1 l
      have h1' : p l ≤ 1 := by
        rw [← hps.2]
        exact Finset.single_le_sum (fun i _ => hps.1 i) (mem_univ l)
      rw [abs_of_nonneg h0]
      exact mul_le_of_le_one_left (abs_nonneg _) h1'
    rw [h1]
    calc aux_pl_f M j k v p0 = ∫ _p, aux_pl_f M j k v p0 ∂(μ : Measure (S → ℝ)) := by simp
      _ ≤ _ := integral_mono_ae (integrable_const _) hint
          (by filter_upwards [hae] with p hp; exact h2 p hp)
  have hd : ((⟨Measure.dirac p0, inferInstance⟩ : ProbabilityMeasure (S → ℝ)) :
      Measure (S → ℝ)) (M.U j k) = 1 := Measure.dirac_apply_of_mem hp0
  apply le_antisymm
  · refine (ciInf_le ⟨_, Set.forall_mem_range.2 lower⟩ ⟨⟨Measure.dirac p0, inferInstance⟩, hd⟩).trans ?_
    rw [h1]
    show ∫ p, aux_pl_f M j k v p ∂(Measure.dirac p0) ≤ aux_pl_f M j k v p0
    rw [integral_dirac' _ _ (aux_pl_f_cont M j k v).stronglyMeasurable]
  · haveI : Nonempty {μ : ProbabilityMeasure (S → ℝ) // (μ : Measure (S → ℝ)) (M.U j k) = 1} :=
      ⟨⟨_, hd⟩⟩
    exact le_ciInf lower

lemma aux_pl_sup (j : S) [Nonempty (D j)] (m : D j → ℝ) :
    (⨆ τ : stdSimplex ℝ (D j), ∑ k, (τ : D j → ℝ) k * m k) = univ.sup' univ_nonempty m := by
  classical
  obtain ⟨k0, -, hk0⟩ := Finset.exists_mem_eq_sup' univ_nonempty m
  have upper : ∀ τ : stdSimplex ℝ (D j), ∑ k, (τ : D j → ℝ) k * m k ≤ univ.sup' univ_nonempty m := by
    rintro ⟨τ, hτ0, hτ1⟩
    calc ∑ k, τ k * m k ≤ ∑ k, τ k * univ.sup' univ_nonempty m :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (Finset.le_sup' m (mem_univ k)) (hτ0 k)
      _ = _ := by rw [← Finset.sum_mul, hτ1, one_mul]
  apply le_antisymm
  · haveI : Nonempty (stdSimplex ℝ (D j)) := ⟨⟨_, single_mem_stdSimplex ℝ k0⟩⟩
    exact ciSup_le upper
  · refine le_trans ?_ (le_ciSup ⟨_, Set.forall_mem_range.2 upper⟩ ⟨_, single_mem_stdSimplex ℝ k0⟩)
    simp [hk0, Pi.single_apply]

lemma aux_pl_eq4 [∀ i, Nonempty (D i)] (M : UncertainMDP S D) (v : S → ℝ) (j : S) :
    eq4Op M v j = univ.sup' univ_nonempty (fun k => aux_pl_rowMin M j k v) := by
  unfold eq4Op
  simp only [aux_pl_inner]
  exact aux_pl_sup j _

/-- the generalized Bellman operator -/
noncomputable def aux_pl_T (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) (v : S → ℝ) : S → ℝ :=
  fun j => (F j).sup' (hF j) (fun k => aux_pl_rowMin M j k v)

lemma aux_pl_simplex_le (p : S → ℝ) (hp : p ∈ stdSimplex ℝ S) (d : S → ℝ) (c : ℝ)
    (hd : ∀ l, d l ≤ c) : ∑ l, p l * d l ≤ c := by
  calc ∑ l, p l * d l ≤ ∑ l, p l * c :=
        Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hd l) (hp.1 l)
    _ = c := by rw [← Finset.sum_mul, hp.2, one_mul]

lemma aux_pl_f_sub (M : UncertainMDP S D) (j : S) (k : D j) (v u p : S → ℝ) :
    aux_pl_f M j k v p - aux_pl_f M j k u p = M.β * ∑ l, p l * (v l - u l) := by
  unfold aux_pl_f
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma aux_pl_rowMin_lip (M : UncertainMDP S D) (j : S) (k : D j) (v u : S → ℝ) :
    aux_pl_rowMin M j k v ≤ aux_pl_rowMin M j k u + M.β * dist v u := by
  obtain ⟨p, hp, h1, _⟩ := aux_pl_rowMin_spec M j k u
  have h2 := aux_pl_rowMin_le M j k v p hp
  have h3 := aux_pl_f_sub M j k v u p
  have h4 : ∑ l, p l * (v l - u l) ≤ dist v u :=
    aux_pl_simplex_le p (M.U_subset j k hp) _ _ fun l => by
      have := dist_le_pi_dist v u l
      rw [Real.dist_eq] at this
      exact (le_abs_self _).trans this
  have h5 := mul_le_mul_of_nonneg_left h4 M.β_nonneg
  linarith

lemma aux_pl_T_lip (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) (v u : S → ℝ) (j : S) :
    aux_pl_T M F hF v j ≤ aux_pl_T M F hF u j + M.β * dist v u := by
  unfold aux_pl_T
  refine Finset.sup'_le _ _ fun k hk => ?_
  exact (aux_pl_rowMin_lip M j k v u).trans
    (add_le_add_left (Finset.le_sup' (fun k => aux_pl_rowMin M j k u) hk) _)

lemma aux_pl_T_dist (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) (v u : S → ℝ) :
    dist (aux_pl_T M F hF v) (aux_pl_T M F hF u) ≤ M.β * dist v u := by
  refine (dist_pi_le_iff (mul_nonneg M.β_nonneg dist_nonneg)).2 fun j => ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor
  · linarith [aux_pl_T_lip M F hF v u j]
  · have := aux_pl_T_lip M F hF u v j
    rw [dist_comm u v] at this
    linarith

lemma aux_pl_T_contr (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) :
    ContractingWith (⟨M.β, M.β_nonneg⟩ : NNReal) (aux_pl_T M F hF) := by
  refine ⟨?_, LipschitzWith.of_dist_le_mul fun v u => ?_⟩
  · exact NNReal.coe_lt_coe.1 M.β_lt_one
  · exact aux_pl_T_dist M F hF v u

noncomputable def aux_pl_fix (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) : S → ℝ :=
  ContractingWith.fixedPoint (aux_pl_T M F hF) (aux_pl_T_contr M F hF)

lemma aux_pl_fix_eq (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) : aux_pl_T M F hF (aux_pl_fix M F hF) = aux_pl_fix M F hF :=
  ContractingWith.fixedPoint_isFixedPt (aux_pl_T_contr M F hF)

lemma aux_pl_fix_unique (M : UncertainMDP S D) (F : (j : S) → Finset (D j))
    (hF : ∀ j, (F j).Nonempty) (v : S → ℝ) (hv : aux_pl_T M F hF v = v) :
    v = aux_pl_fix M F hF :=
  ContractingWith.fixedPoint_unique (aux_pl_T_contr M F hF) hv

lemma aux_pl_min_nonneg (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (q : S → S → ℝ)
    (hq : ∀ i, q i ∈ stdSimplex ℝ S) (d : S → ℝ) (h : ∀ i, β * ∑ l, q i l * d l ≤ d i) :
    ∀ i, 0 ≤ d i := by
  intro i
  by_contra hneg
  push Not at hneg
  haveI : Nonempty S := ⟨i⟩
  obtain ⟨i0, hi0⟩ := Finite.exists_min d
  have h1 : d i0 ≤ ∑ l, q i0 l * d l := by
    calc d i0 = ∑ l, q i0 l * d i0 := by rw [← Finset.sum_mul, (hq i0).2, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hi0 l) ((hq i0).1 l)
  have h2 := h i0
  have h3 : β * d i0 ≤ β * ∑ l, q i0 l * d l := mul_le_mul_of_nonneg_left h1 hβ0
  have h4 := hi0 i
  nlinarith [mul_pos (sub_pos.2 hβ1) (neg_pos.2 (lt_of_le_of_lt h4 hneg))]

lemma aux_pl_max_nonpos (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (q : S → S → ℝ)
    (hq : ∀ i, q i ∈ stdSimplex ℝ S) (d : S → ℝ) (h : ∀ i, d i ≤ β * ∑ l, q i l * d l) :
    ∀ i, d i ≤ 0 := by
  intro i
  have := aux_pl_min_nonneg β hβ0 hβ1 q hq (fun i => -d i) (fun i => by
    simp only [mul_neg, Finset.sum_neg_distrib]
    linarith [h i]) i
  linarith

lemma aux_pl_zero (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (q : S → S → ℝ)
    (hq : ∀ i, q i ∈ stdSimplex ℝ S) (d : S → ℝ) (h : ∀ i, d i = β * ∑ l, q i l * d l) :
    ∀ i, d i = 0 := fun i =>
  le_antisymm (aux_pl_max_nonpos β hβ0 hβ1 q hq d (fun i => (h i).le) i)
    (aux_pl_min_nonneg β hβ0 hβ1 q hq d (fun i => (h i).symm.le) i)

lemma aux_pl_Bmul (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (z : S → ℝ) (i : S) :
    Matrix.mulVec (1 - M.β • transMat M A P) z i = z i - M.β * ∑ l, P.1 i (A i) l * z l := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rfl

lemma aux_pl_pv_solves (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    SolvesEq5 M A P (presentValue M A P) := by
  have hrow : ∀ i, P.1 i (A i) ∈ stdSimplex ℝ S := fun i => M.U_subset _ _ (P.2 i (A i))
  have hinj : Function.Injective (1 - M.β • transMat M A P).mulVec := by
    intro x y hxy
    have e : ∀ i, (x - y) i = M.β * ∑ l, P.1 i (A i) l * (x - y) l := by
      intro i
      have hz : Matrix.mulVec (1 - M.β • transMat M A P) (x - y) i = 0 := by
        rw [Matrix.mulVec_sub, hxy, sub_self]; rfl
      rw [aux_pl_Bmul] at hz
      linarith
    have := aux_pl_zero M.β M.β_nonneg M.β_lt_one (fun i => P.1 i (A i)) hrow (x - y) e
    funext i
    have := this i
    simp only [Pi.sub_apply] at this
    linarith
  have hunit : IsUnit (1 - M.β • transMat M A P) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (1 - M.β • transMat M A P).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 hunit
  have key : Matrix.mulVec (1 - M.β • transMat M A P) (presentValue M A P) = rewardVec M A P := by
    unfold presentValue
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  intro i
  have := congrFun key i
  rw [aux_pl_Bmul] at this
  simp only [rewardVec] at this
  have hs : ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) =
      ∑ j, P.1 i (A i) j * M.r i (A i) j + M.β * ∑ j, P.1 i (A i) j * presentValue M A P j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hs]
  linarith

lemma aux_pl_eq5_unique (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (v w : S → ℝ)
    (hv : SolvesEq5 M A P v) (hw : SolvesEq5 M A P w) : v = w := by
  have hrow : ∀ i, P.1 i (A i) ∈ stdSimplex ℝ S := fun i => M.U_subset _ _ (P.2 i (A i))
  have e : ∀ i, (v - w) i = M.β * ∑ l, P.1 i (A i) l * (v - w) l := by
    intro i
    have h4 := aux_pl_f_sub M i (A i) v w (P.1 i (A i))
    unfold aux_pl_f at h4
    rw [← hv i, ← hw i] at h4
    simpa using h4
  have := aux_pl_zero M.β M.β_nonneg M.β_lt_one (fun i => P.1 i (A i)) hrow (v - w) e
  funext i
  have := this i
  simp only [Pi.sub_apply] at this
  linarith

variable [∀ i, Nonempty (D i)]

noncomputable def aux_pl_w (M : UncertainMDP S D) (A : Policy S D) : S → ℝ :=
  aux_pl_fix M (fun j => {A j}) (fun _ => singleton_nonempty _)

noncomputable def aux_pl_vstar (M : UncertainMDP S D) : S → ℝ :=
  aux_pl_fix M (fun j => (univ : Finset (D j))) (fun _ => univ_nonempty)

lemma aux_pl_w_eq (M : UncertainMDP S D) (A : Policy S D) (i : S) :
    aux_pl_w M A i = aux_pl_rowMin M i (A i) (aux_pl_w M A) := by
  have := congrFun (aux_pl_fix_eq M (fun j => {A j}) (fun _ => singleton_nonempty _)) i
  unfold aux_pl_w
  rw [← this]
  simp only [aux_pl_T, Finset.sup'_singleton]

lemma aux_pl_vstar_eq (M : UncertainMDP S D) (i : S) :
    aux_pl_vstar M i = univ.sup' univ_nonempty (fun k => aux_pl_rowMin M i k (aux_pl_vstar M)) :=
  (congrFun (aux_pl_fix_eq M (fun j => (univ : Finset (D j))) (fun _ => univ_nonempty)) i).symm

noncomputable def aux_pl_Pstar (M : UncertainMDP S D) (w : S → ℝ) : Sel M :=
  Subtype.mk (fun i k => Classical.choose (aux_pl_rowMin_spec M i k w))
    (fun i k => (Classical.choose_spec (aux_pl_rowMin_spec M i k w)).1)

lemma aux_pl_Pstar_spec (M : UncertainMDP S D) (w : S → ℝ) (i : S) (k : D i) :
    aux_pl_rowMin M i k w = aux_pl_f M i k w ((aux_pl_Pstar M w).1 i k) :=
  (Classical.choose_spec (aux_pl_rowMin_spec M i k w)).2.1

lemma aux_pl_w_le_pv (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) (i : S) :
    aux_pl_w M A i ≤ presentValue M A P i := by
  have hsol := aux_pl_pv_solves M A P
  have key : ∀ i, M.β * ∑ l, P.1 i (A i) l * (presentValue M A P l - aux_pl_w M A l) ≤
      presentValue M A P i - aux_pl_w M A i := by
    intro i
    have h1 := hsol i
    have h2 := aux_pl_rowMin_le M i (A i) (aux_pl_w M A) (P.1 i (A i)) (P.2 i (A i))
    have h3 := aux_pl_w_eq M A i
    have h4 := aux_pl_f_sub M i (A i) (presentValue M A P) (aux_pl_w M A) (P.1 i (A i))
    unfold aux_pl_f at h2 h4
    rw [← h1] at h4
    linarith
  have := aux_pl_min_nonneg M.β M.β_nonneg M.β_lt_one (fun i => P.1 i (A i))
    (fun i => M.U_subset _ _ (P.2 i (A i))) (fun i => presentValue M A P i - aux_pl_w M A i) key i
  linarith

lemma aux_pl_pv_Pstar (M : UncertainMDP S D) (A : Policy S D) :
    presentValue M A (aux_pl_Pstar M (aux_pl_w M A)) = aux_pl_w M A := by
  apply aux_pl_eq5_unique M A (aux_pl_Pstar M (aux_pl_w M A)) _ _
    (aux_pl_pv_solves M A _)
  intro i
  rw [aux_pl_w_eq M A i, aux_pl_Pstar_spec M (aux_pl_w M A) i (A i)]
  rfl

lemma aux_pl_robust (M : UncertainMDP S D) (A : Policy S D) (i : S) :
    robustValue M A i = aux_pl_w M A i := by
  unfold robustValue
  have hP := aux_pl_pv_Pstar M A
  apply le_antisymm
  · refine (ciInf_le ⟨aux_pl_w M A i, Set.forall_mem_range.2 fun P => aux_pl_w_le_pv M A P i⟩
      (aux_pl_Pstar M (aux_pl_w M A))).trans ?_
    rw [hP]
  · haveI : Nonempty (Sel M) := ⟨aux_pl_Pstar M (aux_pl_w M A)⟩
    exact le_ciInf fun P => aux_pl_w_le_pv M A P i

lemma aux_pl_w_le_vstar (M : UncertainMDP S D) (A : Policy S D) (i : S) :
    aux_pl_w M A i ≤ aux_pl_vstar M i := by
  let q : S → S → ℝ := fun i => (aux_pl_Pstar M (aux_pl_vstar M)).1 i (A i)
  have hq : ∀ i, q i ∈ M.U i (A i) := fun i => (aux_pl_Pstar M (aux_pl_vstar M)).2 i (A i)
  have key : ∀ i, aux_pl_w M A i - aux_pl_vstar M i ≤
      M.β * ∑ l, q i l * (aux_pl_w M A l - aux_pl_vstar M l) := by
    intro i
    have h1 := aux_pl_w_eq M A i
    have h2 := aux_pl_rowMin_le M i (A i) (aux_pl_w M A) (q i) (hq i)
    have h3 : aux_pl_rowMin M i (A i) (aux_pl_vstar M) ≤ aux_pl_vstar M i :=
      (Finset.le_sup' (fun k => aux_pl_rowMin M i k (aux_pl_vstar M)) (mem_univ (A i))).trans_eq
        (aux_pl_vstar_eq M i).symm
    have h4 := aux_pl_f_sub M i (A i) (aux_pl_w M A) (aux_pl_vstar M) (q i)
    have h5 := aux_pl_Pstar_spec M (aux_pl_vstar M) i (A i)
    linarith
  have := aux_pl_max_nonpos M.β M.β_nonneg M.β_lt_one q (fun i => M.U_subset _ _ (hq i))
    (fun i => aux_pl_w M A i - aux_pl_vstar M i) key i
  linarith

lemma aux_pl_exists_opt (M : UncertainMDP S D) : ∃ A : Policy S D, aux_pl_w M A = aux_pl_vstar M := by
  choose A hA using fun i => Finset.exists_mem_eq_sup' (univ_nonempty (α := D i))
    (fun k => aux_pl_rowMin M i k (aux_pl_vstar M))
  refine ⟨A, ?_⟩
  unfold aux_pl_w
  refine (aux_pl_fix_unique M (fun j => {A j}) (fun _ => singleton_nonempty _) (aux_pl_vstar M) ?_).symm
  funext i
  show ({A i} : Finset (D i)).sup' _ (fun k => aux_pl_rowMin M i k (aux_pl_vstar M)) =
    aux_pl_vstar M i
  rw [Finset.sup'_singleton, aux_pl_vstar_eq M i, (hA i).2]

lemma aux_pl_maxMin (M : UncertainMDP S D) : maxMinValue M = aux_pl_vstar M := by
  funext i
  unfold maxMinValue
  obtain ⟨A, hA⟩ := aux_pl_exists_opt M
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun B _ => ?_
    rw [aux_pl_robust]
    exact aux_pl_w_le_vstar M B i
  · refine le_trans ?_ (Finset.le_sup' (fun B => robustValue M B i) (mem_univ A))
    show aux_pl_vstar M i ≤ robustValue M A i
    rw [aux_pl_robust, hA]

end aux_pl

end SatiaLave.MaxMin

open SatiaLave.MaxMin Finset

theorem p1sol_core {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) :
    (∃! v : S → ℝ, ∀ j, v j = eq4Op M v j) ∧ ∀ j, maxMinValue M j = eq4Op M (maxMinValue M) j := by
  have hT : ∀ v j, eq4Op M v j =
      aux_pl_T M (fun j => (univ : Finset (D j))) (fun _ => univ_nonempty) v j :=
    fun v j => aux_pl_eq4 M v j
  have hfix := aux_pl_fix_eq M (fun j => (univ : Finset (D j))) (fun _ => univ_nonempty)
  refine ⟨⟨aux_pl_vstar M, fun j => ?_, fun v hv => ?_⟩, fun j => ?_⟩
  · rw [hT]
    exact (congrFun hfix j).symm
  · apply aux_pl_fix_unique
    funext j
    rw [← hT]
    exact (hv j).symm
  · rw [aux_pl_maxMin, hT]
    exact (congrFun hfix j).symm

end

namespace SatiaLave.MaxMin

theorem goal_core {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A : ℕ → Policy S D) (hrun : ∀ n, IsPhase2Step M (A n) (A (n + 1))) :
    (∀ n i, robustValue M (A n) i ≤ robustValue M (A (n + 1)) i) ∧
      ∃ n, n < Fintype.card (Policy S D) ∧ A (n + 1) = A n ∧ IsMaxMinOptimal M (A n) ∧
        (∀ v : S → ℝ, (∀ j, v j = eq4Op M v j) → ∀ j, robustValue M (A n) j = v j) ∧
        ∀ ε > 0, IsEpsMaxMinOptimal M ε (A n) := by
  have hmono : ∀ n i, robustValue M (A n) i ≤ robustValue M (A (n + 1)) i := by
    intro n i
    by_cases h : A (n + 1) = A n
    · rw [h]
    · exact (p2sol_core M (A n) (A (n + 1)) (hrun n) h).1 i
  refine ⟨hmono, ?_⟩
  -- f n = sum of values
  set N := Fintype.card (Policy S D) with hN
  have hex : ∃ n, n < N ∧ A (n + 1) = A n := by
    by_contra hcon
    push_neg at hcon
    let f : ℕ → ℝ := fun n => ∑ i, robustValue M (A n) i
    have hstep : ∀ n, n < N → f n < f (n + 1) := by
      intro n hn
      obtain ⟨h1, i, hi⟩ := p2sol_core M (A n) (A (n + 1)) (hrun n) (hcon n hn)
      exact Finset.sum_lt_sum (fun j _ => h1 j) ⟨i, Finset.mem_univ _, hi⟩
    have hsm : ∀ m n, m < n → n ≤ N → f m < f n := by
      intro m n hmn hnN
      induction n with
      | zero => omega
      | succ n ih =>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with h | h
        · exact (ih h (by omega)).trans (hstep n (by omega))
        · subst h; exact hstep m (by omega)
    have hinj : Function.Injective (fun k : Fin (N + 1) => A k.1) := by
      intro a b hab
      simp only at hab
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · have := hsm a b h (by omega)
        simp only [f, hab] at this
        exact lt_irrefl _ this
      · have := hsm b a h (by omega)
        simp only [f, hab] at this
        exact lt_irrefl _ this
    have := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨n, hn, hfix⟩ := hex
  have hstepA : IsPhase2Step M (A n) (A n) := by
    have := hrun n
    rwa [hfix] at this
  have hopt : IsMaxMinOptimal M (A n) := by
    intro i
    apply le_antisymm
    · exact Finset.le_sup' (fun B => robustValue M B i) (Finset.mem_univ (A n))
    · exact Finset.sup'_le _ _ (fun B _ => p3sol_core M (A n) hstepA B i)
  refine ⟨n, hn, hfix, hopt, ?_, ?_⟩
  · intro v hv j
    obtain ⟨⟨w, hw, huniq⟩, hmax⟩ := p1sol_core M
    have h1 : v = w := huniq v hv
    have h2 : maxMinValue M = w := huniq _ hmax
    rw [hopt j, h2, h1]
  · intro ε hε i
    rw [hopt i, sub_self, abs_zero]
    exact hε.le

end SatiaLave.MaxMin

open SatiaLave.MaxMin


theorem solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
    (M : UncertainMDP S D) (A : ℕ → Policy S D) (hrun : ∀ n, IsPhase2Step M (A n) (A (n + 1))) :
    (∀ n i, robustValue M (A n) i ≤ robustValue M (A (n + 1)) i) ∧
      ∃ n, n < Fintype.card (Policy S D) ∧ A (n + 1) = A n ∧ IsMaxMinOptimal M (A n) ∧
        (∀ v : S → ℝ, (∀ j, v j = eq4Op M v j) → ∀ j, robustValue M (A n) j = v j) ∧
        ∀ ε > 0, IsEpsMaxMinOptimal M ε (A n) := by
  exact goal_core M A hrun
