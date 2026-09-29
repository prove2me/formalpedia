-- Prove2me | solution 1 for SatiaLave.MaxMin.phase2_step_improves
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:46:44.973048+00:00
-- url     : https://prove2.me/submissions/e9786c3c-8b1c-4613-b7e5-a37c3d08042f

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

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

theorem solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*} [∀ i, Fintype (D i)] [∀ i, Nonempty (D i)]
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
