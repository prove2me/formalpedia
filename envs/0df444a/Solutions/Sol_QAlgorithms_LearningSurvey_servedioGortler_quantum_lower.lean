-- Prove2me | solution 1 for QAlgorithms.LearningSurvey.servedioGortler_quantum_lower
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T21:12:51.880002+00:00
-- url     : https://prove2.me/submissions/d5d7692b-3f35-4651-8ab7-6644e5fe9d38

import Definitions.Def_QAlgorithms_Defs_LearningHardInstances

set_option autoImplicit false

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms
open QAlgorithms.Learning

noncomputable section

namespace SolServedioLower

universe u

/-- Explicit Euclidean inner product `∑ z, star (u z) * v z`. -/
def vecOverlap {I : Type*} [Fintype I] (u v : I → ℂ) : ℂ :=
  ∑ z : I, star (u z) * v z

private lemma star_mul_self_eq (c : ℂ) : star c * c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm]
  simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj' c

private lemma star_mul_self_re (c : ℂ) : (star c * c).re = ‖c‖ ^ 2 := by
  rw [star_mul_self_eq, Complex.ofReal_re]

private lemma vecOverlap_self_re {I : Type*} [Fintype I] (u : I → ℂ) :
    (vecOverlap u u).re = ∑ z : I, ‖u z‖ ^ 2 := by
  unfold vecOverlap
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro z _
  exact star_mul_self_re (u z)

private lemma vecOverlap_self_eq {I : Type*} [Fintype I] (u : I → ℂ) :
    vecOverlap u u = ((∑ z : I, ‖u z‖ ^ 2 : ℝ) : ℂ) := by
  unfold vecOverlap
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl ?_
  intro z _
  exact star_mul_self_eq (u z)

private lemma vecOverlap_mulVec_of_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) (u v : I → ℂ) :
    vecOverlap ((U : Matrix I I ℂ) *ᵥ u) ((U : Matrix I I ℂ) *ᵥ v) = vecOverlap u v := by
  have hU : (U : Matrix I I ℂ)ᴴ * (U : Matrix I I ℂ) = 1 :=
    (Matrix.mem_unitaryGroup_iff').mp U.2
  change dotProduct (star ((U : Matrix I I ℂ) *ᵥ u)) ((U : Matrix I I ℂ) *ᵥ v) =
    dotProduct (star u) v
  rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU, Matrix.vecMul_one]

private lemma norm_sq_mulVec_of_unitary {I : Type*} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) (u : I → ℂ) :
    (∑ z : I, ‖((U : Matrix I I ℂ) *ᵥ u) z‖ ^ 2) = ∑ z : I, ‖u z‖ ^ 2 := by
  rw [← vecOverlap_self_re, ← vecOverlap_self_re, vecOverlap_mulVec_of_unitary U]

private lemma bool_add_eq_iff (b b' c : Bool) : (b = b' + c) ↔ (b' = b + c) := by
  revert b b' c
  decide

private lemma bool_add_invol (b c : Bool) : (b + c) + c = b := by
  revert b c
  decide

private lemma kronecker_xorOracle_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W]
    (x : ι → Bool) (v : ((ι × Bool) × W) → ℂ) (j : ι) (b : Bool) (w : W) :
    (Matrix.kronecker (xorOracle x) (1 : Matrix W W ℂ) *ᵥ v) ((j, b), w) =
      v ((j, b + x j), w) := by
  unfold Matrix.mulVec dotProduct Matrix.kronecker Matrix.kroneckerMap xorOracle
  rw [Finset.sum_eq_single ((j, b + x j), w)]
  · have hbb : (b + x j) + x j = b := bool_add_invol b (x j)
    simp [Matrix.of_apply, hbb]
  · rintro ⟨⟨j', b'⟩, w'⟩ _ hne
    simp only [Matrix.of_apply, Matrix.one_apply]
    by_cases hw : w = w'
    · subst hw
      by_cases hj : j = j'
      · subst hj
        have hb : b ≠ b' + x j := by
          intro hb
          apply hne
          have hb' : b' = b + x j := (bool_add_eq_iff b b' (x j)).mp hb
          rw [hb']
        simp [hb]
      · simp [hj]
    · simp [hw]
  · intro habs
    exact False.elim (habs (Finset.mem_univ _))

private lemma sum_prod_three' {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    {M : Type*} [AddCommMonoid M] (f : (A × B) × C → M) :
    (∑ z : (A × B) × C, f z) = ∑ a : A, ∑ b : B, ∑ c : C, f ((a, b), c) := by
  calc (∑ z : (A × B) × C, f z)
      = ∑ ab : A × B, ∑ c : C, f (ab, c) := Fintype.sum_prod_type _
    _ = ∑ a : A, ∑ b : B, ∑ c : C, f ((a, b), c) := Fintype.sum_prod_type _

private lemma sum_bool_add {M : Type*} [AddCommMonoid M] (c : Bool) (g : Bool → M) :
    (∑ b : Bool, g (b + c)) = ∑ b : Bool, g b := by
  have h00 : (false + false : Bool) = false := rfl
  have h01 : (false + true : Bool) = true := rfl
  have h10 : (true + false : Bool) = true := rfl
  have h11 : (true + true : Bool) = false := rfl
  rw [Fintype.sum_bool, Fintype.sum_bool]
  cases c <;> simp [h00, h01, h10, h11, add_comm]

private lemma norm_sq_kronecker_xorOracle {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W]
    (x : ι → Bool) (v : ((ι × Bool) × W) → ℂ) :
    (∑ z : (ι × Bool) × W, ‖(Matrix.kronecker (xorOracle x) (1 : Matrix W W ℂ) *ᵥ v) z‖ ^ 2) =
      ∑ z : (ι × Bool) × W, ‖v z‖ ^ 2 := by
  rw [sum_prod_three', sum_prod_three']
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_rhs => rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  refine Finset.sum_congr rfl ?_
  intro w _
  have h1 : (∑ b : Bool, ‖(Matrix.kronecker (xorOracle x) (1 : Matrix W W ℂ) *ᵥ v) ((j, b), w)‖ ^ 2) =
      ∑ b : Bool, ‖v ((j, b + x j), w)‖ ^ 2 := by
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [kronecker_xorOracle_mulVec]
  rw [h1]
  exact sum_bool_add (x j) (fun b => ‖v ((j, b), w)‖ ^ 2)

private lemma stateAt_zero_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (O : Matrix (ι × Bool) (ι × Bool) ℂ) :
    A.stateAt O 0 = act (A.U 0 : Matrix _ _ ℂ) A.start := by
  simp [QueryAlg.stateAt]

private lemma stateAt_succ_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (O : Matrix (ι × Bool) (ι × Bool) ℂ) (t : Fin T) :
    A.stateAt O t.succ =
      act (A.U t.succ : Matrix _ _ ℂ)
        (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (A.stateAt O t.castSucc)) := by
  simp [QueryAlg.stateAt]

private lemma stateAt_norm_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (x : ι → Bool) (t : Fin (T + 1)) :
    (∑ z : (ι × Bool) × W, ‖(A.stateAt (xorOracle x) t).ofLp z‖ ^ 2) = 1 := by
  refine Fin.induction ?_ ?_ t
  · rw [stateAt_zero_eq]
    simp only [act, WithLp.ofLp_toLp]
    rw [norm_sq_mulVec_of_unitary (A.U 0)]
    have hinit := A.start_unit
    have hnorm : ‖A.start‖ ^ 2 = ∑ z : (ι × Bool) × W, ‖A.start.ofLp z‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq A.start
    linarith [show ‖A.start‖ ^ 2 = 1 by rw [hinit]; ring]
  · intro s ih
    rw [stateAt_succ_eq]
    simp only [act, WithLp.ofLp_toLp]
    rw [norm_sq_mulVec_of_unitary (A.U s.succ), norm_sq_kronecker_xorOracle]
    exact ih

/-- Weight of `A.stateAt (xorOracle x) t` on query index `i`. -/
def idxWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (x : ι → Bool) (t : Fin (T + 1)) (i : ι) : ℝ :=
  ∑ b : Bool, ∑ w : W, ‖(A.stateAt (xorOracle x) t).ofLp ((i, b), w)‖ ^ 2

private lemma idxWeight_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (x : ι → Bool) (t : Fin (T + 1)) (i : ι) :
    0 ≤ idxWeight A x t i := by
  unfold idxWeight
  positivity

private lemma sum_idxWeight_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (x : ι → Bool) (t : Fin (T + 1)) :
    (∑ i : ι, idxWeight A x t i) = 1 := by
  unfold idxWeight
  exact (sum_prod_three' (fun z : (ι × Bool) × W =>
    ‖(A.stateAt (xorOracle x) t).ofLp z‖ ^ 2)).symm.trans (stateAt_norm_sq A x t)

private lemma sum_idxWeight_subset_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (x : ι → Bool) (t : Fin (T + 1)) (S : Finset ι) :
    (∑ i ∈ S, idxWeight A x t i) ≤ 1 := by
  calc (∑ i ∈ S, idxWeight A x t i)
      ≤ ∑ i : ι, idxWeight A x t i := by
        refine Finset.sum_le_univ_sum_of_nonneg ?_
        intro i
        exact idxWeight_nonneg A x t i
    _ = 1 := sum_idxWeight_eq_one A x t

private lemma am_gm_sqrt {a b u v : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) * (u * v) ≤ (a * u ^ 2 + b * v ^ 2) / 2 := by
  rw [Real.sqrt_mul ha]
  have hsq : 0 ≤ (Real.sqrt a * u - Real.sqrt b * v) ^ 2 := sq_nonneg _
  have ha2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith

/-- Set of coordinates where `x` and `y` differ. -/
def diffSet {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι → Bool) : Finset ι :=
  Finset.univ.filter (fun i : ι => y i ≠ x i)

private lemma overlap_step_diff_bound_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (x y : ι → Bool) (t : Fin T)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) *
      ‖vecOverlap (A.stateAt (xorOracle x) t.succ).ofLp
          (A.stateAt (xorOracle y) t.succ).ofLp -
        vecOverlap (A.stateAt (xorOracle x) t.castSucc).ofLp
          (A.stateAt (xorOracle y) t.castSucc).ofLp‖ ≤
      ∑ i ∈ diffSet x y,
        (a * idxWeight A x t.castSucc i + b * idxWeight A y t.castSucc i) := by
  set u := (A.stateAt (xorOracle x) t.castSucc).ofLp
  set v := (A.stateAt (xorOracle y) t.castSucc).ofLp
  have hstep_x : (A.stateAt (xorOracle x) t.succ).ofLp =
      (A.U t.succ : Matrix _ _ ℂ) *ᵥ (Matrix.kronecker (xorOracle x) (1 : Matrix W W ℂ) *ᵥ u) := by
    rw [stateAt_succ_eq]
    rfl
  have hstep_y : (A.stateAt (xorOracle y) t.succ).ofLp =
      (A.U t.succ : Matrix _ _ ℂ) *ᵥ (Matrix.kronecker (xorOracle y) (1 : Matrix W W ℂ) *ᵥ v) := by
    rw [stateAt_succ_eq]
    rfl
  rw [hstep_x, hstep_y, vecOverlap_mulVec_of_unitary (A.U t.succ)]
  have hdiff :
      vecOverlap (Matrix.kronecker (xorOracle x) (1 : Matrix W W ℂ) *ᵥ u)
        (Matrix.kronecker (xorOracle y) (1 : Matrix W W ℂ) *ᵥ v) -
        vecOverlap u v =
      ∑ i ∈ diffSet x y,
        ((∑ b0 : Bool, ∑ w : W,
          star (u ((i, b0 + x i), w)) * v ((i, b0 + y i), w)) -
        (∑ b0 : Bool, ∑ w : W,
          star (u ((i, b0), w)) * v ((i, b0), w))) := by
    unfold vecOverlap
    rw [sum_prod_three', sum_prod_three', ← Finset.sum_sub_distrib]
    rw [← Finset.sum_subset (Finset.subset_univ (diffSet x y))]
    · refine Finset.sum_congr rfl ?_
      intro i _
      congr 1
      refine Finset.sum_congr rfl ?_
      intro b0 _
      refine Finset.sum_congr rfl ?_
      intro w _
      rw [kronecker_xorOracle_mulVec, kronecker_xorOracle_mulVec]
    · intro j _ hj
      simp only [diffSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hj
      have h1 : (∑ b0 : Bool, ∑ w : W,
          star ((Matrix.kronecker (xorOracle x) (1 : Matrix W W ℂ) *ᵥ u) ((j, b0), w)) *
            (Matrix.kronecker (xorOracle y) (1 : Matrix W W ℂ) *ᵥ v) ((j, b0), w)) =
          ∑ b0 : Bool, ∑ w : W, star (u ((j, b0), w)) * v ((j, b0), w) := by
        have h2 : (∑ b0 : Bool, ∑ w : W,
            star ((Matrix.kronecker (xorOracle x) (1 : Matrix W W ℂ) *ᵥ u) ((j, b0), w)) *
              (Matrix.kronecker (xorOracle y) (1 : Matrix W W ℂ) *ᵥ v) ((j, b0), w)) =
            ∑ b0 : Bool, ∑ w : W,
              star (u ((j, b0 + x j), w)) * v ((j, b0 + x j), w) := by
          refine Finset.sum_congr rfl ?_
          intro b0 _
          refine Finset.sum_congr rfl ?_
          intro w _
          rw [kronecker_xorOracle_mulVec, kronecker_xorOracle_mulVec, hj]
        rw [h2, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        conv_rhs => rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        refine Finset.sum_congr rfl ?_
        intro w _
        exact sum_bool_add (x j) (fun b0 => star (u ((j, b0), w)) * v ((j, b0), w))
      rw [h1, sub_self]
  rw [hdiff]
  have htri :
      Real.sqrt (a * b) *
        ‖∑ i ∈ diffSet x y,
          ((∑ b0 : Bool, ∑ w : W,
            star (u ((i, b0 + x i), w)) * v ((i, b0 + y i), w)) -
          (∑ b0 : Bool, ∑ w : W,
            star (u ((i, b0), w)) * v ((i, b0), w)))‖ ≤
      ∑ i ∈ diffSet x y,
        Real.sqrt (a * b) *
          ‖(∑ b0 : Bool, ∑ w : W,
              star (u ((i, b0 + x i), w)) * v ((i, b0 + y i), w)) -
            (∑ b0 : Bool, ∑ w : W,
              star (u ((i, b0), w)) * v ((i, b0), w))‖ := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.sqrt_nonneg _)
  refine le_trans htri (Finset.sum_le_sum ?_)
  intro i _
  have hnorm :
      ‖(∑ b0 : Bool, ∑ w : W,
          star (u ((i, b0 + x i), w)) * v ((i, b0 + y i), w)) -
        (∑ b0 : Bool, ∑ w : W,
          star (u ((i, b0), w)) * v ((i, b0), w))‖ ≤
      (∑ b0 : Bool, ∑ w : W,
          ‖u ((i, b0 + x i), w)‖ * ‖v ((i, b0 + y i), w)‖) +
        (∑ b0 : Bool, ∑ w : W,
          ‖u ((i, b0), w)‖ * ‖v ((i, b0), w)‖) := by
    refine le_trans (norm_sub_le _ _) (add_le_add ?_ ?_)
    · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro b0 _
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro w _
      rw [norm_mul, norm_star]
    · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro b0 _
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
      intro w _
      rw [norm_mul, norm_star]
  have hmul := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg (a * b))
  rw [mul_add] at hmul
  have hsum1 :
      Real.sqrt (a * b) *
        (∑ b0 : Bool, ∑ w : W,
          ‖u ((i, b0 + x i), w)‖ * ‖v ((i, b0 + y i), w)‖) ≤
        (a * idxWeight A x t.castSucc i + b * idxWeight A y t.castSucc i) / 2 := by
    rw [Finset.mul_sum]
    have hle :
        (∑ b0 : Bool, Real.sqrt (a * b) * ∑ w : W,
            ‖u ((i, b0 + x i), w)‖ * ‖v ((i, b0 + y i), w)‖) ≤
          ∑ b0 : Bool, ∑ w : W,
            (a * ‖u ((i, b0 + x i), w)‖ ^ 2 + b * ‖v ((i, b0 + y i), w)‖ ^ 2) / 2 := by
      refine Finset.sum_le_sum ?_
      intro b0 _
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro w _
      exact am_gm_sqrt ha hb
    refine le_trans hle ?_
    have hrew_u :
        (∑ b0 : Bool, ∑ w : W, ‖u ((i, b0 + x i), w)‖ ^ 2) = idxWeight A x t.castSucc i := by
      unfold idxWeight
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      conv_rhs => rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      refine Finset.sum_congr rfl ?_
      intro w _
      exact sum_bool_add (x i) (fun b0 => ‖u ((i, b0), w)‖ ^ 2)
    have hrew_v :
        (∑ b0 : Bool, ∑ w : W, ‖v ((i, b0 + y i), w)‖ ^ 2) = idxWeight A y t.castSucc i := by
      unfold idxWeight
      rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      conv_rhs => rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      refine Finset.sum_congr rfl ?_
      intro w _
      exact sum_bool_add (y i) (fun b0 => ‖v ((i, b0), w)‖ ^ 2)
    have hlin :
        (∑ b0 : Bool, ∑ w : W,
          (a * ‖u ((i, b0 + x i), w)‖ ^ 2 + b * ‖v ((i, b0 + y i), w)‖ ^ 2) / 2) =
        (a * (∑ b0 : Bool, ∑ w : W, ‖u ((i, b0 + x i), w)‖ ^ 2) +
          b * (∑ b0 : Bool, ∑ w : W, ‖v ((i, b0 + y i), w)‖ ^ 2)) / 2 := by
      simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    rw [hlin, hrew_u, hrew_v]
  have hsum2 :
      Real.sqrt (a * b) *
        (∑ b0 : Bool, ∑ w : W, ‖u ((i, b0), w)‖ * ‖v ((i, b0), w)‖) ≤
        (a * idxWeight A x t.castSucc i + b * idxWeight A y t.castSucc i) / 2 := by
    rw [Finset.mul_sum]
    have hle :
        (∑ b0 : Bool, Real.sqrt (a * b) * ∑ w : W, ‖u ((i, b0), w)‖ * ‖v ((i, b0), w)‖) ≤
          ∑ b0 : Bool, ∑ w : W,
            (a * ‖u ((i, b0), w)‖ ^ 2 + b * ‖v ((i, b0), w)‖ ^ 2) / 2 := by
      refine Finset.sum_le_sum ?_
      intro b0 _
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum ?_
      intro w _
      exact am_gm_sqrt ha hb
    refine le_trans hle ?_
    have hlin :
        (∑ b0 : Bool, ∑ w : W, (a * ‖u ((i, b0), w)‖ ^ 2 + b * ‖v ((i, b0), w)‖ ^ 2) / 2) =
        (a * idxWeight A x t.castSucc i + b * idxWeight A y t.castSucc i) / 2 := by
      unfold idxWeight
      simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum, u, v]
    rw [hlin]
  linarith

private lemma fin_sum_telescope_bound {T : ℕ} (f : Fin (T + 1) → ℂ) (g : Fin T → ℝ)
    (hf0 : f 0 = 1) (hstep : ∀ t : Fin T, ‖f t.succ - f t.castSucc‖ ≤ g t) :
    ‖(1 : ℂ) - f (Fin.last T)‖ ≤ ∑ t : Fin T, g t := by
  induction T with
  | zero =>
    have hlast : (Fin.last 0 : Fin 1) = 0 := rfl
    rw [hlast, hf0, sub_self, norm_zero]
    simp
  | succ T ih =>
    rw [Fin.sum_univ_castSucc]
    have hih := ih (fun i => f i.castSucc) (fun i => g i.castSucc) hf0 (fun t => by
      simpa using hstep t.castSucc)
    have htri :
        ‖(1 : ℂ) - f (Fin.last (T + 1))‖ ≤
          ‖(1 : ℂ) - f (Fin.last T).castSucc‖ +
            ‖f (Fin.last T).succ - f (Fin.last T).castSucc‖ := by
      have hlast : (Fin.last (T + 1) : Fin (T + 2)) = (Fin.last T).succ := rfl
      rw [hlast]
      have hsub :
          (1 : ℂ) - f (Fin.last T).succ =
            ((1 : ℂ) - f (Fin.last T).castSucc) -
              (f (Fin.last T).succ - f (Fin.last T).castSucc) := by ring
      rw [hsub]
      exact norm_sub_le _ _
    have hlast_step := hstep (Fin.last T)
    linarith

private lemma overlap_final_diff_bound_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (x y : ι → Bool)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) *
      ‖(1 : ℂ) - vecOverlap (A.finalState (xorOracle x)).ofLp
          (A.finalState (xorOracle y)).ofLp‖ ≤
      ∑ t : Fin T, ∑ i ∈ diffSet x y,
        (a * idxWeight A x t.castSucc i + b * idxWeight A y t.castSucc i) := by
  let f : Fin (T + 1) → ℂ := fun t =>
    vecOverlap (A.stateAt (xorOracle x) t).ofLp (A.stateAt (xorOracle y) t).ofLp
  have hf0 : f 0 = 1 := by
    dsimp [f]
    have h0 : A.stateAt (xorOracle y) 0 = A.stateAt (xorOracle x) 0 := rfl
    rw [h0, vecOverlap_self_eq, stateAt_norm_sq]
    simp
  have htel :
      ‖(1 : ℂ) - f (Fin.last T)‖ ≤
        ∑ t : Fin T, ‖f t.succ - f t.castSucc‖ :=
    fin_sum_telescope_bound f (fun t => ‖f t.succ - f t.castSucc‖) hf0 (fun _ => le_rfl)
  have hmul := mul_le_mul_of_nonneg_left htel (Real.sqrt_nonneg (a * b))
  rw [Finset.mul_sum] at hmul
  refine le_trans hmul (Finset.sum_le_sum ?_)
  intro t _
  exact overlap_step_diff_bound_set A x y t ha hb

private lemma prob_eq_norm_sq {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : EuclideanSpace ℂ I) (z : I) :
    prob ψ z = ‖ψ.ofLp z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

private lemma outputProb_eq_sum_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (O : Matrix (ι × Bool) (ι × Bool) ℂ)
    (out : (ι × Bool) × W → (ι → Bool)) (c : ι → Bool) :
    A.outputProb O out c =
      ∑ z : (ι × Bool) × W, if out z = c then ‖(A.finalState O).ofLp z‖ ^ 2 else 0 := by
  unfold QueryAlg.outputProb probEvent
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [prob_eq_norm_sq]

private lemma sum_outputProb_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (x : ι → Bool)
    (out : (ι × Bool) × W → (ι → Bool)) (C' : Finset (ι → Bool)) :
    (∑ c ∈ C', A.outputProb (xorOracle x) out c) ≤ 1 := by
  have hrew : (∑ c ∈ C', A.outputProb (xorOracle x) out c) =
      ∑ z : (ι × Bool) × W,
        ∑ c ∈ C', (if out z = c then ‖(A.finalState (xorOracle x)).ofLp z‖ ^ 2 else 0) := by
    simp_rw [outputProb_eq_sum_ite]
    rw [Finset.sum_comm]
  rw [hrew, ← stateAt_norm_sq A x (Fin.last T)]
  refine Finset.sum_le_sum ?_
  intro z _
  by_cases hz : out z ∈ C'
  · rw [Finset.sum_eq_single (out z)]
    · simp [QueryAlg.finalState]
    · intro c _ hne
      exact if_neg hne.symm
    · intro habs
      exact False.elim (habs hz)
  · rw [Finset.sum_eq_zero]
    · exact sq_nonneg _
    · intro c hc
      have hne : out z ≠ c := fun h => hz (h ▸ hc)
      exact if_neg hne

private lemma overlap_dist_lower_vs_ref {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (out : (ι × Bool) × W → (ι → Bool))
    (x c : ι → Bool) (hacc_c : A.outputProb (xorOracle c) out c ≥ 2 / 3) :
    (19 / 180 : ℝ) - (11 / 60 : ℝ) * A.outputProb (xorOracle x) out c ≤
      ‖(1 : ℂ) - vecOverlap (A.finalState (xorOracle x)).ofLp
          (A.finalState (xorOracle c)).ofLp‖ := by
  set u := (A.finalState (xorOracle x)).ofLp
  set v := (A.finalState (xorOracle c)).ofLp
  have hu_norm : (∑ z : (ι × Bool) × W, ‖u z‖ ^ 2) = 1 := stateAt_norm_sq A x (Fin.last T)
  have hv_norm : (∑ z : (ι × Bool) × W, ‖v z‖ ^ 2) = 1 := stateAt_norm_sq A c (Fin.last T)
  have hv_bad : (∑ z : (ι × Bool) × W, if out z = c then (0 : ℝ) else ‖v z‖ ^ 2) ≤ 1 / 3 := by
    have hsplit :
        A.outputProb (xorOracle c) out c +
          (∑ z : (ι × Bool) × W, if out z = c then (0 : ℝ) else ‖v z‖ ^ 2) =
        ∑ z : (ι × Bool) × W, ‖v z‖ ^ 2 := by
      rw [outputProb_eq_sum_ite, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro z _
      split_ifs <;> ring
    linarith
  have hu_c : (∑ z : (ι × Bool) × W, if out z = c then ‖u z‖ ^ 2 else (0 : ℝ)) =
      A.outputProb (xorOracle x) out c := by
    rw [outputProb_eq_sum_ite]
  have hpt : ∀ z : (ι × Bool) × W,
      ‖star (u z) * v z‖ ≤
        (5 / 12 : ℝ) * ‖u z‖ ^ 2 + (5 / 12 : ℝ) * ‖v z‖ ^ 2 +
          (11 / 60 : ℝ) * (if out z = c then ‖u z‖ ^ 2 else (0 : ℝ)) +
          (11 / 60 : ℝ) * (if out z = c then (0 : ℝ) else ‖v z‖ ^ 2) := by
    intro z
    rw [norm_mul, norm_star]
    by_cases hzc : out z = c
    · simp only [hzc, ↓reduceIte]
      nlinarith [sq_nonneg (6 * ‖u z‖ - 5 * ‖v z‖)]
    · simp only [hzc, ↓reduceIte]
      nlinarith [sq_nonneg (5 * ‖u z‖ - 6 * ‖v z‖)]
  have hov_le : ‖vecOverlap u v‖ ≤ (161 / 180 : ℝ) + (11 / 60 : ℝ) * A.outputProb (xorOracle x) out c := by
    have h1 : ‖vecOverlap u v‖ ≤ ∑ z : (ι × Bool) × W, ‖star (u z) * v z‖ :=
      norm_sum_le _ _
    have h2 : (∑ z : (ι × Bool) × W, ‖star (u z) * v z‖) ≤
        ∑ z : (ι × Bool) × W,
          ((5 / 12 : ℝ) * ‖u z‖ ^ 2 + (5 / 12 : ℝ) * ‖v z‖ ^ 2 +
            (11 / 60 : ℝ) * (if out z = c then ‖u z‖ ^ 2 else (0 : ℝ)) +
            (11 / 60 : ℝ) * (if out z = c then (0 : ℝ) else ‖v z‖ ^ 2)) :=
      Finset.sum_le_sum (fun z _ => hpt z)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    linarith
  have htri : (1 : ℝ) - ‖vecOverlap u v‖ ≤ ‖(1 : ℂ) - vecOverlap u v‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (vecOverlap u v)
    simpa using h
  linarith

/-- Majority concept on `C'`. -/
def bMaj {ι : Type*} (C' : Finset (ι → Bool)) (i : ι) : Bool :=
  if (C'.filter (fun c => c i = false)).card ≤ (C'.filter (fun c => c i = true)).card then
    true
  else
    false

private lemma filter_ne_bMaj_card_le {ι : Type*} [Fintype ι]
    (C' : Finset (ι → Bool)) (i : ι) :
    ((C'.filter (fun c => c i ≠ bMaj C' i)).card : ℝ) ≤ gammaPrime C' * (C'.card : ℝ) := by
  have hle_sup : min (gammaFrac C' i false) (gammaFrac C' i true) ≤ gammaPrime C' := by
    unfold gammaPrime
    exact le_ciSup (Finite.bddAbove_range (fun j : ι => min (gammaFrac C' j false) (gammaFrac C' j true))) i
  have hcard_nonneg : (0 : ℝ) ≤ (C'.card : ℝ) := Nat.cast_nonneg _
  by_cases hcard0 : C'.card = 0
  · rw [Finset.card_eq_zero.mp hcard0]
    simp
  · have hcard_pos : (0 : ℝ) < (C'.card : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hcard0)
    by_cases hcmp : (C'.filter (fun c => c i = false)).card ≤ (C'.filter (fun c => c i = true)).card
    · have hb : bMaj C' i = true := by simp [bMaj, hcmp]
      have hfilt : C'.filter (fun c => c i ≠ bMaj C' i) = C'.filter (fun c => c i = false) := by
        ext c
        simp [hb]
      rw [hfilt]
      have hmin : min (gammaFrac C' i false) (gammaFrac C' i true) = gammaFrac C' i false := by
        refine min_eq_left ?_
        unfold gammaFrac
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcmp) hcard_nonneg
      have hfrac : gammaFrac C' i false ≤ gammaPrime C' := hmin ▸ hle_sup
      unfold gammaFrac at hfrac
      exact (div_le_iff₀ hcard_pos).mp hfrac
    · have hb : bMaj C' i = false := by simp [bMaj, hcmp]
      have hfilt : C'.filter (fun c => c i ≠ bMaj C' i) = C'.filter (fun c => c i = true) := by
        ext c
        simp [hb]
      rw [hfilt]
      have hcmp' : (C'.filter (fun c => c i = true)).card ≤ (C'.filter (fun c => c i = false)).card :=
        Nat.le_of_not_le hcmp
      have hmin : min (gammaFrac C' i false) (gammaFrac C' i true) = gammaFrac C' i true := by
        refine min_eq_right ?_
        unfold gammaFrac
        exact div_le_div_of_nonneg_right (by exact_mod_cast hcmp') hcard_nonneg
      have hfrac : gammaFrac C' i true ≤ gammaPrime C' := hmin ▸ hle_sup
      unfold gammaFrac at hfrac
      exact (div_le_iff₀ hcard_pos).mp hfrac

private lemma gammaPrime_pos_of_two_le_card {ι : Type*} [Fintype ι]
    {C' : Finset (ι → Bool)} (hC' : 2 ≤ C'.card) :
    0 < gammaPrime C' := by
  have h1lt : 1 < C'.card := hC'
  obtain ⟨c₁, c₂, hc₁, hc₂, hne⟩ := Finset.one_lt_card_iff.mp h1lt
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hne
  have hle_sup : min (gammaFrac C' i₀ false) (gammaFrac C' i₀ true) ≤ gammaPrime C' := by
    unfold gammaPrime
    exact le_ciSup (Finite.bddAbove_range (fun j : ι => min (gammaFrac C' j false) (gammaFrac C' j true))) i₀
  have hcard_pos : (0 : ℝ) < (C'.card : ℝ) := by positivity
  have hfalse_pos : 0 < gammaFrac C' i₀ false := by
    unfold gammaFrac
    refine div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ?_)) hcard_pos
    rcases h1 : c₁ i₀ with _ | _
    · exact ⟨c₁, Finset.mem_filter.mpr ⟨hc₁, h1⟩⟩
    · have h2 : c₂ i₀ = false := by
        rcases h2' : c₂ i₀ with _ | _
        · rfl
        · exact False.elim (hi₀ (h1.trans h2'.symm))
      exact ⟨c₂, Finset.mem_filter.mpr ⟨hc₂, h2⟩⟩
  have htrue_pos : 0 < gammaFrac C' i₀ true := by
    unfold gammaFrac
    refine div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ?_)) hcard_pos
    rcases h1 : c₁ i₀ with _ | _
    · have h2 : c₂ i₀ = true := by
        rcases h2' : c₂ i₀ with _ | _
        · exact False.elim (hi₀ (h1.trans h2'.symm))
        · rfl
      exact ⟨c₂, Finset.mem_filter.mpr ⟨hc₂, h2⟩⟩
    · exact ⟨c₁, Finset.mem_filter.mpr ⟨hc₁, h1⟩⟩
  exact lt_of_lt_of_le (lt_min hfalse_pos htrue_pos) hle_sup

private lemma quantum_lower_gamma {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Finset (ι → Bool)} (hC : 2 ≤ C.card)
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (out : (ι × Bool) × W → (ι → Bool))
    (hLearn : IsQExactLearner A out C) :
    (1 / 144 : ℝ) * (1 / Real.sqrt (gammaParam C)) ≤ (T : ℝ) := by
  let SubType := {C' : Finset (ι → Bool) // C' ⊆ C ∧ 2 ≤ C'.card}
  have : Nonempty SubType := ⟨⟨C, Finset.Subset.refl C, hC⟩⟩
  obtain ⟨⟨C', hC'sub, hC'card⟩, hC'eq⟩ :=
    exists_eq_ciInf_of_finite (f := fun s : SubType => gammaPrime s.1)
  have hgamma_eq : gammaPrime C' = gammaParam C := hC'eq
  have hgamma_pos : 0 < gammaParam C := hgamma_eq ▸ gammaPrime_pos_of_two_le_card hC'card
  have hgamma_nonneg : 0 ≤ gammaParam C := le_of_lt hgamma_pos
  have hsqrt_pos : 0 < Real.sqrt (gammaParam C) := Real.sqrt_pos.mpr hgamma_pos
  set x := bMaj C'
  set g := gammaParam C
  have hcard_real : (2 : ℝ) ≤ (C'.card : ℝ) := by exact_mod_cast hC'card
  have hcard_pos : (0 : ℝ) < (C'.card : ℝ) := by linarith
  have hsum_lhs :
      (1 / 72 : ℝ) * (C'.card : ℝ) ≤
        ∑ c ∈ C',
          ‖(1 : ℂ) - vecOverlap (A.finalState (xorOracle x)).ofLp
              (A.finalState (xorOracle c)).ofLp‖ := by
    have h1 :
        ∑ c ∈ C', ((19 / 180 : ℝ) - (11 / 60 : ℝ) * A.outputProb (xorOracle x) out c) ≤
          ∑ c ∈ C',
            ‖(1 : ℂ) - vecOverlap (A.finalState (xorOracle x)).ofLp
                (A.finalState (xorOracle c)).ofLp‖ := by
      refine Finset.sum_le_sum ?_
      intro c hc
      exact overlap_dist_lower_vs_ref A out x c (hLearn c (hC'sub hc))
    have h2 :
        ∑ c ∈ C', ((19 / 180 : ℝ) - (11 / 60 : ℝ) * A.outputProb (xorOracle x) out c) =
          (19 / 180 : ℝ) * (C'.card : ℝ) -
            (11 / 60 : ℝ) * ∑ c ∈ C', A.outputProb (xorOracle x) out c := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      ring
    have hprob := sum_outputProb_le_one A x out C'
    linarith
  have hsum_step : ∀ t : Fin T,
      (∑ c ∈ C', ∑ i ∈ diffSet x c,
        (1 * idxWeight A x t.castSucc i + g * idxWeight A c t.castSucc i)) ≤
        2 * g * (C'.card : ℝ) := by
    intro t
    have hsplit :
        (∑ c ∈ C', ∑ i ∈ diffSet x c,
          (1 * idxWeight A x t.castSucc i + g * idxWeight A c t.castSucc i)) =
        (∑ c ∈ C', ∑ i ∈ diffSet x c, idxWeight A x t.castSucc i) +
          (∑ c ∈ C', ∑ i ∈ diffSet x c, g * idxWeight A c t.castSucc i) := by
      simp only [one_mul, Finset.sum_add_distrib]
    have hterm1 :
        (∑ c ∈ C', ∑ i ∈ diffSet x c, idxWeight A x t.castSucc i) ≤ g * (C'.card : ℝ) := by
      have hswap :
          (∑ c ∈ C', ∑ i ∈ diffSet x c, idxWeight A x t.castSucc i) =
            ∑ i : ι, idxWeight A x t.castSucc i *
              ((C'.filter (fun c => c i ≠ x i)).card : ℝ) := by
        trans (∑ c ∈ C', ∑ i : ι, if c i ≠ x i then idxWeight A x t.castSucc i else 0)
        · refine Finset.sum_congr rfl ?_
          intro c _
          rw [← Finset.sum_filter]
          rfl
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [← Finset.sum_filter]
          simp [mul_comm]
      rw [hswap]
      calc (∑ i : ι, idxWeight A x t.castSucc i *
              ((C'.filter (fun c => c i ≠ x i)).card : ℝ))
          ≤ ∑ i : ι, idxWeight A x t.castSucc i * (g * (C'.card : ℝ)) := by
            refine Finset.sum_le_sum ?_
            intro i _
            refine mul_le_mul_of_nonneg_left ?_ (idxWeight_nonneg A x t.castSucc i)
            have hmaj := filter_ne_bMaj_card_le C' i
            simpa [x, g, hgamma_eq] using hmaj
        _ = (∑ i : ι, idxWeight A x t.castSucc i) * (g * (C'.card : ℝ)) := by
            rw [← Finset.sum_mul]
        _ = g * (C'.card : ℝ) := by
            rw [sum_idxWeight_eq_one, one_mul]
    have hterm2 :
        (∑ c ∈ C', ∑ i ∈ diffSet x c, g * idxWeight A c t.castSucc i) ≤ g * (C'.card : ℝ) := by
      calc (∑ c ∈ C', ∑ i ∈ diffSet x c, g * idxWeight A c t.castSucc i)
          = ∑ c ∈ C', g * ∑ i ∈ diffSet x c, idxWeight A c t.castSucc i := by
            refine Finset.sum_congr rfl ?_
            intro c _
            rw [← Finset.mul_sum]
        _ ≤ ∑ _c ∈ C', g * 1 := by
            refine Finset.sum_le_sum ?_
            intro c _
            exact mul_le_mul_of_nonneg_left
              (sum_idxWeight_subset_le_one A c t.castSucc (diffSet x c)) hgamma_nonneg
        _ = g * (C'.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    linarith
  have hsum_all :
      Real.sqrt g *
        (∑ c ∈ C',
          ‖(1 : ℂ) - vecOverlap (A.finalState (xorOracle x)).ofLp
              (A.finalState (xorOracle c)).ofLp‖) ≤
      (T : ℝ) * (2 * g * (C'.card : ℝ)) := by
    rw [Finset.mul_sum]
    calc (∑ c ∈ C',
            Real.sqrt g *
              ‖(1 : ℂ) - vecOverlap (A.finalState (xorOracle x)).ofLp
                  (A.finalState (xorOracle c)).ofLp‖)
        ≤ ∑ c ∈ C', ∑ t : Fin T, ∑ i ∈ diffSet x c,
            (1 * idxWeight A x t.castSucc i + g * idxWeight A c t.castSucc i) := by
          refine Finset.sum_le_sum ?_
          intro c _
          have h := overlap_final_diff_bound_set A x c (by norm_num : (0 : ℝ) ≤ 1) hgamma_nonneg
          simpa [one_mul] using h
      _ = ∑ t : Fin T, ∑ c ∈ C', ∑ i ∈ diffSet x c,
            (1 * idxWeight A x t.castSucc i + g * idxWeight A c t.castSucc i) := by
          rw [Finset.sum_comm]
      _ ≤ ∑ _t : Fin T, (2 * g * (C'.card : ℝ)) :=
          Finset.sum_le_sum (fun t _ => hsum_step t)
      _ = (T : ℝ) * (2 * g * (C'.card : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmul_lhs := mul_le_mul_of_nonneg_left hsum_lhs (le_of_lt hsqrt_pos)
  have hcomb : Real.sqrt g * ((1 / 72 : ℝ) * (C'.card : ℝ)) ≤ (T : ℝ) * (2 * g * (C'.card : ℝ)) :=
    le_trans hmul_lhs hsum_all
  have hg_sq : Real.sqrt g * Real.sqrt g = g := Real.mul_self_sqrt hgamma_nonneg
  have hcomb' :
      (1 / 72 : ℝ) * (Real.sqrt g * (C'.card : ℝ)) ≤
        (2 * (T : ℝ) * Real.sqrt g) * (Real.sqrt g * (C'.card : ℝ)) := by
    calc (1 / 72 : ℝ) * (Real.sqrt g * (C'.card : ℝ))
        = Real.sqrt g * ((1 / 72 : ℝ) * (C'.card : ℝ)) := by ring
      _ ≤ (T : ℝ) * (2 * g * (C'.card : ℝ)) := hcomb
      _ = (T : ℝ) * (2 * (Real.sqrt g * Real.sqrt g) * (C'.card : ℝ)) := by rw [hg_sq]
      _ = (2 * (T : ℝ) * Real.sqrt g) * (Real.sqrt g * (C'.card : ℝ)) := by ring
  have hprod_pos : 0 < Real.sqrt g * (C'.card : ℝ) := mul_pos hsqrt_pos hcard_pos
  have hdiv : (1 / 144 : ℝ) ≤ (T : ℝ) * Real.sqrt g := by
    have h1 := le_of_mul_le_mul_right hcomb' hprod_pos
    linarith
  rw [mul_one_div]
  exact (div_le_iff₀ hsqrt_pos).mpr hdiv

/-! ### Part 2: Information-theoretic lower bound `(log |C|) / n = O(T)` -/

/-- Coordinate-projected query action on `((ι × Bool) × W)`: acts on query index `i` with bit `bVal`
and zeroes out all other query indices `j ≠ i`. -/
def projOp {ι : Type*} [DecidableEq ι] {W : Type u}
    (i : ι) (bVal : Bool) (u : EuclideanSpace ℂ ((ι × Bool) × W)) :
    EuclideanSpace ℂ ((ι × Bool) × W) :=
  WithLp.toLp 2 (fun z : (ι × Bool) × W =>
    if z.1.1 = i then u.ofLp ((i, z.1.2 + bVal), z.2) else 0)

private lemma act_add {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (u v : EuclideanSpace ℂ I) :
    act M (u + v) = act M u + act M v := by
  ext z
  simp [act, Matrix.mulVec_add]

private lemma act_smul {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (r : ℂ) (u : EuclideanSpace ℂ I) :
    act M (r • u) = r • act M u := by
  ext z
  simp [act, Matrix.mulVec_smul]

private lemma act_zero {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) :
    act M (0 : EuclideanSpace ℂ I) = 0 := by
  ext z
  simp [act]

private lemma act_sum {I J : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (s : Finset J) (f : J → EuclideanSpace ℂ I) :
    act M (∑ j ∈ s, f j) = ∑ j ∈ s, act M (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [act_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, act_add, ih, Finset.sum_insert ha]

private lemma act_kronecker_xorOracle_eq_sum_projOp {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W]
    (c : ι → Bool) (u : EuclideanSpace ℂ ((ι × Bool) × W)) :
    act (Matrix.kronecker (xorOracle c) (1 : Matrix W W ℂ)) u =
      ∑ i : ι, projOp i (c i) u := by
  ext ⟨⟨j, b⟩, w⟩
  simp only [act, projOp, WithLp.ofLp_toLp, WithLp.ofLp_sum, Finset.sum_apply]
  rw [kronecker_xorOracle_mulVec]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    exact if_neg hij.symm
  · intro habs
    exact False.elim (habs (Finset.mem_univ _))

/-- Finite set of spanning vectors at query step `s : Fin (T + 1)`. -/
def stateSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (s : Fin (T + 1)) :
    Finset (EuclideanSpace ℂ ((ι × Bool) × W)) := by
  classical
  exact Fin.induction
    ({act (A.U 0 : Matrix _ _ ℂ) A.start})
    (fun t prev =>
      prev.biUnion (fun u =>
        (Finset.univ : Finset (ι × Bool)).image (fun p =>
          act (A.U t.succ : Matrix _ _ ℂ) (projOp p.1 p.2 u))))
    s

private lemma stateSet_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) :
    stateSet A 0 = {act (A.U 0 : Matrix _ _ ℂ) A.start} := by
  simp [stateSet]

private lemma stateSet_succ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (t : Fin T) :
    stateSet A t.succ = by
      classical
      exact (stateSet A t.castSucc).biUnion (fun u =>
        (Finset.univ : Finset (ι × Bool)).image (fun p =>
          act (A.U t.succ : Matrix _ _ ℂ) (projOp p.1 p.2 u))) := by
  simp [stateSet]

private lemma card_stateSet_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (s : Fin (T + 1)) :
    (stateSet A s).card ≤ (Fintype.card ι * 2) ^ (s : ℕ) := by
  classical
  refine Fin.induction ?_ ?_ s
  · rw [stateSet_zero]
    simp
  · intro t ih
    rw [stateSet_succ, Fin.val_succ, pow_succ]
    calc ((stateSet A t.castSucc).biUnion (fun u =>
            (Finset.univ : Finset (ι × Bool)).image (fun p =>
              act (A.U t.succ : Matrix _ _ ℂ) (projOp p.1 p.2 u)))).card
        ≤ ∑ u ∈ stateSet A t.castSucc,
            ((Finset.univ : Finset (ι × Bool)).image (fun p =>
              act (A.U t.succ : Matrix _ _ ℂ) (projOp p.1 p.2 u))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _u ∈ stateSet A t.castSucc, (Fintype.card ι * 2) := by
          refine Finset.sum_le_sum ?_
          intro u _
          refine le_trans Finset.card_image_le ?_
          simp [Fintype.card_prod]
      _ = (stateSet A t.castSucc).card * (Fintype.card ι * 2) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (Fintype.card ι * 2) ^ (t : ℕ) * (Fintype.card ι * 2) :=
          Nat.mul_le_mul_right _ ih

private lemma stateAt_mem_span_stateSet {ι : Type*} [Fintype ι] [DecidableEq ι]
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (c : ι → Bool) (s : Fin (T + 1)) :
    A.stateAt (xorOracle c) s ∈
      Submodule.span ℂ (stateSet A s : Set (EuclideanSpace ℂ ((ι × Bool) × W))) := by
  classical
  refine Fin.induction ?_ ?_ s
  · rw [stateAt_zero_eq, stateSet_zero]
    exact Submodule.subset_span (by simp)
  · intro t ih
    rw [stateAt_succ_eq]
    let stepOp : EuclideanSpace ℂ ((ι × Bool) × W) → EuclideanSpace ℂ ((ι × Bool) × W) :=
      fun u => act (A.U t.succ : Matrix _ _ ℂ) (act (Matrix.kronecker (xorOracle c) (1 : Matrix W W ℂ)) u)
    change stepOp (A.stateAt (xorOracle c) t.castSucc) ∈
      Submodule.span ℂ (stateSet A t.succ : Set (EuclideanSpace ℂ ((ι × Bool) × W)))
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ih
    · intro u hu
      have hu_fin : u ∈ stateSet A t.castSucc := hu
      change act (A.U t.succ : Matrix _ _ ℂ)
          (act (Matrix.kronecker (xorOracle c) (1 : Matrix W W ℂ)) u) ∈
        Submodule.span ℂ (stateSet A t.succ : Set (EuclideanSpace ℂ ((ι × Bool) × W)))
      rw [act_kronecker_xorOracle_eq_sum_projOp, act_sum]
      refine sum_mem ?_
      intro i _
      refine Submodule.subset_span ?_
      change act (A.U t.succ : Matrix _ _ ℂ) (projOp i (c i) u) ∈ stateSet A t.succ
      rw [stateSet_succ, Finset.mem_biUnion]
      refine ⟨u, hu_fin, Finset.mem_image.mpr ⟨(i, c i), Finset.mem_univ _, rfl⟩⟩
    · change act (A.U t.succ : Matrix _ _ ℂ)
          (act (Matrix.kronecker (xorOracle c) (1 : Matrix W W ℂ)) 0) ∈
        Submodule.span ℂ (stateSet A t.succ : Set (EuclideanSpace ℂ ((ι × Bool) × W)))
      rw [act_zero, act_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      change act (A.U t.succ : Matrix _ _ ℂ)
          (act (Matrix.kronecker (xorOracle c) (1 : Matrix W W ℂ)) (x + y)) ∈
        Submodule.span ℂ (stateSet A t.succ : Set (EuclideanSpace ℂ ((ι × Bool) × W)))
      rw [act_add, act_add]
      exact Submodule.add_mem _ hx hy
    · intro r x _ hx
      change act (A.U t.succ : Matrix _ _ ℂ)
          (act (Matrix.kronecker (xorOracle c) (1 : Matrix W W ℂ)) (r • x)) ∈
        Submodule.span ℂ (stateSet A t.succ : Set (EuclideanSpace ℂ ((ι × Bool) × W)))
      rw [act_smul, act_smul]
      exact Submodule.smul_mem _ r hx

private lemma coord_norm_sq_le_onb_sum {I : Type*} [Fintype I] [DecidableEq I]
    (S : Submodule ℂ (EuclideanSpace ℂ I))
    (ψ : EuclideanSpace ℂ I) (hψ : ψ ∈ S) (hnorm : (∑ z : I, ‖ψ.ofLp z‖ ^ 2) = 1) (z : I) :
    let b := stdOrthonormalBasis ℂ S
    ‖ψ.ofLp z‖ ^ 2 ≤
      ∑ k : Fin (Module.finrank ℂ S), ‖((b k : S) : EuclideanSpace ℂ I).ofLp z‖ ^ 2 := by
  intro b
  let ψ' : S := ⟨ψ, hψ⟩
  have hrepr : ψ.ofLp z =
      ∑ k : Fin (Module.finrank ℂ S),
        (b.repr ψ').ofLp k * ((b k : S) : EuclideanSpace ℂ I).ofLp z := by
    have h1 := b.sum_repr ψ'
    have h2 := congr_arg (fun x : S => (x : EuclideanSpace ℂ I).ofLp z) h1
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, WithLp.ofLp_sum,
      WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    exact h2.symm
  have hnorm_ψ' : ‖ψ'‖ ^ 2 = 1 := by
    change ‖ψ‖ ^ 2 = 1
    rw [EuclideanSpace.norm_sq_eq, hnorm]
  have hrepr_norm :
      (∑ k : Fin (Module.finrank ℂ S), ‖(b.repr ψ').ofLp k‖ ^ 2) = 1 := by
    rw [← EuclideanSpace.norm_sq_eq, LinearIsometryEquiv.norm_map, hnorm_ψ']
  have htri :
      ‖ψ.ofLp z‖ ≤
        ∑ k : Fin (Module.finrank ℂ S),
          ‖(b.repr ψ').ofLp k‖ * ‖((b k : S) : EuclideanSpace ℂ I).ofLp z‖ := by
    rw [hrepr]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum ?_)
    intro k _
    rw [norm_mul]
  have hsq_le :
      ‖ψ.ofLp z‖ ^ 2 ≤
        (∑ k : Fin (Module.finrank ℂ S),
          ‖(b.repr ψ').ofLp k‖ * ‖((b k : S) : EuclideanSpace ℂ I).ofLp z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin (Module.finrank ℂ S)))
    (fun k => ‖(b.repr ψ').ofLp k‖)
    (fun k => ‖((b k : S) : EuclideanSpace ℂ I).ofLp z‖)
  rw [hrepr_norm, one_mul] at hcs
  exact le_trans hsq_le hcs

private lemma sum_onb_coord_norm_sq {I : Type*} [Fintype I] [DecidableEq I]
    (S : Submodule ℂ (EuclideanSpace ℂ I)) :
    let b := stdOrthonormalBasis ℂ S
    (∑ z : I, ∑ k : Fin (Module.finrank ℂ S), ‖((b k : S) : EuclideanSpace ℂ I).ofLp z‖ ^ 2) =
      (Module.finrank ℂ S : ℝ) := by
  intro b
  rw [Finset.sum_comm]
  have h1 : ∀ k : Fin (Module.finrank ℂ S),
      (∑ z : I, ‖((b k : S) : EuclideanSpace ℂ I).ofLp z‖ ^ 2) = 1 := by
    intro k
    rw [← EuclideanSpace.norm_sq_eq]
    have hk : ‖(b k : S)‖ = 1 := b.orthonormal.1 k
    change ‖(b k : S)‖ ^ 2 = 1
    rw [hk, one_pow]
  simp [h1]

private lemma card_le_dim_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C : Finset (ι → Bool)}
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg ι Bool W T) (out : (ι × Bool) × W → (ι → Bool))
    (hLearn : IsQExactLearner A out C) :
    (2 / 3 : ℝ) * (C.card : ℝ) ≤ (((Fintype.card ι * 2) ^ T : ℕ) : ℝ) := by
  let S : Submodule ℂ (EuclideanSpace ℂ ((ι × Bool) × W)) :=
    Submodule.span ℂ (stateSet A (Fin.last T) : Set (EuclideanSpace ℂ ((ι × Bool) × W)))
  let b := stdOrthonormalBasis ℂ S
  have hprob_le : ∀ c ∈ C,
      (2 / 3 : ℝ) ≤
        ∑ z : (ι × Bool) × W,
          if out z = c then
            ∑ k : Fin (Module.finrank ℂ S), ‖((b k : S) : EuclideanSpace ℂ ((ι × Bool) × W)).ofLp z‖ ^ 2
          else 0 := by
    intro c hc
    have hacc := hLearn c hc
    rw [outputProb_eq_sum_ite] at hacc
    refine le_trans hacc (Finset.sum_le_sum ?_)
    intro z _
    split_ifs with hzc
    · exact coord_norm_sq_le_onb_sum S (A.finalState (xorOracle c))
        (stateAt_mem_span_stateSet A c (Fin.last T))
        (stateAt_norm_sq A c (Fin.last T)) z
    · exact le_rfl
  have hsum_C :
      (2 / 3 : ℝ) * (C.card : ℝ) ≤
        ∑ z : (ι × Bool) × W,
          ∑ k : Fin (Module.finrank ℂ S), ‖((b k : S) : EuclideanSpace ℂ ((ι × Bool) × W)).ofLp z‖ ^ 2 := by
    calc (2 / 3 : ℝ) * (C.card : ℝ)
        = ∑ _c ∈ C, (2 / 3 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ c ∈ C, ∑ z : (ι × Bool) × W,
            if out z = c then
              ∑ k : Fin (Module.finrank ℂ S), ‖((b k : S) : EuclideanSpace ℂ ((ι × Bool) × W)).ofLp z‖ ^ 2
            else 0 :=
          Finset.sum_le_sum hprob_le
      _ = ∑ z : (ι × Bool) × W, ∑ c ∈ C,
            if out z = c then
              ∑ k : Fin (Module.finrank ℂ S), ‖((b k : S) : EuclideanSpace ℂ ((ι × Bool) × W)).ofLp z‖ ^ 2
            else 0 := by
          rw [Finset.sum_comm]
      _ ≤ ∑ z : (ι × Bool) × W,
            ∑ k : Fin (Module.finrank ℂ S), ‖((b k : S) : EuclideanSpace ℂ ((ι × Bool) × W)).ofLp z‖ ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro z _
          by_cases hz : out z ∈ C
          · rw [Finset.sum_eq_single (out z)]
            · simp
            · intro c _ hne
              exact if_neg hne.symm
            · intro habs
              exact False.elim (habs hz)
          · rw [Finset.sum_eq_zero]
            · positivity
            · intro c hc
              have hne : out z ≠ c := fun h => hz (h ▸ hc)
              exact if_neg hne
  rw [sum_onb_coord_norm_sq S] at hsum_C
  have hfinrank_le : Module.finrank ℂ S ≤ (stateSet A (Fin.last T)).card := by
    classical
    simpa [S] using
      finrank_span_le_card (R := ℂ)
        (stateSet A (Fin.last T) : Set (EuclideanSpace ℂ ((ι × Bool) × W)))
  have hcard_le : (stateSet A (Fin.last T)).card ≤ (Fintype.card ι * 2) ^ T := by
    simpa using card_stateSet_le A (Fin.last T)
  have hnat_le : Module.finrank ℂ S ≤ (Fintype.card ι * 2) ^ T :=
    le_trans hfinrank_le hcard_le
  exact le_trans hsum_C (by exact_mod_cast hnat_le)

private lemma quantum_lower_log {n : ℕ} (hn : 1 ≤ n)
    {C : Finset (Qubits n → Bool)} (hC : 2 ≤ C.card)
    {W : Type u} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Qubits n) Bool W T) (out : (Qubits n × Bool) × W → (Qubits n → Bool))
    (hLearn : IsQExactLearner A out C) :
    (1 / 3 : ℝ) * (Real.log (C.card : ℝ) / (n : ℝ)) ≤ (T : ℝ) := by
  have hdim := card_le_dim_bound A out hLearn
  have hcard_qubits : Fintype.card (Qubits n) * 2 = 2 ^ (n + 1) := by
    simp [Qubits, pow_succ]
  rw [hcard_qubits, ← pow_mul] at hdim
  have hT_pos : 1 ≤ T := by
    by_contra hT0
    have hT_eq : T = 0 := by omega
    subst hT_eq
    have hC_real : (2 : ℝ) ≤ (C.card : ℝ) := by exact_mod_cast hC
    simp only [mul_zero, pow_zero, Nat.cast_one] at hdim
    linarith
  have hexp_le : (n + 1) * T + 1 ≤ 3 * n * T := by nlinarith
  have hpow_nat : 2 * 2 ^ ((n + 1) * T) ≤ 2 ^ (3 * n * T) := by
    calc 2 * 2 ^ ((n + 1) * T)
        = 2 ^ ((n + 1) * T + 1) := by ring
      _ ≤ 2 ^ (3 * n * T) := Nat.pow_le_pow_right (by omega) hexp_le
  have hpow_real : (2 : ℝ) * (((2 ^ ((n + 1) * T) : ℕ) : ℝ)) ≤ (((2 ^ (3 * n * T) : ℕ) : ℝ)) := by
    exact_mod_cast hpow_nat
  have hcard_le_pow : (C.card : ℝ) ≤ (2 : ℝ) ^ (3 * n * T) := by
    have h1 : (C.card : ℝ) ≤ (2 : ℝ) * (((2 ^ ((n + 1) * T) : ℕ) : ℝ)) := by linarith
    have h2 : (((2 ^ (3 * n * T) : ℕ) : ℝ)) = (2 : ℝ) ^ (3 * n * T) := by push_cast; rfl
    linarith
  have hcard_pos : (0 : ℝ) < (C.card : ℝ) := by
    have : 0 < C.card := by omega
    exact_mod_cast this
  have hlog_le : Real.log (C.card : ℝ) ≤ (3 : ℝ) * (n : ℝ) * (T : ℝ) := by
    calc Real.log (C.card : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (3 * n * T)) := Real.log_le_log hcard_pos hcard_le_pow
      _ = ((3 * n * T : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ ((3 * n * T : ℕ) : ℝ) * 1 := by
          have hlog2 : Real.log 2 ≤ 1 := by
            have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
            linarith
          have hnonneg : (0 : ℝ) ≤ ((3 * n * T : ℕ) : ℝ) := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_left hlog2 hnonneg
      _ = (3 : ℝ) * (n : ℝ) * (T : ℝ) := by push_cast; ring
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hdiv : Real.log (C.card : ℝ) / (n : ℝ) ≤ (3 : ℝ) * (T : ℝ) := by
    rw [div_le_iff₀ hn_pos]
    linarith
  linarith

end SolServedioLower

universe u

theorem solution :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ), 1 ≤ n → ∀ (C : Finset (Qubits n → Bool)), 2 ≤ C.card →
      ∀ (W : Type u) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Qubits n) Bool W T)
        (out : (Qubits n × Bool) × W → (Qubits n → Bool)),
        Learning.IsQExactLearner A out C →
          K * max (1 / Real.sqrt (Learning.gammaParam C)) (Real.log (C.card : ℝ) / (n : ℝ)) ≤
            (T : ℝ) := by
  refine ⟨1 / 144, by norm_num, ?_⟩
  intro n hn C hC W _ _ T A out hLearn
  have h1 := SolServedioLower.quantum_lower_gamma hC A out hLearn
  have h2 := SolServedioLower.quantum_lower_log hn hC A out hLearn
  have hcard_ge_one : (1 : ℝ) ≤ (C.card : ℝ) := by
    have : 1 ≤ C.card := by omega
    exact_mod_cast this
  have hlog_nonneg : 0 ≤ Real.log (C.card : ℝ) / (n : ℝ) := by
    refine div_nonneg (Real.log_nonneg hcard_ge_one) (Nat.cast_nonneg _)
  have h2' : (1 / 144 : ℝ) * (Real.log (C.card : ℝ) / (n : ℝ)) ≤ (T : ℝ) := by
    linarith
  rcases max_choice (1 / Real.sqrt (Learning.gammaParam C)) (Real.log (C.card : ℝ) / (n : ℝ)) with hmax | hmax
  · rw [hmax]; exact h1
  · rw [hmax]; exact h2'
