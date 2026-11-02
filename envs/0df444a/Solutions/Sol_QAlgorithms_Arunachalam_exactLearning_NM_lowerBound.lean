-- Prove2me | solution 1 for QAlgorithms.Arunachalam.exactLearning_NM_lowerBound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T20:08:30.917194+00:00
-- url     : https://prove2.me/submissions/d8e6846e-b8c5-43d3-afcd-ea53e47277e2

import Definitions.Def_QAlgorithms_Defs_Learning

set_option autoImplicit false

open scoped Matrix ComplexConjugate ComplexOrder
open QAlgorithms
open QAlgorithms.Learning

noncomputable section

namespace SolExactLearning

/-- Number of `true` bits in a Boolean string `x : Fin N → Bool`. -/
def hammingWt {N : ℕ} (x : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin N => x i = true)).card

/-- Indices where `x i = false`. -/
def zerosOf {N : ℕ} (x : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => x i = false)

/-- Indices where `x i = true`. -/
def onesOf {N : ℕ} (x : Fin N → Bool) : Finset (Fin N) :=
  Finset.univ.filter (fun i : Fin N => x i = true)

/-- Strings of Hamming weight `d`. -/
def sliceSet (N d : ℕ) : Finset (Fin N → Bool) :=
  Finset.univ.filter (fun x : Fin N → Bool => hammingWt x = d)

/-- Concept class of strings of Hamming weight `k - 1` or `k`. -/
def classForK (N k : ℕ) : Finset (Fin N → Bool) :=
  sliceSet N (k - 1) ∪ sliceSet N k

/-- Flip bit `i` of `x`. -/
def flipBit {N : ℕ} (x : Fin N → Bool) (i : Fin N) : Fin N → Bool :=
  Function.update x i (!x i)

private lemma flipBit_invol {N : ℕ} (x : Fin N → Bool) (i : Fin N) :
    flipBit (flipBit x i) i = x := by
  ext j
  simp only [flipBit, Function.update_apply]
  split_ifs with h
  · subst h; simp
  · rfl

private lemma flipBit_self {N : ℕ} (x : Fin N → Bool) (i : Fin N) :
    flipBit x i i = !x i := by
  simp [flipBit]

private lemma flipBit_of_ne {N : ℕ} (x : Fin N → Bool) {i j : Fin N} (h : j ≠ i) :
    flipBit x i j = x j := by
  simp [flipBit, h]

private lemma onesOf_add_zerosOf_card {N : ℕ} (x : Fin N → Bool) :
    (onesOf x).card + (zerosOf x).card = N := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (p := fun i : Fin N => x i = true)
  have hnot : (Finset.univ.filter (fun i : Fin N => ¬x i = true)) = zerosOf x := by
    ext i
    simp [zerosOf]
  rw [hnot] at h
  simpa [onesOf] using h

private lemma onesOf_flipBit_of_false {N : ℕ} {x : Fin N → Bool} {i : Fin N} (hx : x i = false) :
    onesOf (flipBit x i) = insert i (onesOf x) := by
  ext j
  simp only [onesOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    flipBit, Function.update_apply]
  by_cases hji : j = i
  · subst hji; simp [hx]
  · simp [hji]

private lemma hammingWt_flipBit_of_false {N : ℕ} {x : Fin N → Bool} {i : Fin N}
    (hx : x i = false) :
    hammingWt (flipBit x i) = hammingWt x + 1 := by
  change (onesOf (flipBit x i)).card = (onesOf x).card + 1
  rw [onesOf_flipBit_of_false hx, Finset.card_insert_of_notMem]
  simp [onesOf, hx]

private lemma hammingWt_flipBit_of_true {N : ℕ} {y : Fin N → Bool} {i : Fin N}
    (hy : y i = true) :
    hammingWt (flipBit y i) + 1 = hammingWt y := by
  have hfalse : flipBit y i i = false := by simp [flipBit, hy]
  have h1 := hammingWt_flipBit_of_false hfalse
  rw [flipBit_invol] at h1
  exact h1.symm

private lemma card_zerosOf_of_mem_slice {N k : ℕ} {x : Fin N → Bool}
    (hk1 : 1 ≤ k) (hkN : k ≤ N) (hx : x ∈ sliceSet N (k - 1)) :
    (zerosOf x).card = N - k + 1 := by
  simp only [sliceSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  have hsum := onesOf_add_zerosOf_card x
  change hammingWt x + (zerosOf x).card = N at hsum
  omega

private lemma card_onesOf_of_mem_slice {N k : ℕ} {y : Fin N → Bool}
    (hy : y ∈ sliceSet N k) :
    (onesOf y).card = k := by
  simp only [sliceSet, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  exact hy

private lemma card_sliceSet (N d : ℕ) : (sliceSet N d).card = N.choose d := by
  classical
  have hbij : (sliceSet N d).card =
      (Finset.powersetCard d (Finset.univ : Finset (Fin N))).card := by
    refine Finset.card_bij (fun x _ => onesOf x) ?_ ?_ ?_
    · intro x hx
      simp only [sliceSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, hx⟩
    · intro x₁ _ x₂ _ h
      ext i
      have hi : (i ∈ onesOf x₁) ↔ (i ∈ onesOf x₂) := by rw [h]
      simp only [onesOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      cases hx₁ : x₁ i <;> cases hx₂ : x₂ i <;> simp_all
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      have hwt : hammingWt (fun i : Fin N => decide (i ∈ S)) = d := by
        unfold hammingWt
        have hEq : (Finset.univ.filter (fun i : Fin N => decide (i ∈ S) = true)) = S := by
          ext i; simp
        rw [hEq, hS.2]
      refine ⟨fun i => decide (i ∈ S), ?_, ?_⟩
      · simp [sliceSet, hwt]
      · ext i; simp [onesOf]
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma card_classForK_le (N k : ℕ) :
    (classForK N k).card ≤ N.choose (k - 1) + N.choose k := by
  calc (classForK N k).card
      ≤ (sliceSet N (k - 1)).card + (sliceSet N k).card := Finset.card_union_le _ _
    _ = N.choose (k - 1) + N.choose k := by rw [card_sliceSet, card_sliceSet]

/-- Edge-switching identity between `(sliceSet N (k - 1), zerosOf)` and `(sliceSet N k, onesOf)`. -/
private lemma sum_edges_eq {N k : ℕ} (hk1 : 1 ≤ k)
    (F : (Fin N → Bool) → (Fin N → Bool) → Fin N → ℝ) :
    ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x, F x (flipBit x i) i =
      ∑ y ∈ sliceSet N k, ∑ i ∈ onesOf y, F (flipBit y i) y i := by
  have hL :
      (∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x, F x (flipBit x i) i) =
        ∑ p ∈ (sliceSet N (k - 1)).sigma zerosOf, F p.1 (flipBit p.1 p.2) p.2 :=
    Finset.sum_sigma' (sliceSet N (k - 1)) zerosOf
      (fun x i => F x (flipBit x i) i)
  have hR :
      (∑ y ∈ sliceSet N k, ∑ i ∈ onesOf y, F (flipBit y i) y i) =
        ∑ q ∈ (sliceSet N k).sigma onesOf, F (flipBit q.1 q.2) q.1 q.2 :=
    Finset.sum_sigma' (sliceSet N k) onesOf
      (fun y i => F (flipBit y i) y i)
  rw [hL, hR]
  refine Finset.sum_bij'
    (fun p _ => ⟨flipBit p.1 p.2, p.2⟩)
    (fun q _ => ⟨flipBit q.1 q.2, q.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, i⟩ hp
    simp only [Finset.mem_sigma, sliceSet, Finset.mem_filter, Finset.mem_univ, true_and,
      zerosOf, onesOf] at hp ⊢
    refine ⟨?_, ?_⟩
    · rw [hammingWt_flipBit_of_false hp.2, hp.1]
      omega
    · simp [flipBit, hp.2]
  · rintro ⟨y, i⟩ hq
    simp only [Finset.mem_sigma, sliceSet, Finset.mem_filter, Finset.mem_univ, true_and,
      zerosOf, onesOf] at hq ⊢
    refine ⟨?_, ?_⟩
    · have h := hammingWt_flipBit_of_true hq.2
      omega
    · simp [flipBit, hq.2]
  · rintro ⟨x, i⟩ _
    ext <;> simp [flipBit_invol]
  · rintro ⟨y, i⟩ _
    ext <;> simp [flipBit_invol]
  · rintro ⟨x, i⟩ _
    simp [flipBit_invol]

private lemma card_edges_eq {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    ((sliceSet N (k - 1)).card : ℝ) * ((N - k + 1 : ℕ) : ℝ) =
      ((sliceSet N k).card : ℝ) * (k : ℝ) := by
  have h := sum_edges_eq (N := N) (k := k) hk1 (fun _ _ _ => (1 : ℝ))
  have hL : (∑ x ∈ sliceSet N (k - 1), ∑ _i ∈ zerosOf x, (1 : ℝ)) =
      ((sliceSet N (k - 1)).card : ℝ) * ((N - k + 1 : ℕ) : ℝ) := by
    have h1 : ∀ x ∈ sliceSet N (k - 1),
        (∑ _i ∈ zerosOf x, (1 : ℝ)) = ((N - k + 1 : ℕ) : ℝ) := by
      intro x hx
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_zerosOf_of_mem_slice hk1 hkN hx]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  have hR : (∑ y ∈ sliceSet N k, ∑ _i ∈ onesOf y, (1 : ℝ)) =
      ((sliceSet N k).card : ℝ) * (k : ℝ) := by
    have h1 : ∀ y ∈ sliceSet N k, (∑ _i ∈ onesOf y, (1 : ℝ)) = (k : ℝ) := by
      intro y hy
      rw [Finset.sum_const, nsmul_eq_mul, mul_one, card_onesOf_of_mem_slice hy]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
  linarith

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

private lemma kronecker_xorOracle_mulVec {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (x : Fin N → Bool) (v : ((Fin N × Bool) × W) → ℂ) (j : Fin N) (b : Bool) (w : W) :
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

private lemma norm_sq_kronecker_xorOracle {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W]
    (x : Fin N → Bool) (v : ((Fin N × Bool) × W) → ℂ) :
    (∑ z : (Fin N × Bool) × W, ‖(Matrix.kronecker (xorOracle x) (1 : Matrix W W ℂ) *ᵥ v) z‖ ^ 2) =
      ∑ z : (Fin N × Bool) × W, ‖v z‖ ^ 2 := by
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

private lemma stateAt_zero_eq {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (O : Matrix (Fin N × Bool) (Fin N × Bool) ℂ) :
    A.stateAt O 0 = act (A.U 0 : Matrix _ _ ℂ) A.start := by
  simp [QueryAlg.stateAt]

private lemma stateAt_succ_eq {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (O : Matrix (Fin N × Bool) (Fin N × Bool) ℂ) (t : Fin T) :
    A.stateAt O t.succ =
      act (A.U t.succ : Matrix _ _ ℂ)
        (act (Matrix.kronecker O (1 : Matrix W W ℂ)) (A.stateAt O t.castSucc)) := by
  simp [QueryAlg.stateAt]

private lemma stateAt_norm_sq {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (x : Fin N → Bool) (t : Fin (T + 1)) :
    (∑ z : (Fin N × Bool) × W, ‖(A.stateAt (xorOracle x) t).ofLp z‖ ^ 2) = 1 := by
  refine Fin.induction ?_ ?_ t
  · rw [stateAt_zero_eq]
    simp only [act, WithLp.ofLp_toLp]
    rw [norm_sq_mulVec_of_unitary (A.U 0)]
    have hinit := A.start_unit
    have hnorm : ‖A.start‖ ^ 2 = ∑ z : (Fin N × Bool) × W, ‖A.start.ofLp z‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq A.start
    linarith [show ‖A.start‖ ^ 2 = 1 by rw [hinit]; ring]
  · intro s ih
    rw [stateAt_succ_eq]
    simp only [act, WithLp.ofLp_toLp]
    rw [norm_sq_mulVec_of_unitary (A.U s.succ), norm_sq_kronecker_xorOracle]
    exact ih

/-- Weight of `A.stateAt (xorOracle x) t` on query index `i`. -/
def idxWeight {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (x : Fin N → Bool) (t : Fin (T + 1)) (i : Fin N) : ℝ :=
  ∑ b : Bool, ∑ w : W, ‖(A.stateAt (xorOracle x) t).ofLp ((i, b), w)‖ ^ 2

private lemma idxWeight_nonneg {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (x : Fin N → Bool) (t : Fin (T + 1)) (i : Fin N) :
    0 ≤ idxWeight A x t i := by
  unfold idxWeight
  positivity

private lemma sum_idxWeight_eq_one {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (x : Fin N → Bool) (t : Fin (T + 1)) :
    (∑ i : Fin N, idxWeight A x t i) = 1 := by
  unfold idxWeight
  exact (sum_prod_three' (fun z : (Fin N × Bool) × W =>
    ‖(A.stateAt (xorOracle x) t).ofLp z‖ ^ 2)).symm.trans (stateAt_norm_sq A x t)

private lemma sum_idxWeight_subset_le_one {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (x : Fin N → Bool) (t : Fin (T + 1)) (S : Finset (Fin N)) :
    (∑ i ∈ S, idxWeight A x t i) ≤ 1 := by
  calc (∑ i ∈ S, idxWeight A x t i)
      ≤ ∑ i : Fin N, idxWeight A x t i := by
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

private lemma overlap_step_diff_bound {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (x : Fin N → Bool) (i : Fin N) (t : Fin T)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) *
      ‖vecOverlap (A.stateAt (xorOracle x) t.succ).ofLp
          (A.stateAt (xorOracle (flipBit x i)) t.succ).ofLp -
        vecOverlap (A.stateAt (xorOracle x) t.castSucc).ofLp
          (A.stateAt (xorOracle (flipBit x i)) t.castSucc).ofLp‖ ≤
      a * idxWeight A x t.castSucc i + b * idxWeight A (flipBit x i) t.castSucc i := by
  set y := flipBit x i
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
      (∑ b0 : Bool, ∑ w : W,
        star (u ((i, b0 + x i), w)) * v ((i, b0 + y i), w)) -
      (∑ b0 : Bool, ∑ w : W,
        star (u ((i, b0), w)) * v ((i, b0), w)) := by
    unfold vecOverlap
    rw [sum_prod_three', sum_prod_three', ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single i]
    · congr 1
      refine Finset.sum_congr rfl ?_
      intro b0 _
      refine Finset.sum_congr rfl ?_
      intro w _
      rw [kronecker_xorOracle_mulVec, kronecker_xorOracle_mulVec]
    · intro j _ hji
      have hyj : y j = x j := flipBit_of_ne x hji
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
          rw [kronecker_xorOracle_mulVec, kronecker_xorOracle_mulVec, hyj]
        rw [h2, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        conv_rhs => rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
        refine Finset.sum_congr rfl ?_
        intro w _
        exact sum_bool_add (x j) (fun b0 => star (u ((j, b0), w)) * v ((j, b0), w))
      rw [h1, sub_self]
    · intro habs
      exact False.elim (habs (Finset.mem_univ _))
  rw [hdiff]
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
  have hsqrt_nonneg : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hnorm hsqrt_nonneg
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

private lemma overlap_final_diff_bound {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (x : Fin N → Bool) (i : Fin N)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) *
      ‖(1 : ℂ) - vecOverlap (A.finalState (xorOracle x)).ofLp
          (A.finalState (xorOracle (flipBit x i))).ofLp‖ ≤
      ∑ t : Fin T,
        (a * idxWeight A x t.castSucc i + b * idxWeight A (flipBit x i) t.castSucc i) := by
  let f : Fin (T + 1) → ℂ := fun t =>
    vecOverlap (A.stateAt (xorOracle x) t).ofLp (A.stateAt (xorOracle (flipBit x i)) t).ofLp
  have hf0 : f 0 = 1 := by
    dsimp [f]
    have h0 : A.stateAt (xorOracle (flipBit x i)) 0 = A.stateAt (xorOracle x) 0 := rfl
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
  exact overlap_step_diff_bound A x i t ha hb

private lemma prob_eq_norm_sq {I : Type*} [Fintype I] [DecidableEq I]
    (ψ : EuclideanSpace ℂ I) (z : I) :
    prob ψ z = ‖ψ.ofLp z‖ ^ 2 := by
  simp [prob, ket, EuclideanSpace.inner_single_left]

private lemma outputProb_eq_sum_ite {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    (A : QueryAlg (Fin N) Bool W T) (O : Matrix (Fin N × Bool) (Fin N × Bool) ℂ)
    (out : (Fin N × Bool) × W → (Fin N → Bool)) (c : Fin N → Bool) :
    A.outputProb O out c =
      ∑ z : (Fin N × Bool) × W, if out z = c then ‖(A.finalState O).ofLp z‖ ^ 2 else 0 := by
  unfold QueryAlg.outputProb probEvent
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [prob_eq_norm_sq]

private lemma overlap_final_dist_lower {N : ℕ} {W : Type*} [Fintype W] [DecidableEq W] {T : ℕ}
    {A : QueryAlg (Fin N) Bool W T} {out : (Fin N × Bool) × W → (Fin N → Bool)}
    {C : Finset (Fin N → Bool)} (hLearn : IsQExactLearner A out C)
    {x y : Fin N → Bool} (hx : x ∈ C) (hy : y ∈ C) (hxy : x ≠ y) :
    (1 / 18 : ℝ) ≤
      ‖(1 : ℂ) - vecOverlap (A.finalState (xorOracle x)).ofLp
          (A.finalState (xorOracle y)).ofLp‖ := by
  set u := (A.finalState (xorOracle x)).ofLp
  set v := (A.finalState (xorOracle y)).ofLp
  have hacc_x : A.outputProb (xorOracle x) out x ≥ 2 / 3 := hLearn x hx
  have hacc_y : A.outputProb (xorOracle y) out y ≥ 2 / 3 := hLearn y hy
  have hu_norm : (∑ z : (Fin N × Bool) × W, ‖u z‖ ^ 2) = 1 := stateAt_norm_sq A x (Fin.last T)
  have hv_norm : (∑ z : (Fin N × Bool) × W, ‖v z‖ ^ 2) = 1 := stateAt_norm_sq A y (Fin.last T)
  have hu_bad : (∑ z : (Fin N × Bool) × W, if out z = x then (0 : ℝ) else ‖u z‖ ^ 2) ≤ 1 / 3 := by
    have hsplit :
        A.outputProb (xorOracle x) out x +
          (∑ z : (Fin N × Bool) × W, if out z = x then (0 : ℝ) else ‖u z‖ ^ 2) =
        ∑ z : (Fin N × Bool) × W, ‖u z‖ ^ 2 := by
      rw [outputProb_eq_sum_ite, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro z _
      split_ifs <;> ring
    linarith
  have hv_bad : (∑ z : (Fin N × Bool) × W, if out z = x then ‖v z‖ ^ 2 else (0 : ℝ)) ≤ 1 / 3 := by
    have hle :
        (∑ z : (Fin N × Bool) × W, if out z = x then ‖v z‖ ^ 2 else (0 : ℝ)) +
          A.outputProb (xorOracle y) out y ≤
        ∑ z : (Fin N × Bool) × W, ‖v z‖ ^ 2 := by
      rw [outputProb_eq_sum_ite, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum ?_
      intro z _
      by_cases hzx : out z = x
      · have hzy : out z ≠ y := by
          intro hzy
          exact hxy (hzx.symm.trans hzy)
        rw [if_pos hzx, if_neg hzy, add_zero]
      · by_cases hzy : out z = y
        · rw [if_neg hzx, if_pos hzy, zero_add]
        · rw [if_neg hzx, if_neg hzy, add_zero]
          exact sq_nonneg _
    linarith
  have hpt : ∀ z : (Fin N × Bool) × W,
      ‖star (u z) * v z‖ ≤
        (1 / 3 : ℝ) * ‖u z‖ ^ 2 + (1 / 3 : ℝ) * ‖v z‖ ^ 2 +
          (5 / 12 : ℝ) * (if out z = x then (0 : ℝ) else ‖u z‖ ^ 2) +
          (5 / 12 : ℝ) * (if out z = x then ‖v z‖ ^ 2 else (0 : ℝ)) := by
    intro z
    rw [norm_mul, norm_star]
    by_cases hzx : out z = x
    · simp only [hzx, ↓reduceIte]
      nlinarith [sq_nonneg (2 * ‖u z‖ - 3 * ‖v z‖)]
    · simp only [hzx, ↓reduceIte]
      nlinarith [sq_nonneg (3 * ‖u z‖ - 2 * ‖v z‖)]
  have hov_le : ‖vecOverlap u v‖ ≤ 17 / 18 := by
    have h1 : ‖vecOverlap u v‖ ≤ ∑ z : (Fin N × Bool) × W, ‖star (u z) * v z‖ :=
      norm_sum_le _ _
    have h2 : (∑ z : (Fin N × Bool) × W, ‖star (u z) * v z‖) ≤
        ∑ z : (Fin N × Bool) × W,
          ((1 / 3 : ℝ) * ‖u z‖ ^ 2 + (1 / 3 : ℝ) * ‖v z‖ ^ 2 +
            (5 / 12 : ℝ) * (if out z = x then (0 : ℝ) else ‖u z‖ ^ 2) +
            (5 / 12 : ℝ) * (if out z = x then ‖v z‖ ^ 2 else (0 : ℝ))) :=
      Finset.sum_le_sum (fun z _ => hpt z)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    linarith
  have htri : (1 : ℝ) - ‖vecOverlap u v‖ ≤ ‖(1 : ℂ) - vecOverlap u v‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (vecOverlap u v)
    simpa using h
  linarith

private lemma exactLearning_fixed_k_lowerBound {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    {C : Finset (Fin N → Bool)} (hC : classForK N k ⊆ C)
    (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Fin N) Bool W T)
    (out : (Fin N × Bool) × W → (Fin N → Bool))
    (hLearn : IsQExactLearner A out C) :
    (1 / 36 : ℝ) * Real.sqrt ((((N - k + 1 : ℕ) : ℝ)) * (k : ℝ)) ≤ (T : ℝ) := by
  set a : ℝ := ((N - k + 1 : ℕ) : ℝ)
  set b : ℝ := (k : ℝ)
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hedge : ∀ x ∈ sliceSet N (k - 1), ∀ i ∈ zerosOf x,
      (1 / 18 : ℝ) * Real.sqrt (a * b) ≤
        ∑ s : Fin T,
          (a * idxWeight A x s.castSucc i + b * idxWeight A (flipBit x i) s.castSucc i) := by
    intro x hx i hi
    have hxC : x ∈ C := hC (Finset.mem_union_left _ hx)
    have hy_slice : flipBit x i ∈ sliceSet N k := by
      simp only [sliceSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      simp only [zerosOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [hammingWt_flipBit_of_false hi, hx]
      omega
    have hyC : flipBit x i ∈ C := hC (Finset.mem_union_right _ hy_slice)
    have hxy : x ≠ flipBit x i := by
      intro hEq
      simp only [zerosOf, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      have h1 : x i = flipBit x i i := congrFun hEq i
      rw [flipBit_self, hi] at h1
      exact Bool.false_ne_true h1
    have hlow := overlap_final_dist_lower hLearn hxC hyC hxy
    have hup := overlap_final_diff_bound A x i ha hb
    have hmul := mul_le_mul_of_nonneg_left hlow (Real.sqrt_nonneg (a * b))
    linarith
  have hsum_L :
      (∑ x ∈ sliceSet N (k - 1), ∑ _i ∈ zerosOf x, (1 / 18 : ℝ) * Real.sqrt (a * b)) =
        ((sliceSet N (k - 1)).card : ℝ) * a * ((1 / 18 : ℝ) * Real.sqrt (a * b)) := by
    have h1 : ∀ x ∈ sliceSet N (k - 1),
        (∑ _i ∈ zerosOf x, (1 / 18 : ℝ) * Real.sqrt (a * b)) =
          a * ((1 / 18 : ℝ) * Real.sqrt (a * b)) := by
      intro x hx
      rw [Finset.sum_const, nsmul_eq_mul, card_zerosOf_of_mem_slice hk1 hkN hx]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hsum_le :
      ((sliceSet N (k - 1)).card : ℝ) * a * ((1 / 18 : ℝ) * Real.sqrt (a * b)) ≤
        ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x,
          ∑ s : Fin T,
            (a * idxWeight A x s.castSucc i + b * idxWeight A (flipBit x i) s.castSucc i) := by
    rw [← hsum_L]
    refine Finset.sum_le_sum ?_
    intro x hx
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hedge x hx i hi
  have hcomm :
      (∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x,
        ∑ s : Fin T,
          (a * idxWeight A x s.castSucc i + b * idxWeight A (flipBit x i) s.castSucc i)) =
      ∑ s : Fin T,
        ((a * ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x, idxWeight A x s.castSucc i) +
          (b * ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x,
            idxWeight A (flipBit x i) s.castSucc i)) := by
    trans (∑ s : Fin T, ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x,
        (a * idxWeight A x s.castSucc i + b * idxWeight A (flipBit x i) s.castSucc i))
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [Finset.sum_comm]
    · refine Finset.sum_congr rfl ?_
      intro s _
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hstep_bound : ∀ s : Fin T,
      (a * ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x, idxWeight A x s.castSucc i) +
        (b * ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x,
          idxWeight A (flipBit x i) s.castSucc i) ≤
      2 * (((sliceSet N (k - 1)).card : ℝ) * a) := by
    intro s
    have hx_le :
        (∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x, idxWeight A x s.castSucc i) ≤
          ((sliceSet N (k - 1)).card : ℝ) := by
      calc (∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x, idxWeight A x s.castSucc i)
          ≤ ∑ _x ∈ sliceSet N (k - 1), (1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro x _
            exact sum_idxWeight_subset_le_one A x s.castSucc (zerosOf x)
        _ = ((sliceSet N (k - 1)).card : ℝ) := by simp
    have hy_eq :
        (∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x, idxWeight A (flipBit x i) s.castSucc i) =
          ∑ y ∈ sliceSet N k, ∑ i ∈ onesOf y, idxWeight A y s.castSucc i :=
      sum_edges_eq hk1 (fun _ y i => idxWeight A y s.castSucc i)
    have hy_le :
        (∑ y ∈ sliceSet N k, ∑ i ∈ onesOf y, idxWeight A y s.castSucc i) ≤
          ((sliceSet N k).card : ℝ) := by
      calc (∑ y ∈ sliceSet N k, ∑ i ∈ onesOf y, idxWeight A y s.castSucc i)
          ≤ ∑ _y ∈ sliceSet N k, (1 : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro y _
            exact sum_idxWeight_subset_le_one A y s.castSucc (onesOf y)
        _ = ((sliceSet N k).card : ℝ) := by simp
    have hmul_x := mul_le_mul_of_nonneg_left hx_le ha
    have hmul_y := mul_le_mul_of_nonneg_left (hy_eq.trans_le hy_le) hb
    have hcard_eq := card_edges_eq hk1 hkN
    change ((sliceSet N (k - 1)).card : ℝ) * a = ((sliceSet N k).card : ℝ) * b at hcard_eq
    linarith
  have hsum_R :
      (∑ s : Fin T,
        ((a * ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x, idxWeight A x s.castSucc i) +
          (b * ∑ x ∈ sliceSet N (k - 1), ∑ i ∈ zerosOf x,
            idxWeight A (flipBit x i) s.castSucc i))) ≤
      (T : ℝ) * (2 * (((sliceSet N (k - 1)).card : ℝ) * a)) := by
    calc _ ≤ ∑ _s : Fin T, (2 * (((sliceSet N (k - 1)).card : ℝ) * a)) :=
          Finset.sum_le_sum (fun s _ => hstep_bound s)
      _ = (T : ℝ) * (2 * (((sliceSet N (k - 1)).card : ℝ) * a)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcomb :
      ((sliceSet N (k - 1)).card : ℝ) * a * ((1 / 18 : ℝ) * Real.sqrt (a * b)) ≤
        (T : ℝ) * (2 * (((sliceSet N (k - 1)).card : ℝ) * a)) := by
    linarith
  have hcard_pos : (0 : ℝ) < ((sliceSet N (k - 1)).card : ℝ) := by
    rw [card_sliceSet]
    exact Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have ha_pos : (0 : ℝ) < a := by
    change (0 : ℝ) < ((N - k + 1 : ℕ) : ℝ)
    exact Nat.cast_pos.mpr (by omega)
  have hprod_pos : (0 : ℝ) < ((sliceSet N (k - 1)).card : ℝ) * a := mul_pos hcard_pos ha_pos
  nlinarith

end SolExactLearning

theorem solution :
    ∃ c0 : ℝ, 0 < c0 ∧ ∀ N M : ℕ, ∃ C : Finset (Fin N → Bool), C.card ≤ M ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ N → N.choose (k - 1) + N.choose k ≤ M →
        ∀ (W : Type) [Fintype W] [DecidableEq W] (T : ℕ) (A : QueryAlg (Fin N) Bool W T)
          (out : (Fin N × Bool) × W → (Fin N → Bool)),
          IsQExactLearner A out C →
            c0 * Real.sqrt ((((N - k + 1 : ℕ) : ℝ)) * (k : ℝ)) ≤ (T : ℝ) := by
  refine ⟨1 / 36, by norm_num, ?_⟩
  intro N M
  let adm : Finset ℕ := (Finset.Icc 1 N).filter (fun k => N.choose (k - 1) + N.choose k ≤ M)
  by_cases hne : adm.Nonempty
  · obtain ⟨kStar, hkStar_mem, hkStar_max⟩ :=
      Finset.exists_max_image adm (fun k => (N - k + 1) * k) hne
    have hkStar_props : (1 ≤ kStar ∧ kStar ≤ N) ∧ N.choose (kStar - 1) + N.choose kStar ≤ M := by
      simpa [adm, Finset.mem_filter, Finset.mem_Icc] using hkStar_mem
    refine ⟨SolExactLearning.classForK N kStar, ?_, ?_⟩
    · exact le_trans (SolExactLearning.card_classForK_le N kStar) hkStar_props.2
    · intro k hk1 hkN hkM W _ _ T A out hLearn
      have hk_mem : k ∈ adm := by
        simp [adm, Finset.mem_filter, Finset.mem_Icc, hk1, hkN, hkM]
      have hk_le : (N - k + 1) * k ≤ (N - kStar + 1) * kStar := hkStar_max k hk_mem
      have hk_le_real :
          (((N - k + 1 : ℕ) : ℝ)) * (k : ℝ) ≤ (((N - kStar + 1 : ℕ) : ℝ)) * (kStar : ℝ) := by
        exact_mod_cast hk_le
      have hsqrt_le :
          Real.sqrt ((((N - k + 1 : ℕ) : ℝ)) * (k : ℝ)) ≤
            Real.sqrt ((((N - kStar + 1 : ℕ) : ℝ)) * (kStar : ℝ)) :=
        Real.sqrt_le_sqrt hk_le_real
      have hStar := SolExactLearning.exactLearning_fixed_k_lowerBound
        hkStar_props.1.1 hkStar_props.1.2 (Finset.Subset.refl _) W T A out hLearn
      linarith
  · refine ⟨∅, by simp, ?_⟩
    intro k hk1 hkN hkM
    exfalso
    apply hne
    refine ⟨k, ?_⟩
    simp [adm, Finset.mem_filter, Finset.mem_Icc, hk1, hkN, hkM]
