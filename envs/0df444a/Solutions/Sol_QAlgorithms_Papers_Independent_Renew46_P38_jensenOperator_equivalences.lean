-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P38.jensenOperator_equivalences
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:50:46.854586+00:00
-- url     : https://prove2.me/submissions/58a37e52-a7f6-46ed-b828-b96e3e16760a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P38

/- Standalone original Jensen equivalences. Actual accepted dilation/cyclic
proofs by fizzyinc3 are attributed below. All other local mathematical bodies
are included in full. Module-local sections isolate options and open names;
there are no statement-only theorem imports or assumed helper conclusions. -/


/- Included module: JENS1_Accepted. -/
section Inline_JENS1_Accepted
/- Reused actual accepted proofs by fizzyinc3: canonical dilation submission
1bfcc74e-7a2a-4f3e-bae7-2d64779bd443 and cyclic averaging submission
5f3a3e6a-a53c-4af9-8ed7-c2bb9bab6375. Only namespaces/entrypoints changed;
unrelated cyclic-projection helpers omitted. -/
namespace JENS1AcceptedDilation
noncomputable section

section
variable {A : Type*} [Ring A] [StarRing A] {n : ℕ}

def g64e_W (a : Fin n → A) (g : A) (i j : Fin n) : A :=
  (if i = j then 1 else 0) - a i * g * star (a j)

def g64e_U (a : Fin n → A) (g d : A) : Matrix (Option (Fin n)) (Option (Fin n)) A
  | some i, some j => g64e_W a g i j
  | some i, none => a i
  | none, some j => -star (a j)
  | none, none => d

theorem g64e_sumS (a : Fin n → A) (x y : A) :
    ∑ k, x * star (a k) * (a k * y) = x * (∑ k, star (a k) * a k) * y := by
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_assoc]

theorem g64e_U_unitary (a : Fin n → A) (g d : A) (hg : star g = g) (hd : star d = d)
    (h1 : (∑ k, star (a k) * a k) + d * d = 1)
    (h2 : (∑ k, star (a k) * a k) * g = 1 - d)
    (h3 : g * (∑ k, star (a k) * a k) = 1 - d)
    (h4 : (1 + d) * g = 1) :
    star (g64e_U a g d) * g64e_U a g d = 1 ∧ g64e_U a g d * star (g64e_U a g d) = 1 := by
  have hWs : ∀ i k, star (g64e_W a g i k) = g64e_W a g k i := by
    intro i k
    unfold g64e_W
    rw [star_sub, star_mul, star_mul, star_star, hg, ← mul_assoc]
    congr 1
    by_cases h : i = k
    · subst h; simp
    · simp [h, Ne.symm h]
  have LW : ∀ i j, (∑ k, g64e_W a g i k * g64e_W a g k j) + a i * star (a j) =
      if i = j then 1 else 0 := by
    intro i j
    have : ∀ k, g64e_W a g i k * g64e_W a g k j =
        ((if i = k then 1 else 0) * (if k = j then 1 else 0)) - (if i = k then a k * g * star (a j) else 0)
        - (if k = j then a i * g * star (a k) else 0) + (a i * g) * star (a k) * (a k * (g * star (a j))) := by
      intro k
      unfold g64e_W
      split_ifs <;> subst_vars <;> noncomm_ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, g64e_sumS, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hgSg : g * (∑ k, star (a k) * a k) * g = g + g - 1 := by
      rw [h3]
      have : d * g = 1 - g := by rw [← h4]; noncomm_ring
      calc (1 - d) * g = g - d * g := by noncomm_ring
        _ = g + g - 1 := by rw [this]; noncomm_ring
    have e : a i * g * (∑ k, star (a k) * a k) * (g * star (a j)) =
        a i * (g * (∑ k, star (a k) * a k) * g) * star (a j) := by noncomm_ring
    rw [e, hgSg]
    split_ifs with h
    · subst h; noncomm_ring
    · noncomm_ring
  have Lw1 : ∀ i, ∑ k, g64e_W a g i k * a k = a i * d := by
    intro i
    simp only [g64e_W, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have : ∑ k, a i * g * star (a k) * a k = a i * g * (∑ k, star (a k) * a k) := by
      rw [Finset.mul_sum]; simp only [mul_assoc]
    rw [this, mul_assoc, h3]; noncomm_ring
  have Lw2 : ∀ j, ∑ k, star (a k) * g64e_W a g k j = d * star (a j) := by
    intro j
    simp only [g64e_W, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    have : ∑ k, star (a k) * (a k * g * star (a j)) = (∑ k, star (a k) * a k) * g * star (a j) := by
      rw [Finset.sum_mul, Finset.sum_mul]; simp only [mul_assoc]
    rw [this, h2]; noncomm_ring
  constructor
  · ext x y
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.star_apply]
    rcases x with _ | i <;> rcases y with _ | j
    · simp only [g64e_U, hd, Matrix.one_apply_eq]
      rw [add_comm]; exact h1
    · simp only [g64e_U, hd, Matrix.one_apply, reduceCtorEq, if_false]
      rw [Lw2, mul_neg, neg_add_cancel]
    · simp only [g64e_U, hWs, star_neg, star_star, Matrix.one_apply, reduceCtorEq, if_false]
      rw [Lw1, neg_mul, neg_add_cancel]
    · simp only [g64e_U, hWs, star_neg, star_star, neg_mul_neg, Matrix.one_apply, Option.some.injEq]
      rw [add_comm, LW]
  · ext x y
    rw [Matrix.mul_apply, Fintype.sum_option]
    simp only [Matrix.star_apply]
    rcases x with _ | i <;> rcases y with _ | j
    · simp only [g64e_U, hd, Matrix.one_apply_eq, star_neg, star_star, neg_mul_neg]
      rw [add_comm]; exact h1
    · simp only [g64e_U, hWs, star_neg, star_star, neg_mul, Matrix.one_apply, reduceCtorEq,
        if_false, Finset.sum_neg_distrib]
      rw [Lw2, add_neg_cancel]
    · simp only [g64e_U, hd, star_neg, star_star, mul_neg, Matrix.one_apply, reduceCtorEq,
        if_false, Finset.sum_neg_distrib]
      rw [Lw1, add_neg_cancel]
    · simp only [g64e_U, hWs, Matrix.one_apply, Option.some.injEq]
      rw [add_comm, LW]
end



open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, §3, PDF p. 5, explicit canonical dilation (11)--(12).
Block order is H^n ⊕ H. The first-row a_m* in (12) is corrected to a_n* using
(11) and p=1-aa*. The negative sign in the bottom row is retained. -/
theorem canonicalDilation_proof (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (a : Fin n → Operators H) (ha : columnSquares a = 1) :
    IsStarProjection (columnRangeComplement a) ∧
    IsUnitaryMatrix (columnCanonicalDilation a) ∧
    (∀ i : Fin n, columnCanonicalDilation a (some i) none = a i) ∧
    columnCanonicalDilation a none none = 0 := by
  have hS : (∑ k, star (a k) * a k) = 1 := ha
  have hM : star (Matrix.of (fun i j => a i * star (a j))) = Matrix.of (fun i j => a i * star (a j)) := by
    ext i j; simp [Matrix.star_apply, star_mul]
  have hMM : IsIdempotentElem (Matrix.of (fun i j => a i * star (a j))) := by
    unfold IsIdempotentElem
    ext i j
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    have := g64e_sumS a (a i) (star (a j))
    rw [hS, mul_one] at this
    rw [← this]
  have hEq : columnCanonicalDilation a = g64e_U a 1 0 := by
    ext x y
    rcases x with _ | i <;> rcases y with _ | j <;>
      simp [columnCanonicalDilation, g64e_U, g64e_W, columnRangeComplement, Matrix.one_apply]
  have hU := g64e_U_unitary a 1 0 (star_one _) (star_zero _) (by rw [hS]; simp) (by rw [hS]; simp)
    (by rw [hS]; simp) (by simp)
  refine ⟨⟨hMM.one_sub, ?_⟩, ?_, fun i => rfl, rfl⟩
  · show star (1 - Matrix.of (fun i j => a i * star (a j))) = 1 - Matrix.of (fun i j => a i * star (a j))
    rw [star_sub, star_one, hM]
  · rw [hEq]; exact ⟨hU.1, hU.2⟩


end

end JENS1AcceptedDilation
namespace JENS1AcceptedCyclic
noncomputable section
open QAlgorithms.Papers.Independent.Renew46.P38


theorem g64e_prim (n : ℕ) (hn : 1 ≤ n) : IsPrimitiveRoot (cyclicRoot n) n := by
  unfold cyclicRoot
  exact Complex.isPrimitiveRoot_exp n (by omega)

theorem g64e_star_mul (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    star (cyclicRoot n ^ m) * cyclicRoot n ^ m = 1 := by
  have h := (g64e_prim n hn).norm'_eq_one (by omega)
  rw [show star (cyclicRoot n ^ m) = (starRingEnd ℂ) (cyclicRoot n ^ m) from rfl,
    Complex.conj_mul', norm_pow, h]; simp

theorem g64e_rootsum (n : ℕ) (hn : 1 ≤ n) (i j : Fin n) :
    ∑ k : Fin n, (star (cyclicRoot n ^ (i.val + 1))) ^ (k.val + 1) *
      (cyclicRoot n ^ (j.val + 1)) ^ (k.val + 1) = if i = j then (n : ℂ) else 0 := by
  set θ := cyclicRoot n
  have hθ := g64e_prim n hn
  set w := star (θ ^ (i.val + 1)) * θ ^ (j.val + 1) with hw
  have hterm : ∀ k : Fin n, (star (θ ^ (i.val + 1))) ^ (k.val + 1) *
      (θ ^ (j.val + 1)) ^ (k.val + 1) = w ^ (k.val + 1) := fun k => by rw [hw, mul_pow]
  simp only [hterm]
  split_ifs with hij
  · subst hij
    have : w = 1 := g64e_star_mul n hn _
    simp [this]
  · have hwn : w ^ n = 1 := by
      have e1 : (θ ^ (j.val+1)) ^ n = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hθ.pow_eq_one, one_pow]
      have e2 : (star (θ ^ (i.val+1))) ^ n = 1 := by
        rw [← star_pow, ← pow_mul, mul_comm, pow_mul, hθ.pow_eq_one, one_pow, star_one]
      rw [hw, mul_pow, e1, e2, one_mul]
    have hw1 : w ≠ 1 := by
      intro h1
      apply hij
      have h2 : θ ^ (j.val + 1) = θ ^ (i.val + 1) := by
        have := congrArg (fun z => θ ^ (i.val + 1) * z) h1
        simp only [hw, ← mul_assoc] at this
        rw [mul_comm (θ ^ (i.val + 1)) (star _), g64e_star_mul n hn] at this
        simpa using this
      rw [pow_succ, pow_succ] at h2
      have hθ0 : θ ≠ 0 := hθ.ne_zero (by omega)
      have h3 := mul_right_cancel₀ hθ0 h2
      exact Fin.ext (hθ.pow_inj i.isLt j.isLt h3.symm)
    rw [Fin.sum_univ_eq_sum_range (fun k => w ^ (k + 1)) n]
    simp_rw [pow_succ, ← Finset.sum_mul, geom_sum_eq hw1, hwn]; simp

theorem g64e_avg (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) (Operators H)) :
    IsUnitaryMatrix (cyclicE n) ∧ IsUnitaryMatrix (operatorCyclicE H n) ∧
    (n : ℂ)⁻¹ • (∑ k : Fin n,
      (star (operatorCyclicE H n)) ^ (k.val + 1) * A *
        (operatorCyclicE H n) ^ (k.val + 1)) = Matrix.diagonal (fun i => A i i) := by
  have hs := g64e_star_mul n hn
  have hs' : ∀ m, cyclicRoot n ^ m * star (cyclicRoot n ^ m) = 1 := fun m => by
    rw [mul_comm]; exact hs m
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · simp only [cyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i; exact hs _
  · simp only [cyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i; exact hs' _
  · simp only [operatorCyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i
    simp only [Pi.star_apply, star_smul, star_one, smul_mul_smul_comm, mul_one]
    rw [hs, one_smul]
  · simp only [operatorCyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]; congr 1; funext i
    simp only [Pi.star_apply, star_smul, star_one, smul_mul_smul_comm, mul_one]
    rw [hs', one_smul]
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.smul_apply, Matrix.sum_apply]
    have hk : ∀ k : Fin n, ((star (operatorCyclicE H n)) ^ (k.val+1) * A *
        (operatorCyclicE H n) ^ (k.val+1)) i j =
        ((star (cyclicRoot n ^ (i.val+1))) ^ (k.val+1) * (cyclicRoot n ^ (j.val+1)) ^ (k.val+1)) • A i j := by
      intro k
      simp only [operatorCyclicE, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_pow, Matrix.diagonal_mul, Matrix.mul_diagonal, Pi.pow_apply, Pi.star_apply,
        star_smul, star_one, smul_pow, one_pow, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
        smul_smul]
      (try congr 1) <;> (try simp only [star_pow]) <;> (try ring)
    rw [Finset.sum_congr rfl (fun k _ => hk k), ← Finset.sum_smul, g64e_rootsum n hn i j,
      Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rw [smul_smul, inv_mul_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega)), one_smul]
    · simp

open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal

open QAlgorithms.Papers.Independent.Renew46.P38

universe u

/-- Hansen--Pedersen, Lemma 3.1, PDF p. 6, display (13).
Operator-valued blocks are arbitrary. Powers k.val+1 cover exactly k=1,...,n. -/
theorem cyclicAveraging_proof (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (n : ℕ) (hn : 1 ≤ n)
    (A : Matrix (Fin n) (Fin n) (Operators H)) :
    IsUnitaryMatrix (cyclicE n) ∧ IsUnitaryMatrix (operatorCyclicE H n) ∧
    (n : ℂ)⁻¹ • (∑ k : Fin n,
      (star (operatorCyclicE H n)) ^ (k.val + 1) * A *
        (operatorCyclicE H n) ^ (k.val + 1)) = Matrix.diagonal (fun i => A i i) := by
  exact g64e_avg H n hn A


end

end JENS1AcceptedCyclic

end Inline_JENS1_Accepted


/- Included module: JENS1_Amplification. -/

noncomputable section Inline_JENS1_Amplification
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder InnerProduct CStarAlgebra
namespace QAlgorithms.Papers.Independent.Renew46.P38.AmplificationProof
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Amplified (H : Type u) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

def amplifyOp (T : Operators H) : Operators (Amplified H) :=
  lp.mapCLM 2 (fun _ : ℕ => T) (norm_nonneg T) (fun _ => le_rfl)

omit [CompleteSpace H] in
@[simp] lemma amplifyOp_apply (T : Operators H) (x : Amplified H) (i : ℕ) :
    amplifyOp T x i = T (x i) := rfl

def amplify : Operators H →⋆ₐ[ℂ] Operators (Amplified H) where
  toFun := amplifyOp
  map_zero' := by ext x i; simp
  map_add' T S := by ext x i; simp
  map_one' := by ext x i; simp
  map_mul' T S := by ext x i; simp
  commutes' z := by ext x i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [lp.inner_eq_tsum, amplifyOp_apply]
    apply tsum_congr
    intro i
    exact ContinuousLinearMap.adjoint_inner_left T (y i) (x i)

@[simp] lemma amplify_apply (T : Operators H) (x : Amplified H) (i : ℕ) :
    amplify T x i = T (x i) := rfl

lemma amplify_injective : Function.Injective (amplify (H := H)) := by
  intro T S h
  ext x
  have h' := congrArg (fun A : Operators (Amplified H) => A (lp.single 2 0 x) 0) h
  simpa using h'

lemma amplify_norm_le (T : Operators H) : ‖amplify T‖ ≤ ‖T‖ :=
  lp.norm_mapCLM_le 2 _ (norm_nonneg T) (fun _ => le_rfl)

lemma amplify_continuous : Continuous (amplify (H := H)) := by
  exact ((amplify (H := H)).toLinearMap.mkContinuous 1 (by
    intro x
    simpa using amplify_norm_le x)).continuous


lemma amplify_cfc (f : ℝ → ℝ) (T : Operators H) (hT : IsSelfAdjoint T)
    (hf : ContinuousOn f (spectrum ℝ T)) :
    amplify (cfc f T) = cfc f (amplify T) :=
  (amplify (H := H)).map_cfc f T hf amplify_continuous hT (hT.map amplify)

lemma amplify_inInterval (I : Set ℝ) (T : Operators H) (hT : InInterval I T) :
    InInterval I (amplify T) :=
  ⟨hT.1.map amplify, Set.Subset.trans
    (AlgHom.spectrum_apply_subset ((amplify (H := H)).restrictScalars ℝ) T) hT.2⟩

lemma amplify_le_iff (T S : Operators H) : amplify T ≤ amplify S ↔ T ≤ S := by
  refine ⟨fun h => ?_, fun h => OrderHomClass.mono amplify h⟩
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex] at h ⊢
  intro x
  have h' := h (lp.single 2 0 x)
  simpa [lp.inner_single_right] using h'

omit [CompleteSpace H] in
lemma amplified_infinite [Nontrivial H] : ¬ FiniteDimensional ℂ (Amplified H) := by
  intro hfinite
  let := hfinite
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  let coeL : Amplified H →ₗ[ℂ] (ℕ → H) :=
    { toFun := fun x => x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hi : LinearIndependent ℂ (fun i : ℕ => lp.single 2 i v) := by
    apply LinearIndependent.of_comp coeL
    convert Pi.linearIndependent_single_of_ne_zero (R := ℂ) (ι := ℕ) (fun _ => hv) using 1 <;> rfl
  have hcard := hi.lt_aleph0_of_finiteDimensional
  simp at hcard

lemma amplify_cfc_any (f : ℝ → ℝ) (T : Operators H) (hT : IsSelfAdjoint T) :
    amplify (cfc f T) = cfc f (amplify T) := by
  by_cases hf : ContinuousOn f (spectrum ℝ T)
  · exact amplify_cfc f T hT hf
  · have hf' : ¬ ContinuousOn f (spectrum ℝ (amplify T)) := by
      rwa [hT.map_spectrum_real amplify amplify_injective]
    rw [cfc_apply_of_not_continuousOn _ hf, cfc_apply_of_not_continuousOn _ hf', map_zero]

@[simp] lemma amplify_real_smul (r : ℝ) (T : Operators H) :
    amplify (r • T) = r • amplify T := by
  ext x i
  simp

lemma convex_on_all (I : Set ℝ) (f : ℝ → ℝ)
    (hconv : IntervalOperatorConvex.{u} I f) : ConvexOnOperators H I f := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    intro x y hx hy t ht ht1
    exact le_of_eq (Subsingleton.elim _ _)
  · let := hH
    intro x y hx hy t ht ht1
    have h := hconv (Amplified H) amplified_infinite (amplify x) (amplify y)
      (amplify_inInterval I x hx) (amplify_inInterval I y hy) t ht ht1
    apply (amplify_le_iff _ _).mp
    rw [map_add, amplify_real_smul, amplify_real_smul,
      amplify_cfc_any f x hx.1, amplify_cfc_any f y hy.1,
      amplify_cfc_any f _ (((IsSelfAdjoint.all t).smul hx.1).add
        ((IsSelfAdjoint.all (1-t)).smul hy.1)), map_add,
      amplify_real_smul, amplify_real_smul]
    exact h

def frontOp (T : Operators H × Operators H) : Operators (Amplified H) :=
  lp.mapCLM 2 (fun i : ℕ => if i = 0 then T.1 else T.2)
    (K := max ‖T.1‖ ‖T.2‖)
    (le_trans (norm_nonneg T.1) (le_max_left _ _))
    (fun i => by
      by_cases hi : i = 0
      · simpa only [if_pos hi] using le_max_left ‖T.1‖ ‖T.2‖
      · simpa only [if_neg hi] using le_max_right ‖T.1‖ ‖T.2‖)

omit [CompleteSpace H] in
@[simp] lemma frontOp_apply (T : Operators H × Operators H) (x : Amplified H) (i : ℕ) :
    frontOp T x i = (if i = 0 then T.1 else T.2) (x i) := rfl

def front : (Operators H × Operators H) →⋆ₐ[ℂ] Operators (Amplified H) where
  toFun := frontOp
  map_zero' := by ext x i; by_cases hi : i=0 <;> simp [hi]
  map_add' T S := by ext x i; by_cases hi : i=0 <;> simp [hi]
  map_one' := by ext x i; by_cases hi : i=0 <;> simp [hi]
  map_mul' T S := by ext x i; by_cases hi : i=0 <;> simp [hi]
  commutes' z := by ext x i; by_cases hi : i=0 <;> simp [hi, Algebra.algebraMap_eq_smul_one]
  map_star' T := by
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [lp.inner_eq_tsum, frontOp_apply]
    apply tsum_congr
    intro i
    by_cases hi : i=0
    · simp only [if_pos hi]
      change inner ℂ ((star T.1) (x i)) (y i) = inner ℂ (x i) (T.1 (y i))
      exact ContinuousLinearMap.adjoint_inner_left T.1 (y i) (x i)
    · simp only [if_neg hi]
      change inner ℂ ((star T.2) (x i)) (y i) = inner ℂ (x i) (T.2 (y i))
      exact ContinuousLinearMap.adjoint_inner_left T.2 (y i) (x i)

@[simp] lemma front_apply (T : Operators H × Operators H) (x : Amplified H) (i : ℕ) :
    front T x i = (if i = 0 then T.1 else T.2) (x i) := rfl

lemma front_norm_le (T : Operators H × Operators H) : ‖front T‖ ≤ max ‖T.1‖ ‖T.2‖ := by
  apply lp.norm_mapCLM_le
  · positivity
  · intro i
    by_cases hi : i=0
    · simpa only [if_pos hi] using le_max_left ‖T.1‖ ‖T.2‖
    · simpa only [if_neg hi] using le_max_right ‖T.1‖ ‖T.2‖

lemma front_continuous : Continuous (front (H := H)) := by
  exact ((front (H := H)).toLinearMap.mkContinuous 1 (by
    intro T
    change ‖front T‖ ≤ 1 * ‖T‖
    rw [one_mul, Prod.norm_def]
    exact front_norm_le T)).continuous

lemma front_cfc (f : ℝ → ℝ) (T S : Operators H)
    (hT : IsSelfAdjoint T) (hS : IsSelfAdjoint S)
    (hf : ContinuousOn f (spectrum ℝ T ∪ spectrum ℝ S)) :
    cfc f (front (T,S)) = front (cfc f T,cfc f S) := by
  have hTS : IsSelfAdjoint (T,S) := by exact Prod.ext hT hS
  rw [← front.map_cfc f (T,S) (by simpa only [Prod.spectrum_eq] using hf)
    front_continuous hTS (hTS.map front)]
  rw [cfc_map_prod (S := ℂ) f T S hf hTS hT hS]

lemma front_inInterval (I : Set ℝ) (T S : Operators H)
    (hT : InInterval I T) (hS : InInterval I S) :
    InInterval I (front (T,S)) := by
  have hTS : IsSelfAdjoint (T,S) := by exact Prod.ext hT.1 hS.1
  refine ⟨hTS.map front, Set.Subset.trans
    (AlgHom.spectrum_apply_subset ((front (H := H)).restrictScalars ℝ) (T,S)) ?_⟩
  simpa only [Prod.spectrum_eq, Set.union_subset_iff] using And.intro hT.2 hS.2

lemma front_le_first (T S : Operators H × Operators H) (h : front T ≤ front S) : T.1 ≤ S.1 := by
  rw [ContinuousLinearMap.le_def, ContinuousLinearMap.isPositive_iff_complex] at h ⊢
  intro x
  have h' := h (lp.single 2 0 x)
  simpa [lp.inner_single_right] using h'

end QAlgorithms.Papers.Independent.Renew46.P38.AmplificationProof

end Inline_JENS1_Amplification


/- Included module: JENS2_Blocks. -/

noncomputable section Inline_JENS2_Blocks

open scoped BigOperators ComplexOrder CStarAlgebra
open ContinuousLinearMap

namespace QAlgorithms.Papers.Independent.Renew46.P38.BlockProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The finite operator matrix acting on the Hilbert direct sum. -/
def blockRaw (A : Matrix ι ι (Operators H)) :
    Operators (PiLp 2 (fun _ : ι => H)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j, (A i j).comp (PiLp.proj 2 (fun _ : ι => H) j))

omit [DecidableEq ι] [CompleteSpace H] in
@[simp] lemma blockRaw_apply (A : Matrix ι ι (Operators H))
    (z : PiLp 2 (fun _ : ι => H)) (i : ι) :
    blockRaw A z i = ∑ j, A i j (z j) := by
  simp [blockRaw]

omit [DecidableEq ι] in
lemma blockRaw_star (A : Matrix ι ι (Operators H)) :
    blockRaw (star A) = star (blockRaw A) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  simp only [PiLp.inner_apply, blockRaw_apply, Matrix.star_apply, sum_inner,
    inner_sum, ContinuousLinearMap.star_eq_adjoint, adjoint_inner_left]
  rw [Finset.sum_comm]

/-- Faithful unital star-algebra realization; the domain needs no C*-matrix norm. -/
def block : Matrix ι ι (Operators H) →⋆ₐ[ℂ]
    Operators (PiLp 2 (fun _ : ι => H)) where
  toFun := blockRaw
  map_zero' := by
    ext z i
    simp
  map_add' A B := by
    ext z i
    simp [Finset.sum_add_distrib]
  map_one' := by
    ext z i
    simp only [blockRaw_apply, Matrix.one_apply, one_apply_eq_self]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_mul' A B := by
    ext z i
    simp only [blockRaw_apply, Matrix.mul_apply, sum_apply,
      mul_apply_eq_comp, map_sum]
    rw [Finset.sum_comm]
  commutes' c := by
    ext z i
    simp only [blockRaw_apply, Matrix.algebraMap_matrix_apply, ContinuousLinearMap.algebraMap_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  map_star' := blockRaw_star

@[simp] lemma block_apply (A : Matrix ι ι (Operators H))
    (z : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (block (ι := ι) (H := H)) A z i = ∑ j, A i j (z j) := blockRaw_apply A z i

@[simp] lemma block_single (A : Matrix ι ι (Operators H)) (j i : ι) (u : H) :
    (block (ι := ι) (H := H)) A (PiLp.single 2 j u) i = A i j u := by
  simp [block_apply, PiLp.single_apply, apply_ite]

theorem block_injective : Function.Injective
    (block : Matrix ι ι (Operators H) →⋆ₐ[ℂ] Operators (PiLp 2 (fun _ : ι => H))) := by
  intro A B h
  ext i j u
  simpa only [block_single] using congrArg (fun T : Operators (PiLp 2 (fun _ : ι => H)) =>
    T (PiLp.single 2 j u) i) h

/-- The diagonal realization from the finite product C*-algebra. -/
def diagonalHom : (ι → Operators H) →⋆ₐ[ℂ]
    Operators (PiLp 2 (fun _ : ι => H)) :=
  (block (ι := ι) (H := H)).comp { Matrix.diagonalAlgHom ℂ (n := ι) (α := Operators H) with
    map_star' := by
      intro x
      apply Matrix.ext
      intro i j
      by_cases hij : i = j
      · subst j; simp [Matrix.star_apply]
      · simp [Matrix.star_apply, hij, Ne.symm hij] }

@[simp] lemma diagonalHom_apply (x : ι → Operators H) :
    (diagonalHom (ι := ι) (H := H)) x = (block (ι := ι) (H := H)) (Matrix.diagonal x) := rfl

@[simp] lemma block_diagonal_apply (x : ι → Operators H)
    (z : PiLp 2 (fun _ : ι => H)) (i : ι) :
    (block (ι := ι) (H := H)) (Matrix.diagonal x) z i = x i (z i) := by
  simp only [block_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Ne.symm hji]
  · simp

/-- Spectrum containment, valid also when the index type or Hilbert space is trivial. -/
theorem diagonal_spectrum_subset (x : ι → Operators H) :
    spectrum ℝ ((block (ι := ι) (H := H)) (Matrix.diagonal x)) ⊆ ⋃ i, spectrum ℝ (x i) := by
  have h := AlgHom.spectrum_apply_subset ((diagonalHom (ι := ι) (H := H)).restrictScalars ℝ) x
  change spectrum ℝ ((diagonalHom (ι := ι) (H := H)) x) ⊆ spectrum ℝ x at h
  simpa only [Pi.spectrum_eq, diagonalHom_apply] using h

theorem diagonal_isSelfAdjoint (x : ι → Operators H) (hx : ∀ i, IsSelfAdjoint (x i)) :
    IsSelfAdjoint ((block (ι := ι) (H := H)) (Matrix.diagonal x)) := by
  have h : IsSelfAdjoint x := by
    change star x = x
    funext i
    exact (hx i).star_eq
  exact h.map (diagonalHom (ι := ι) (H := H))

theorem InInterval_diagonal {I : Set ℝ} (x : ι → Operators H)
    (hx : ∀ i, InInterval I (x i)) : InInterval I ((block (ι := ι) (H := H)) (Matrix.diagonal x)) := by
  refine ⟨diagonal_isSelfAdjoint x (fun i => (hx i).1), ?_⟩
  exact (diagonal_spectrum_subset x).trans (Set.iUnion_subset (fun i => (hx i).2))

set_option backward.isDefEq.respectTransparency false in
/-- Continuous functional calculus acts coordinatewise on diagonal blocks. -/
theorem diagonal_cfc (f : ℝ → ℝ) (x : ι → Operators H)
    (hx : ∀ i, IsSelfAdjoint (x i))
    (hf : ContinuousOn f (⋃ i, spectrum ℝ (x i))) :
    cfc f ((block (ι := ι) (H := H)) (Matrix.diagonal x)) =
      (block (ι := ι) (H := H)) (Matrix.diagonal (fun i => cfc f (x i))) := by
  have : ContinuousFunctionalCalculus ℝ (ι → Operators H) IsSelfAdjoint :=
    (IsSelfAdjoint.instIsometricContinuousFunctionalCalculus (A := ι → Operators H)).toContinuousFunctionalCalculus
  have hsa : IsSelfAdjoint x := by
    change star x = x
    funext i
    exact (hx i).star_eq
  have hfc : ContinuousOn f (spectrum ℝ x) := by simpa only [Pi.spectrum_eq] using hf
  have h := (diagonalHom (ι := ι) (H := H)).map_cfc f x hfc
    (by fun_prop) hsa (diagonal_isSelfAdjoint x hx)
  rw [cfc_map_pi (S := ℂ) f x hf hsa hx] at h
  exact h.symm

/-- Positive operators remain positive under coordinate compression. -/
theorem diagonal_le_of_block_le {A B : Matrix ι ι (Operators H)}
    (h : (block (ι := ι) (H := H)) A ≤ (block (ι := ι) (H := H)) B) (i : ι) : A i i ≤ B i i := by
  have hp : ((block (ι := ι) (H := H)) (B - A)).IsPositive := by
    simpa only [map_sub] using (ContinuousLinearMap.le_def _ _).mp h
  have hs : star (B - A) = B - A := block_injective (by
    rw [map_star, hp.isSelfAdjoint.star_eq])
  apply (ContinuousLinearMap.le_def _ _).mpr
  apply ContinuousLinearMap.isPositive_def'.mpr
  constructor
  · have hh := congrArg (fun C : Matrix ι ι (Operators H) => C i i) hs
    change star (B i i - A i i) = B i i - A i i
    simpa only [Matrix.star_apply, Matrix.sub_apply] using hh
  · intro u
    have hh := hp.re_inner_nonneg_left (PiLp.single 2 i u)
    simp only [PiLp.inner_apply, block_single] at hh
    simpa [ContinuousLinearMap.reApplyInnerSelf, PiLp.single_apply,
      apply_ite] using hh

end QAlgorithms.Papers.Independent.Renew46.P38.BlockProof

end Inline_JENS2_Blocks


/- Included module: JENS3_Interval. -/

noncomputable section Inline_JENS3_Interval

namespace QAlgorithms.Papers.Independent.Renew46.P38.IntervalProof

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma exists_common_bounds [Nontrivial (Operators H)] {ι : Type*} [Fintype ι] [Nonempty ι]
    (I : Set ℝ) (x : ι → Operators H) (hx : ∀ i, InInterval I (x i)) :
    ∃ m ∈ I, ∃ M ∈ I, ∀ i,
      algebraMap ℝ (Operators H) m ≤ x i ∧ x i ≤ algebraMap ℝ (Operators H) M := by
  let S : Set ℝ := ⋃ i, spectrum ℝ (x i)
  have hcompact : IsCompact S := isCompact_iUnion fun i =>
    ContinuousFunctionalCalculus.isCompact_spectrum (R := ℝ) (x i)
  have hnonempty : S.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    obtain ⟨r, hr⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) (x i) (hx i).1
    exact ⟨r, Set.mem_iUnion.mpr ⟨i, hr⟩⟩
  have hsub : S ⊆ I := by
    intro r hr
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hr
    exact (hx i).2 hi
  obtain ⟨m, hm, hmin⟩ := hcompact.exists_isLeast hnonempty
  obtain ⟨M, hM, hmax⟩ := hcompact.exists_isGreatest hnonempty
  refine ⟨m, hsub hm, M, hsub hM, fun i => ⟨?_, ?_⟩⟩
  · apply (algebraMap_le_iff_le_spectrum (hx i).1).mpr
    intro r hr
    exact hmin (Set.mem_iUnion.mpr ⟨i, hr⟩)
  · apply (le_algebraMap_iff_spectrum_le (hx i).1).mpr
    intro r hr
    exact hmax (Set.mem_iUnion.mpr ⟨i, hr⟩)

lemma inInterval_of_bounds (I : Set ℝ) (hI : Set.OrdConnected I)
    {z : Operators H} (hz : IsSelfAdjoint z) {m M : ℝ} (hm : m ∈ I) (hM : M ∈ I)
    (hlo : algebraMap ℝ (Operators H) m ≤ z)
    (hup : z ≤ algebraMap ℝ (Operators H) M) : InInterval I z := by
  refine ⟨hz, fun r hr => hI.out hm hM ⟨?_, ?_⟩⟩
  · exact (algebraMap_le_iff_le_spectrum hz).mp hlo r hr
  · exact (le_algebraMap_iff_spectrum_le hz).mp hup r hr

lemma combination_scalar {ι : Type*} [Fintype ι] (a : ι → Operators H)
    (ha : columnSquares a = 1) (r : ℝ) :
    combination a (fun _ => algebraMap ℝ (Operators H) r) = algebraMap ℝ (Operators H) r := by
  simp only [combination, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one,
    smul_mul_assoc, ← Finset.smul_sum]
  exact congrArg (fun z : Operators H => r • z) ha

lemma combination_selfAdjoint {ι : Type*} [Fintype ι] (a x : ι → Operators H)
    (hx : ∀ i, IsSelfAdjoint (x i)) : IsSelfAdjoint (combination a x) := by
  change star (combination a x) = combination a x
  simp only [combination, star_sum]
  exact Finset.sum_congr rfl fun i _ => ((hx i).conjugate' (a i)).star_eq

theorem combination_inInterval {ι : Type*} [Fintype ι]
    (I : Set ℝ) (hI : Set.OrdConnected I)
    (x a : ι → Operators H)
    (hx : ∀ i, InInterval I (x i)) (ha : columnSquares a = 1) :
    InInterval I (combination a x) := by
  rcases subsingleton_or_nontrivial (Operators H) with hsub | hnontrivial
  · exact ⟨Subsingleton.elim _ _, by simp⟩
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    have hzero : (0 : Operators H) = 1 := by
      simpa only [columnSquares, Finset.univ_eq_empty, Finset.sum_empty] using ha
    exact (zero_ne_one hzero).elim
  | inr hi =>
    obtain ⟨m, hm, M, hM, hb⟩ := exists_common_bounds I x hx
    apply inInterval_of_bounds I hI (combination_selfAdjoint a x (fun i => (hx i).1)) hm hM
    · rw [← combination_scalar a ha m]
      exact Finset.sum_le_sum fun i _ => star_left_conjugate_le_conjugate (hb i).1 (a i)
    · rw [← combination_scalar a ha M]
      exact Finset.sum_le_sum fun i _ => star_left_conjugate_le_conjugate (hb i).2 (a i)

theorem convex_inInterval (I : Set ℝ) (hI : Set.OrdConnected I) :
    Convex ℝ {x : Operators H | InInterval I x} := by
  intro x hx y hy a b ha hb hab
  rcases subsingleton_or_nontrivial (Operators H) with hsub | hnontrivial
  · exact ⟨Subsingleton.elim _ _, by simp⟩
  obtain ⟨m, hm, M, hM, hbounds⟩ := exists_common_bounds I ![x, y] (by
    intro i
    fin_cases i <;> assumption)
  have hxlo := (hbounds 0).1
  have hxup := (hbounds 0).2
  have hylo := (hbounds 1).1
  have hyup := (hbounds 1).2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hxlo hxup hylo hyup
  apply inInterval_of_bounds I hI ((IsSelfAdjoint.smul (show IsSelfAdjoint a from rfl) hx.1).add
    (IsSelfAdjoint.smul (show IsSelfAdjoint b from rfl) hy.1)) hm hM
  · have h := add_le_add (smul_le_smul_of_nonneg_left hxlo ha)
      (smul_le_smul_of_nonneg_left hylo hb)
    simpa only [← add_smul, hab, one_smul] using h
  · have h := add_le_add (smul_le_smul_of_nonneg_left hxup ha)
      (smul_le_smul_of_nonneg_left hyup hb)
    simpa only [← add_smul, hab, one_smul] using h

end QAlgorithms.Papers.Independent.Renew46.P38.IntervalProof

end Inline_JENS3_Interval


/- Included module: JENS1_Elementary. -/

noncomputable section Inline_JENS1_Elementary
open scoped BigOperators ComplexOrder
namespace QAlgorithms.Papers.Independent.Renew46.P38.ElementaryProof
universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma scalar_sandwich (t : ℝ) (ht : 0 ≤ t) (x : Operators H) :
    star (Real.sqrt t • (1 : Operators H)) * x * (Real.sqrt t • 1) = t • x := by
  simp [star_smul, smul_smul, Real.mul_self_sqrt ht]

lemma scalar_square (t : ℝ) (ht : 0 ≤ t) :
    star (Real.sqrt t • (1 : Operators H)) * (Real.sqrt t • 1) = t • 1 := by
  simpa using scalar_sandwich (H := H) t ht 1

lemma unital_two_convex (I : Set ℝ) (f : ℝ → ℝ)
    (hJ : UnitalJensenOn H I f 2) : ConvexOnOperators H I f := by
  intro x y hx hy t ht ht1
  have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have ha : columnSquares ![Real.sqrt t • (1 : Operators H), Real.sqrt (1-t) • 1] = 1 := by
    simp only [columnSquares, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      scalar_square t ht, scalar_square (1-t) h1t]
    rw [← add_smul]
    simp
  have h := hJ ![x,y] ![Real.sqrt t • 1,Real.sqrt (1-t) • 1]
    (by intro i; fin_cases i <;> assumption) ha
  simpa only [combination, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, scalar_sandwich t ht, scalar_sandwich (1-t) h1t] using h

lemma allUnital_convex (I : Set ℝ) (f : ℝ → ℝ)
    (hJ : ∀ n : ℕ, 1 ≤ n → AllUnitalJensen.{u} I f n) :
    IntervalOperatorConvex.{u} I f := by
  intro H _ _ _ _
  exact unital_two_convex I f (hJ 2 (by omega) H)

lemma allUnital_isometry (I : Set ℝ) (f : ℝ → ℝ)
    (hJ : ∀ n : ℕ, 1 ≤ n → AllUnitalJensen.{u} I f n) :
    IsometryJensen.{u} I f := by
  intro H _ _ _ _ v x hv hx
  simpa [combination, columnSquares] using
    hJ 1 le_rfl H (fun _ => x) (fun _ => v) (fun _ => hx)
      (by simpa [columnSquares] using hv)

lemma scalar_inInterval (I : Set ℝ) (s : ℝ) (hs : s ∈ I) :
    InInterval I (s • (1 : Operators H)) := by
  refine ⟨(IsSelfAdjoint.all s).smul (IsSelfAdjoint.one _), ?_⟩
  rcases subsingleton_or_nontrivial (Operators H) with h | h
  · let := h
    simp [spectrum.of_subsingleton]
  · let := h
    simpa only [← Algebra.algebraMap_eq_smul_one, spectrum.scalar_eq,
      Set.singleton_subset_iff] using hs

lemma allUnital_pinching (I : Set ℝ) (f : ℝ → ℝ)
    (hJ : ∀ n : ℕ, 1 ≤ n → AllUnitalJensen.{u} I f n) :
    PinchingJensen.{u} I f := by
  intro H _ _ _ _ p x hp hx s hs
  have ha : columnSquares ![p, 1-p] = 1 := by
    simp [columnSquares, Fin.sum_univ_two, hp.isSelfAdjoint.star_eq,
      hp.one_sub.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
      hp.one_sub.isIdempotentElem.eq]
  have h := hJ 2 (by omega) H ![x, s • 1] ![p, 1-p]
    (by intro i; fin_cases i; exact hx; exact scalar_inInterval I s hs) ha
  have hc : combination ![p, 1-p] ![x, s • 1] = p*x*p + s • (1-p) := by
    simp [combination, Fin.sum_univ_two, hp.isSelfAdjoint.star_eq,
      hp.one_sub.isSelfAdjoint.star_eq,
      hp.one_sub.isIdempotentElem.eq]
  rw [hc] at h
  have hc' := star_left_conjugate_le_conjugate h p
  simp only [combination, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    hp.isSelfAdjoint.star_eq, hp.one_sub.isSelfAdjoint.star_eq,
    mul_add, ← mul_assoc, hp.isIdempotentElem.eq, hp.mul_one_sub_self,
    zero_mul, add_zero] at hc'
  simpa only [mul_assoc, hp.isIdempotentElem.eq] using hc'

end QAlgorithms.Papers.Independent.Renew46.P38.ElementaryProof

end Inline_JENS1_Elementary


/- Included module: JENS4_Shift. -/

noncomputable section Inline_JENS4_Shift
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators InnerProduct ComplexOrder

namespace QAlgorithms.Papers.Independent.Renew46.P38.ShiftProof

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev ShiftSpace (H : Type*) [NormedAddCommGroup H] := lp (fun _ : ℕ => H) 2

def coordinateIso (i : ℕ) : H →ₗᵢ[ℂ] ShiftSpace H where
  toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : ℕ => H) 2 i
  norm_map' u := lp.norm_single (E := fun _ : ℕ => H) (by norm_num : (0 : ENNReal) < 2) i u

omit [CompleteSpace H] in
@[simp] lemma coordinateIso_apply (i : ℕ) (u : H) :
    coordinateIso i u = lp.single 2 i u := rfl

omit [CompleteSpace H] in
lemma successor_orthogonal : OrthogonalFamily ℂ (fun _ : ℕ => H)
    (fun i => coordinateIso (i+1)) := by
  intro i j hij u v
  simp only [coordinateIso_apply, lp.inner_single_left]
  rw [lp.single_apply_ne (E := fun _ : ℕ => H) 2 (j+1) v (by omega)]
  simp

def shiftIsometry : ShiftSpace H →ₗᵢ[ℂ] ShiftSpace H :=
  (successor_orthogonal (H := H)).linearIsometry

def shift : Operators (ShiftSpace H) := shiftIsometry.toContinuousLinearMap

@[simp] lemma shift_single (i : ℕ) (u : H) :
    shift (lp.single 2 i u) = lp.single 2 (i+1) u := by
  exact (successor_orthogonal (H := H)).linearIsometry_apply_single u

lemma star_shift_mul_shift : star (shift (H := H)) * shift = 1 :=
  (shiftIsometry (H := H)).adjoint_comp_self

@[simp] lemma star_shift_apply (z : ShiftSpace H) (i : ℕ) :
    star (shift (H := H)) z i = z (i+1) := by
  apply ext_inner_left ℂ
  intro u
  calc
    inner ℂ u (star (shift (H := H)) z i) =
        inner ℂ (lp.single 2 i u) (star (shift (H := H)) z) :=
      (lp.inner_single_left (𝕜 := ℂ) (G := fun _ : ℕ => H) i u _).symm
    _ = inner ℂ (shift (lp.single 2 i u)) z :=
      ContinuousLinearMap.adjoint_inner_right shift _ z
    _ = inner ℂ u (z (i+1)) := by rw [shift_single, lp.inner_single_left]

@[simp] lemma shift_apply_zero (z : ShiftSpace H) : shift z 0 = 0 := by
  have h : (lp.evalCLM ℂ (fun _ : ℕ => H) 2 0).comp shift = 0 := by
    apply lp.ext_continuousLinearMap (by norm_num)
    intro i
    ext u
    change shift (lp.single 2 i u) 0 = 0
    rw [shift_single]
    exact lp.single_apply_ne (E := fun _ : ℕ => H) 2 (i+1) u (by omega)
  exact congrArg (fun T : ShiftSpace H →L[ℂ] H => T z) h

@[simp] lemma shift_apply_succ (z : ShiftSpace H) (i : ℕ) : shift z (i+1) = z i := by
  have h := congrArg (fun T : Operators (ShiftSpace H) => T z i)
    (star_shift_mul_shift (H := H))
  simpa only [mul_apply_eq_comp, star_shift_apply, one_apply_eq_self] using h

open AmplificationProof

def stabilized (p : Operators H) : Operators (Amplified H) :=
  amplify p + shift * amplify (1-p)

@[simp] lemma stabilized_apply_zero (p : Operators H) (z : Amplified H) :
    stabilized p z 0 = p (z 0) := by
  simp [stabilized, mul_apply_eq_comp]

@[simp] lemma stabilized_apply_succ (p : Operators H) (z : Amplified H) (i : ℕ) :
    stabilized p z (i+1) = p (z (i+1)) + (1-p) (z i) := by
  simp [stabilized, mul_apply_eq_comp]

@[simp] lemma star_stabilized_apply (p : Operators H) (hp : IsStarProjection p)
    (z : Amplified H) (i : ℕ) :
    star (stabilized p) z i = p (z i) + (1-p) (z (i+1)) := by
  simp only [stabilized, star_add, star_mul, ← map_star,
    hp.isSelfAdjoint.star_eq, hp.one_sub.isSelfAdjoint.star_eq,
    add_apply, lp.coeFn_add, Pi.add_apply, mul_apply_eq_comp, amplify_apply, star_shift_apply]

lemma stabilized_isometry (p : Operators H) (hp : IsStarProjection p) :
    star (stabilized p) * stabilized p = 1 := by
  have pp (u : H) : p (p u) = p u :=
    congrArg (fun T : Operators H => T u) hp.isIdempotentElem
  ext z i
  cases i with
  | zero =>
    simp [mul_apply_eq_comp, star_stabilized_apply p hp, map_add, map_sub, pp]
  | succ i =>
    simp [mul_apply_eq_comp, star_stabilized_apply p hp, map_add, map_sub, pp]

lemma stabilized_compression (p : Operators H) (hp : IsStarProjection p)
    (x : Operators H) (s : ℝ) :
    star (stabilized p) * front (x, s • 1) * stabilized p =
      front (p*x*p + s • (1-p), s • 1) := by
  have pp (u : H) : p (p u) = p u :=
    congrArg (fun T : Operators H => T u) hp.isIdempotentElem
  ext z i
  cases i with
  | zero =>
    simp [mul_apply_eq_comp, star_stabilized_apply p hp, front_apply,
      map_add, map_sub, smul_sub, pp]
  | succ i =>
    simp [mul_apply_eq_comp, star_stabilized_apply p hp, front_apply,
      map_add, map_sub, smul_sub, pp]

theorem exists_stabilized_isometry (p : Operators H) (hp : IsStarProjection p) :
    ∃ v : Operators (Amplified H), star v * v = 1 ∧
      ∀ (x : Operators H) (s : ℝ),
        star v * front (x, s • 1) * v =
          front (p*x*p + s • (1-p), s • 1) :=
  ⟨stabilized p, stabilized_isometry p hp, stabilized_compression p hp⟩

end QAlgorithms.Papers.Independent.Renew46.P38.ShiftProof

end Inline_JENS4_Shift


/- Included module: JENS5_Pinching. -/

noncomputable section Inline_JENS5_Pinching
open scoped BigOperators ComplexOrder CStarAlgebra
open ContinuousLinearMap
set_option backward.isDefEq.respectTransparency false
namespace QAlgorithms.Papers.Independent.Renew46.P38.PinchingProof
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev BMat (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Matrix (Fin 2) (Fin 2) (Operators H)

noncomputable def rotation (a b : ℝ) : BMat H :=
  !![a • 1, b • 1; b • 1, -a • 1]

lemma rotation_star (a b : ℝ) : star (rotation (H := H) a b) = rotation a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation, Matrix.star_apply]

omit [CompleteSpace H] in
lemma rotation_square (a b : ℝ) (hab : a*a+b*b=1) :
    rotation (H := H) a b * rotation a b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, smul_smul, ← add_smul,
      mul_comm a b, hab, add_comm (b*b) (a*a)]

omit [CompleteSpace H] in
lemma rotation_diag_zero (a b : ℝ) (x y : Operators H) :
    ((rotation (H := H) a b * Matrix.diagonal ![x,y] * rotation a b) : BMat H) 0 0 =
      (a*a) • x + (b*b) • y := by
  simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
    smul_smul, Matrix.vecMul, dotProduct]

noncomputable def firstProjection : BMat H := Matrix.diagonal ![1,0]

lemma firstProjection_star : star (firstProjection (H := H)) = firstProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [firstProjection, Matrix.star_apply]

omit [CompleteSpace H] in
lemma firstProjection_square : firstProjection (H := H) * firstProjection = firstProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstProjection, Matrix.mul_apply, Matrix.diagonal_apply]

omit [CompleteSpace H] in
lemma compress_eq (M : BMat H) :
    firstProjection * M * firstProjection = Matrix.diagonal ![M 0 0,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstProjection, Matrix.mul_apply, Matrix.diagonal_apply]

omit [CompleteSpace H] in
lemma pinch_eq (M : BMat H) (s : ℝ) :
    firstProjection * M * firstProjection + s • (1-firstProjection) =
      Matrix.diagonal ![M 0 0,s • 1] := by
  rw [compress_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [firstProjection]

lemma block_smul (s : ℝ) (M : BMat H) :
    (BlockProof.block (H := H) (ι := Fin 2)) (s • M) = s • (BlockProof.block (H := H) (ι := Fin 2)) M := by
  ext z i
  simp [BlockProof.block_apply]

omit [CompleteSpace H] in
lemma power_infinite (hH : ¬ FiniteDimensional ℂ H) :
    ¬ FiniteDimensional ℂ (HilbertPower H 2) := by
  intro h
  let := h
  apply hH
  exact FiniteDimensional.of_surjective (PiLp.proj 2 (fun _ : Fin 2 => H) 0).toLinearMap
    (fun y => ⟨PiLp.single 2 0 y, by simp⟩)

lemma conjugate_cfc {A : Type*} [CStarAlgebra A] (U : unitary A)
    (x : A) (hx : IsSelfAdjoint x) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ x)) :
    cfc f ((U:A)*x*star (U:A)) = (U:A)*cfc f x*star (U:A) := by
  exact (StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ A U) f x hf
    (by fun_prop) hx (hx.conjugate U)).symm

lemma scalar_inInterval (I : Set ℝ) (s : ℝ) (hs : s ∈ I) :
    InInterval I (s • (1 : Operators H)) := by
  refine ⟨(IsSelfAdjoint.all s).smul (IsSelfAdjoint.one _), ?_⟩
  rcases subsingleton_or_nontrivial (Operators H) with h | h
  · simp [spectrum.of_subsingleton]
  · simpa only [← Algebra.algebraMap_eq_smul_one, spectrum.scalar_eq,
      Set.singleton_subset_iff] using hs

lemma unitary_inInterval {A : Type*} [CStarAlgebra A] (I : Set ℝ)
    (U : unitary A) {x : A} (hx : InInterval I x) :
    InInterval I ((U:A)*x*star (U:A)) := by
  refine ⟨hx.1.conjugate U, ?_⟩
  exact (AlgHom.spectrum_apply_subset
    ((Unitary.conjStarAlgAut ℂ A U).toAlgEquiv.toAlgHom.restrictScalars ℝ) x).trans hx.2

theorem pinching_convex (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I)
    (hpinch : PinchingJensen.{u} I f) : IntervalOperatorConvex.{u} I f := by
  intro H _ _ _ hH x y hx hy t ht ht1
  have h1t : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have hnt : ¬ Subsingleton H := by
    intro h
    let := h
    exact hH (inferInstance : FiniteDimensional ℂ H)
  let : Nontrivial H := not_subsingleton_iff_nontrivial.mp hnt
  obtain ⟨s, hs⟩ := ContinuousFunctionalCalculus.spectrum_nonempty (R := ℝ) x hx.1
  have hsI : s ∈ I := hx.2 hs
  let B := BlockProof.block (ι := Fin 2) (H := H)
  let R : BMat H := rotation (Real.sqrt t) (Real.sqrt (1-t))
  let P : BMat H := firstProjection
  let D : BMat H := Matrix.diagonal ![x,y]
  let Z : BMat H := R*D*R
  let z : Operators H := t • x+(1-t) • y
  have hz : InInterval I z :=
    (IntervalProof.convex_inInterval I hI) hx hy ht h1t (by ring)
  have hRstar : star R = R := rotation_star _ _
  have hRsq : R*R=1 := rotation_square _ _ (by
    rw [Real.mul_self_sqrt ht, Real.mul_self_sqrt h1t]; ring)
  have hBRstar : star (B R) = B R := by rw [← map_star, hRstar]
  have hBRsq : B R * B R = 1 := by rw [← map_mul, hRsq, map_one]
  let U : unitary (Operators (HilbertPower H 2)) :=
    ⟨B R, by simp only [Unitary.mem_iff, hBRstar, hBRsq, and_self]⟩
  have hD : InInterval I (B D) := BlockProof.InInterval_diagonal ![x,y]
    (by intro i; fin_cases i <;> assumption)
  have hZeq : B Z = (U : Operators (HilbertPower H 2)) * B D * star (U : Operators (HilbertPower H 2)) := by
    simp only [Z, map_mul, U, hBRstar]
  have hZ : InInterval I (B Z) := hZeq.symm ▸ unitary_inInterval I U hD
  have hZzero : Z 0 0 = z := by
    simp only [Z, R, D, rotation_diag_zero, Real.mul_self_sqrt ht,
      Real.mul_self_sqrt h1t, z]
  have hP : IsStarProjection (B P) := by
    apply IsStarProjection.map (f := B)
    exact ⟨firstProjection_square, firstProjection_star⟩
  have h := hpinch (HilbertPower H 2) (power_infinite hH) (B P) (B Z) hP hZ s hsI
  have hpin : B P * B Z * B P + s • (1-B P) = B (Matrix.diagonal ![z,s • 1]) := by
    have he := congrArg B (pinch_eq Z s)
    simpa only [map_add, map_mul, map_sub, map_one, block_smul, hZzero, P, B] using he
  have hfcZ : cfc f (B Z) = B (R * Matrix.diagonal ![cfc f x,cfc f y] * R) := by
    rw [hZeq, conjugate_cfc U (B D) hD.1 f (hf.mono hD.2)]
    have hc := BlockProof.diagonal_cfc f ![x,y]
      (by intro i; fin_cases i; exact hx.1; exact hy.1)
      (hf.mono (Set.iUnion_subset fun i => by fin_cases i; exact hx.2; exact hy.2))
    change cfc f (B D) = B (Matrix.diagonal (fun i => cfc f (![x,y] i))) at hc
    rw [hc]
    simp only [map_mul, U, hBRstar]
    rfl
  have hscalar := scalar_inInterval (H := H) I s hsI
  have hfcPin : cfc f (B (Matrix.diagonal ![z,s • 1])) =
      B (Matrix.diagonal ![cfc f z,cfc f (s • 1)]) := by
    have hc := BlockProof.diagonal_cfc f ![z,s • 1]
      (by intro i; fin_cases i; exact hz.1; exact hscalar.1)
      (hf.mono (Set.iUnion_subset fun i => by fin_cases i; exact hz.2; exact hscalar.2))
    convert hc using 1
    congr 2
    ext i
    fin_cases i <;> rfl
  rw [hpin, hfcPin, hfcZ] at h
  have hb : B (P * Matrix.diagonal ![cfc f z,cfc f (s • 1)] * P) ≤
      B (P * (R * Matrix.diagonal ![cfc f x,cfc f y] * R) * P) := by
    simpa only [map_mul] using h
  have hh := BlockProof.diagonal_le_of_block_le hb 0
  simpa only [P, compress_eq, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
    R, rotation_diag_zero, Real.mul_self_sqrt ht, Real.mul_self_sqrt h1t] using hh

end QAlgorithms.Papers.Independent.Renew46.P38.PinchingProof

end Inline_JENS5_Pinching


/- Included module: JENS1_Isometry. -/

noncomputable section Inline_JENS1_Isometry
open scoped BigOperators ComplexOrder CStarAlgebra
set_option backward.isDefEq.respectTransparency false
namespace QAlgorithms.Papers.Independent.Renew46.P38.IsometryProof
universe u
open AmplificationProof ElementaryProof

lemma isometry_pinching (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I)
    (hIso : IsometryJensen.{u} I f) : PinchingJensen.{u} I f := by
  intro H _ _ _ _ p x hp hx s hs
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    exact le_of_eq (Subsingleton.elim _ _)
  let := hH
  have hsI : InInterval I (s • (1 : Operators H)) := scalar_inInterval I s hs
  have ha : columnSquares ![p, 1-p] = 1 := by
    simp [columnSquares, Fin.sum_univ_two, hp.isSelfAdjoint.star_eq,
      hp.one_sub.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq,
      hp.one_sub.isIdempotentElem.eq]
  have hc : combination ![p, 1-p] ![x, s • 1] = p*x*p + s • (1-p) := by
    simp [combination, Fin.sum_univ_two, hp.isSelfAdjoint.star_eq,
      hp.one_sub.isSelfAdjoint.star_eq, hp.one_sub.isIdempotentElem.eq]
  have hz : InInterval I (p*x*p+s•(1-p)) := by
    rw [← hc]
    exact IntervalProof.combination_inInterval I hI ![x,s•1] ![p,1-p]
      (by intro i; fin_cases i; exact hx; exact hsI) ha
  obtain ⟨v, hv, hcomp⟩ := ShiftProof.exists_stabilized_isometry p hp
  have h := hIso (Amplified H) (amplified_infinite (H := H)) v (front (x,s•1)) hv
    (front_inInterval I x (s•1) hx hsI)
  rw [hcomp x s] at h
  rw [front_cfc f _ _ hz.1 hsI.1 (hf.mono (Set.union_subset hz.2 hsI.2)),
    front_cfc f _ _ hx.1 hsI.1 (hf.mono (Set.union_subset hx.2 hsI.2))] at h
  have hscalar : cfc f (s • (1 : Operators H)) = f s • 1 := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (cfc_algebraMap (A := Operators H) s f)
  rw [hscalar, hcomp (cfc f x) (f s)] at h
  have h' := front_le_first _ _ h
  have h'' := star_left_conjugate_le_conjugate h' p
  simp only [hp.isSelfAdjoint.star_eq, mul_add, mul_smul_comm,
    ← mul_assoc, hp.isIdempotentElem.eq, hp.mul_one_sub_self,
    smul_zero, add_zero] at h''
  simpa only [mul_assoc, hp.isIdempotentElem.eq] using h''

end QAlgorithms.Papers.Independent.Renew46.P38.IsometryProof

end Inline_JENS1_Isometry


/- Included module: JENS6_Unital. -/

noncomputable section Inline_JENS6_Unital
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 80000
open scoped BigOperators ComplexOrder CStarAlgebra
namespace QAlgorithms.Papers.Independent.Renew46.P38.UnitalProof
open BlockProof IntervalProof
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma convex_cfc (I : Set ℝ) (f : ℝ → ℝ) (hI : Set.OrdConnected I)
    (hconv : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ConvexOnOperators H I f) :
    ConvexOn ℝ {x : Operators H | InInterval I x} (cfc f) := by
  refine ⟨convex_inInterval I hI, ?_⟩
  intro x hx y hy a b ha hb hab
  have hb' : b = 1-a := by linarith
  subst b
  exact hconv H x y hx hy a ha (by linarith)

set_option maxHeartbeats 1000000 in
lemma finite_jensen (I : Set ℝ) (f : ℝ → ℝ) (hI : Set.OrdConnected I)
    (hconv : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K], ConvexOnOperators K I f)
    {ι : Type*} [Fintype ι] (X : ι → Operators H) (hX : ∀ i, InInterval I (X i))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    cfc f (∑ i, w i • X i) ≤ ∑ i, w i • cfc f (X i) := by
  exact (convex_cfc (H := H) I f hI hconv).map_sum_le
    (E := Operators H) (β := Operators H) (t := Finset.univ) (w := w) (p := X)
    (fun i _ => hw i) hs (fun i _ => hX i)

omit [CompleteSpace H] in
lemma real_average_eq_complex (n : ℕ) (z : Fin n → Operators H) :
    (∑ k, (n : ℝ)⁻¹ • z k) = (n : ℂ)⁻¹ • ∑ k, z k := by
  rw [← Finset.smul_sum, RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_inv, RCLike.ofReal_natCast]

lemma inInterval_conj (I : Set ℝ) (x : Operators H) (hx : InInterval I x)
    (U : unitary (Operators H)) :
    InInterval I (star (U : Operators H) * x * U) := by
  refine ⟨hx.1.conjugate' U, ?_⟩
  simpa only [Unitary.spectrum_star_left_conjugate] using hx.2

lemma cfc_conj (f : ℝ → ℝ) (x : Operators H) (hx : IsSelfAdjoint x)
    (hf : ContinuousOn f (spectrum ℝ x)) (U : unitary (Operators H)) :
    cfc f (star (U : Operators H) * x * U) = star (U : Operators H) * cfc f x * U := by
  have h := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (Operators H) (star U))
    f x hf (by fun_prop) hx (hx.map _)
  simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] using h.symm

def blockUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (Operators H)) (hU : IsUnitaryMatrix U) :
    unitary (Operators (PiLp 2 (fun _ : ι => H))) :=
  ⟨(block (ι := ι) (H := H)) U, by
    rw [Unitary.mem_iff]
    constructor
    · rw [← map_star, ← map_mul, hU.1, map_one]
    · rw [← map_star, ← map_mul, hU.2, map_one]⟩

@[simp] lemma coe_blockUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (Operators H)) (hU : IsUnitaryMatrix U) :
    (blockUnitary U hU : Operators (PiLp 2 (fun _ : ι => H))) = (block (ι := ι) (H := H)) U := rfl

lemma cyclic_block (n : ℕ) (hn : 1 ≤ n) (A : Matrix (Fin n) (Fin n) (Operators H)) :
    ∑ k : Fin n, (n : ℝ)⁻¹ • (block (ι := Fin n) (H := H)) ((star (operatorCyclicE H n)) ^ (k.val+1) * A *
      (operatorCyclicE H n) ^ (k.val+1)) = (block (ι := Fin n) (H := H)) (Matrix.diagonal (fun i => A i i)) := by
  have h := congrArg (block (ι := Fin n) (H := H))
    (JENS1AcceptedCyclic.cyclicAveraging_proof H n hn A).2.2
  rw [map_smul, map_sum] at h
  rw [real_average_eq_complex]
  exact h

lemma pinching_diagonal (I : Set ℝ) (f : ℝ → ℝ) (hI : Set.OrdConnected I)
    (hf : ContinuousOn f I) (hconv : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ConvexOnOperators H I f)
    (n : ℕ) (hn : 1 ≤ n) (A F : Matrix (Fin n) (Fin n) (Operators H))
    (hA : InInterval I ((block (ι := Fin n) (H := H)) A)) (hdiag : ∀ i, InInterval I (A i i))
    (hF : cfc f ((block (ι := Fin n) (H := H)) A) = (block (ι := Fin n) (H := H)) F) : ∀ i, cfc f (A i i) ≤ F i i := by
  let E := operatorCyclicE H n
  have hE : IsUnitaryMatrix E :=
    (JENS1AcceptedCyclic.cyclicAveraging_proof H n hn A).2.1
  let U : unitary (Operators (HilbertPower H n)) := blockUnitary E hE
  let X : Fin n → Operators (HilbertPower H n) := fun k =>
    star ((U ^ (k.val+1) : unitary _) : Operators (HilbertPower H n)) * (block (ι := Fin n) (H := H)) A * (U ^ (k.val+1))
  have hX : ∀ k, InInterval I (X k) := fun k => inInterval_conj I ((block (ι := Fin n) (H := H)) A) hA _
  have hw : ∑ _ : Fin n, (n : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (show n ≠ 0 by omega))
  have hJ := finite_jensen I f hI hconv X hX (fun _ : Fin n => (n : ℝ)⁻¹)
    (fun _ => by positivity) hw
  have hleft : (∑ k : Fin n, (n : ℝ)⁻¹ • X k) = (block (ι := Fin n) (H := H)) (Matrix.diagonal (fun i => A i i)) := by
    convert cyclic_block n hn A using 1
    apply Finset.sum_congr rfl
    intro k _
    simp only [X, U, E, SubmonoidClass.coe_pow, star_pow, coe_blockUnitary, map_mul, map_pow, map_star]
  have hright : (∑ k : Fin n, (n : ℝ)⁻¹ • cfc f (X k)) =
      (block (ι := Fin n) (H := H)) (Matrix.diagonal (fun i => F i i)) := by
    convert cyclic_block n hn F using 1
    apply Finset.sum_congr rfl
    intro k _
    have hc : cfc f (X k) =
        star ((U ^ (k.val+1) : unitary _) : Operators (HilbertPower H n)) *
          cfc f ((block (ι := Fin n) (H := H)) A) *
          ((U ^ (k.val+1) : unitary _) : Operators (HilbertPower H n)) :=
      cfc_conj f ((block (ι := Fin n) (H := H)) A) hA.1 (hf.mono hA.2) (U ^ (k.val + 1))
    rw [hc, hF]
    simp only [U, E, SubmonoidClass.coe_pow, star_pow, coe_blockUnitary, map_mul, map_pow, map_star]
  rw [hleft, hright, diagonal_cfc f (fun i => A i i) (fun i => (hdiag i).1)
    (hf.mono (Set.iUnion_subset fun i => (hdiag i).2))] at hJ
  intro i
  simpa only [Matrix.diagonal_apply_eq] using diagonal_le_of_block_le hJ i

lemma column_unital {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (Operators H)) (hU : IsUnitaryMatrix U) (j : ι) :
    columnSquares (fun i => U i j) = 1 := by
  have h := congrArg (fun M : Matrix ι ι (Operators H) => M j j) hU.1
  simpa only [columnSquares, Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] using h

lemma conjugated_diagonal_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (Operators H)) (x : ι → Operators H) (j : ι) :
    (star U * Matrix.diagonal x * U) j j = combination (fun i => U i j) x := by
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, combination,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma unitary_column_jensen (I : Set ℝ) (f : ℝ → ℝ) (hI : Set.OrdConnected I)
    (hf : ContinuousOn f I)
    (hconv : ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K], ConvexOnOperators K I f)
    (n : ℕ) (hn : 1 ≤ n) (x : Fin n → Operators H) (hx : ∀ i, InInterval I (x i))
    (U : Matrix (Fin n) (Fin n) (Operators H)) (hU : IsUnitaryMatrix U) (j : Fin n) :
    cfc f (combination (fun i => U i j) x) ≤ combination (fun i => U i j) (fun i => cfc f (x i)) := by
  let A := star U * Matrix.diagonal x * U
  let F := star U * Matrix.diagonal (fun i => cfc f (x i)) * U
  have hxblock := InInterval_diagonal x hx
  have hA : InInterval I ((block (ι := Fin n) (H := H)) A) := by
    simpa only [A, coe_blockUnitary, map_mul, map_star] using
      inInterval_conj I ((block (ι := Fin n) (H := H)) (Matrix.diagonal x))
        hxblock (blockUnitary U hU)
  have hdiag (i : Fin n) : InInterval I (A i i) := by
    change InInterval I ((star U * Matrix.diagonal x * U) i i)
    rw [conjugated_diagonal_entry]
    exact combination_inInterval I hI x _ hx (column_unital U hU i)
  have hF : cfc f ((block (ι := Fin n) (H := H)) A) =
      (block (ι := Fin n) (H := H)) F := by
    have h := cfc_conj f ((block (ι := Fin n) (H := H)) (Matrix.diagonal x))
      hxblock.1 (hf.mono hxblock.2) (blockUnitary U hU)
    rw [diagonal_cfc f x (fun i => (hx i).1)
      (hf.mono (Set.iUnion_subset fun i => (hx i).2))] at h
    simpa only [A, F, coe_blockUnitary, map_mul, map_star] using h
  have h := pinching_diagonal I f hI hf hconv n hn A F hA hdiag hF j
  simpa only [A, F, conjugated_diagonal_entry] using h

lemma reindex_unitary {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (U : Matrix ι ι (Operators H)) (hU : IsUnitaryMatrix U) :
    IsUnitaryMatrix ((Matrix.reindexAlgEquiv ℂ (Operators H) e) U) := by
  let R := Matrix.reindexAlgEquiv ℂ (Operators H) e
  have hs (A : Matrix ι ι (Operators H)) : R (star A) = star (R A) := by
    ext i j
    rfl
  constructor
  · change star (R U) * R U = 1
    rw [← hs, ← map_mul, hU.1, map_one]
  · change R U * star (R U) = 1
    rw [← hs, ← map_mul, hU.2, map_one]

theorem allUnital_of_allConvex (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I)
    (hconv : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ConvexOnOperators H I f) :
    ∀ n : ℕ, 1 ≤ n → AllUnitalJensen.{u} I f n := by
  intro n hn H _ _ _ x a hx ha
  let e : Option (Fin n) ≃ Fin (n+1) := (finSuccEquiv n).symm
  let U := (Matrix.reindexAlgEquiv ℂ (Operators H) e) (columnCanonicalDilation a)
  have hU : IsUnitaryMatrix U := reindex_unitary e _
    (JENS1AcceptedDilation.canonicalDilation_proof H n hn a ha).2.1
  let y : Option (Fin n) → Operators H := fun i =>
    match i with
    | none => x ⟨0, by omega⟩
    | some j => x j
  have hy : ∀ i, InInterval I (y (e.symm i)) := by
    intro i
    cases e.symm i <;> apply hx
  have h := unitary_column_jensen I f hI hf hconv (n+1) (by omega)
    (fun i => y (e.symm i)) hy U hU (e none)
  have hc (z : Option (Fin n) → Operators H) :
      combination (fun i => U i (e none)) (fun i => z (e.symm i)) =
        combination a (fun i => z (some i)) := by
    change (∑ i, star ((columnCanonicalDilation a) (e.symm i) (e.symm (e none))) *
      z (e.symm i) * (columnCanonicalDilation a) (e.symm i) (e.symm (e none))) = _
    simp only [e.symm_apply_apply]
    let g : Option (Fin n) → Operators H := fun i =>
      star (columnCanonicalDilation a i none) * z i * columnCanonicalDilation a i none
    change (∑ i, g (e.symm i)) = _
    calc
      _ = ∑ i, g i := e.symm.sum_comp g
      _ = _ := by simp [g, Fintype.sum_option, columnCanonicalDilation, combination]

  rw [hc y, hc (fun i => cfc f (y i))] at h
  exact h

end QAlgorithms.Papers.Independent.Renew46.P38.UnitalProof

end Inline_JENS6_Unital


/- Included module: JENS1_Assembly. -/

noncomputable section Inline_JENS1_Assembly
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open QAlgorithms.Papers.Independent.Renew46.P38
universe u

/-- The original Hansen--Pedersen operator Jensen equivalences, with arbitrary
complete complex Hilbert spaces and the original infinite-space convexity predicate. -/
theorem solution (I : Set ℝ) (f : ℝ → ℝ)
    (hI : Set.OrdConnected I) (hf : ContinuousOn f I) :
    (IntervalOperatorConvex.{u} I f ↔ ∀ n : ℕ, 1 ≤ n → AllUnitalJensen.{u} I f n) ∧
    (IntervalOperatorConvex.{u} I f ↔ IsometryJensen.{u} I f) ∧
    (IntervalOperatorConvex.{u} I f ↔ PinchingJensen.{u} I f) := by
  have hforward : IntervalOperatorConvex.{u} I f →
      ∀ n : ℕ, 1 ≤ n → AllUnitalJensen.{u} I f n := by
    intro hconv
    apply UnitalProof.allUnital_of_allConvex I f hI hf
    intro H _ _ _
    exact AmplificationProof.convex_on_all I f hconv
  refine ⟨⟨hforward, ElementaryProof.allUnital_convex I f⟩, ?_, ?_⟩
  · exact ⟨fun h => ElementaryProof.allUnital_isometry I f (hforward h),
      fun h => PinchingProof.pinching_convex I f hI hf
        (IsometryProof.isometry_pinching I f hI hf h)⟩
  · exact ⟨fun h => ElementaryProof.allUnital_pinching I f (hforward h),
      PinchingProof.pinching_convex I f hI hf⟩

end Inline_JENS1_Assembly
