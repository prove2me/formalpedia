-- Prove2me | solution 1 for UniformADProbes.Trace.uniform_spanning_probes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:17:28.45375+00:00
-- url     : https://prove2.me/submissions/89d6574b-1def-4b6a-88aa-91e85dfeaf4f

import Mathlib
import Definitions.Def_UniformADProbes_Trace_algebra
import Theorems.Thm_UniformADProbes_Trace_small_residue_rigidity
import Definitions.Def_UniformADProbes_Trace_circuits

section
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.Dist
open UniformADProbes.Trace

section eval
variable {R : Type} [Ring R]

def fmon (H K : R) : Bool → R := fun b => if b then K else H

lemma wordEval_eq (H K : R) (w : Word) : wordEval H K w = FreeMonoid.lift (fmon H K) w := by
  simp [wordEval, FreeMonoid.lift_apply, List.prod_eq_foldr, fmon, List.foldr_map]

noncomputable def ev (H K : R) : NCPoly →ₐ[ℤ] R :=
  MonoidAlgebra.lift ℤ R Word (FreeMonoid.lift (fmon H K))

lemma polyEval_eq_ev (H K : R) (p : NCPoly) : polyEval H K p = ev H K p := by
  rw [ev, MonoidAlgebra.lift_apply]
  simp [polyEval, wordEval_eq]

lemma polyEval_x (H K : R) : polyEval H K x = H := by
  simp [polyEval, x, wordEval]

lemma polyEval_y (H K : R) : polyEval H K y = K := by
  simp [polyEval, y, wordEval]

end eval

section tree
open scoped Classical
variable {n : ℕ} {T : SimpleGraph (Fin n)}

end tree

section part3
end part3

end UniformADProbes.Trace.Dev.Dist

namespace UniformADProbes.Trace

end UniformADProbes.Trace
end

section
/-! The formal adjoint on `NCPoly` is additive, ℤ-linear and anti-multiplicative. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningAdj
open UniformADProbes.Trace
noncomputable section

def revWord (w : Word) : Word := FreeMonoid.ofList w.toList.reverse

def revHom : Word →* NCPolyᵐᵒᵖ where
  toFun w := MulOpposite.op (MonoidAlgebra.single (revWord w) (1 : ℤ))
  map_one' := by
    simp [revWord]
    rfl
  map_mul' a b := by
    simp only [revWord]
    rw [← MulOpposite.op_mul, MonoidAlgebra.single_mul_single]
    congr 2
    simp [FreeMonoid.toList_mul]

def L : NCPoly →ₐ[ℤ] NCPolyᵐᵒᵖ := MonoidAlgebra.lift ℤ NCPolyᵐᵒᵖ Word revHom

lemma adjoint_eq (p : NCPoly) : adjoint p = (L p).unop := by
  unfold adjoint L
  rw [MonoidAlgebra.lift_apply]
  rw [MulOpposite.unop_finsuppSum]
  refine Finsupp.sum_congr fun w _ => ?_
  simp only [revHom, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_smul, MulOpposite.unop_op,
    revWord]
  rw [MonoidAlgebra.smul_single']
  simp

lemma adjoint_add (p q : NCPoly) : adjoint (p + q) = adjoint p + adjoint q := by
  rw [adjoint_eq, adjoint_eq, adjoint_eq, map_add]; rfl

lemma adjoint_zero : adjoint 0 = 0 := by
  rw [adjoint_eq, map_zero]; rfl

lemma adjoint_zsmul (c : ℤ) (p : NCPoly) : adjoint (c • p) = c • adjoint p := by
  rw [adjoint_eq, adjoint_eq, map_zsmul]; rfl

lemma adjoint_mul (p q : NCPoly) : adjoint (p * q) = adjoint q * adjoint p := by
  rw [adjoint_eq, adjoint_eq, adjoint_eq, map_mul]; rfl

lemma adjoint_one : adjoint 1 = 1 := by
  rw [adjoint_eq, map_one]; rfl

lemma adjoint_x : adjoint x = x := by
  unfold adjoint x
  rw [Finsupp.sum_single_index]
  · rfl
  · simp

lemma adjoint_y : adjoint y = y := by
  unfold adjoint y
  rw [Finsupp.sum_single_index]
  · rfl
  · simp

end
end UniformADProbes.Trace.Dev.SpanningAdj
end

section
/-! Adapted from github.com/Lzp88/AD (Z. Lu), ADComplete.RationalDerivative:
the real derivation on `RatFunc ℝ`, and its agreement with `rationalDerivative`. -/
set_option autoImplicit false
namespace Dev.SpanningDer

open Polynomial
open scoped nonZeroDivisors
noncomputable section

abbrev F := RatFunc ℝ
abbrev Jet := TrivSqZeroExt F F

/-- Polynomial value and first derivative as a square-zero algebra map. -/
def polynomialJet : ℝ[X] →ₐ[ℝ] Jet where
  toFun p := (algebraMap ℝ[X] F p, algebraMap ℝ[X] F p.derivative)
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' p q := by
    apply TrivSqZeroExt.ext
    · change algebraMap ℝ[X] F (p+q) = algebraMap ℝ[X] F p + algebraMap ℝ[X] F q
      exact map_add _ p q
    · change algebraMap ℝ[X] F (p+q).derivative =
        algebraMap ℝ[X] F p.derivative + algebraMap ℝ[X] F q.derivative
      simp [Polynomial.derivative_add]
  map_mul' p q := by
    apply TrivSqZeroExt.ext
    · change algebraMap ℝ[X] F (p*q) = algebraMap ℝ[X] F p * algebraMap ℝ[X] F q
      exact map_mul _ p q
    · change algebraMap ℝ[X] F (p*q).derivative =
        algebraMap ℝ[X] F p * algebraMap ℝ[X] F q.derivative +
        algebraMap ℝ[X] F p.derivative * algebraMap ℝ[X] F q
      simp [Polynomial.derivative_mul, mul_comm, add_comm]
  commutes' r := by
    ext
    · change algebraMap ℝ[X] F (algebraMap ℝ ℝ[X] r) = algebraMap ℝ F r
      exact (IsScalarTower.algebraMap_apply ℝ ℝ[X] F r).symm
    · change algebraMap ℝ[X] F (C r).derivative = 0
      simp

theorem polynomialJet_units (p : ℝ[X]⁰) : IsUnit (polynomialJet p) := by
  apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
  apply isUnit_iff_ne_zero.mpr
  exact RatFunc.algebraMap_ne_zero (nonZeroDivisors.ne_zero p.property)

/-- The polynomial jet extends to the field by the universal localization map. -/
def rationalJet : F →ₐ[ℝ] Jet :=
  IsLocalization.liftAlgHom (M := ℝ[X]⁰) (S := F) polynomialJet_units

theorem rationalJet_polynomial (p : ℝ[X]) :
    rationalJet (algebraMap ℝ[X] F p) = polynomialJet p := by
  exact IsLocalization.lift_eq polynomialJet_units p

theorem rationalJet_fst (x : F) : (rationalJet x).fst = x := by
  let f : F →+* F := (TrivSqZeroExt.fstHom ℝ F F).toRingHom.comp rationalJet.toRingHom
  have hf : f = RingHom.id F := by
    apply IsLocalization.ringHom_ext (R := ℝ[X]) (S := F) (M := ℝ[X]⁰)
    apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply, RingHom.id_apply]
    change (rationalJet (algebraMap ℝ[X] F p)).fst = algebraMap ℝ[X] F p
    rw [rationalJet_polynomial]
    rfl
  exact DFunLike.congr_fun hf x

/-- The second component of the jet is a genuine real derivation. -/
def derivative : Derivation ℝ F F where
  toLinearMap := (TrivSqZeroExt.sndHom F F).restrictScalars ℝ |>.comp rationalJet.toLinearMap
  map_one_eq_zero' := by change (rationalJet 1).snd = 0; simp
  leibniz' x y := by
    change (rationalJet (x*y)).snd = x • (rationalJet y).snd + y • (rationalJet x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, rationalJet_fst, rationalJet_fst]
    simp [smul_eq_mul, mul_comm]

theorem derivative_polynomial (p : ℝ[X]) :
    derivative (algebraMap ℝ[X] F p) = algebraMap ℝ[X] F p.derivative := by
  change (rationalJet (algebraMap ℝ[X] F p)).snd = _
  rw [rationalJet_polynomial]
  rfl



theorem rd_eq (f : RatFunc ℝ) : UniformADProbes.Trace.rationalDerivative f = derivative f := by
  have hd : algebraMap ℝ[X] F f.denom ≠ 0 := by simpa using f.denom_ne_zero
  conv_rhs => rw [← RatFunc.num_div_denom f]
  unfold UniformADProbes.Trace.rationalDerivative
  rw [div_eq_mul_inv (algebraMap ℝ[X] F f.num), Derivation.leibniz, Derivation.leibniz_inv,
    derivative_polynomial, derivative_polynomial]
  simp only [smul_eq_mul, map_sub, map_mul, map_pow]
  field_simp
  ring

end

end Dev.SpanningDer
end

section
/-! Adapted from github.com/Lzp88/AD (Z. Lu), ADComplete.DifferentialKrylov:
finite stabilisation of a differential Krylov chain. -/
set_option autoImplicit false
namespace Dev.SpanningDK

open Matrix Module

variable {F ι : Type*} [Field F] [Algebra ℝ F] [Fintype ι]

/-- A coordinate derivation plus ordinary matrix multiplication. -/
def connection (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F) : ι → F :=
  fun i => D (v i) + A.mulVec v i

lemma connection_zero (D : Derivation ℝ F F) (A : Matrix ι ι F) :
    connection D A (0 : ι → F) = 0 := by
  ext i
  change D 0 + (A.mulVec 0) i = 0
  rw [map_zero, Matrix.mulVec_zero]
  simp

lemma connection_add (D : Derivation ℝ F F) (A : Matrix ι ι F) (u v : ι → F) :
    connection D A (u + v) = connection D A u + connection D A v := by
  ext i
  simp only [connection, Pi.add_apply, map_add, Matrix.mulVec_add]
  ring

lemma connection_smul (D : Derivation ℝ F F) (A : Matrix ι ι F) (c : F) (v : ι → F) :
    connection D A (c • v) = (D c) • v + c • connection D A v := by
  ext i
  simp only [connection, Pi.smul_apply, smul_eq_mul, Derivation.leibniz,
    Matrix.mulVec_smul, Pi.add_apply]
  ring

/-- The prefix contains indices strictly smaller than its length. -/
def krylovSpan (q : ℕ → ι → F) (n : ℕ) : Submodule F (ι → F) :=
  Submodule.span F (Set.range (fun i : Fin n => q i.val))

omit [Algebra ℝ F] [Fintype ι] in
lemma prefix_mem (q : ℕ → ι → F) {n i : ℕ} (hi : i < n) : q i ∈ krylovSpan q n :=
  Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

omit [Algebra ℝ F] [Fintype ι] in
lemma prefix_mono (q : ℕ → ι → F) {m n : ℕ} (hmn : m ≤ n) : krylovSpan q m ≤ krylovSpan q n := by
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hmn⟩, rfl⟩

omit [Algebra ℝ F] [Fintype ι] in
lemma independent_before_first_dependence (q : ℕ → ι → F) (n : ℕ)
    (h : ∀ k < n, q k ∉ krylovSpan q k) :
    LinearIndependent F (fun i : Fin n => q i.val) := by
  induction n with
  | zero => exact linearIndependent_empty_type
  | succ n ih =>
      apply linearIndependent_finSucc'.mpr
      constructor
      · exact ih (fun k hk => h k (by omega))
      · exact h n (Nat.lt_succ_self n)

omit [Algebra ℝ F] in
/-- Dimension alone locates a first dependence; it does not by itself assert
stability. Stability is proved separately with the actual Leibniz rule. -/
theorem exists_dependence (q : ℕ → ι → F) :
    ∃ n ≤ Fintype.card ι, q n ∈ krylovSpan q n := by
  classical
  by_contra h
  push Not at h
  have hind := independent_before_first_dependence q (Fintype.card ι + 1)
    (fun k hk => h k (by omega))
  have hcard := hind.fintype_card_le_finrank
  simp only [Fintype.card_fin, Module.finrank_pi] at hcard
  omega

/-- The chain consists of actual repeated connection applications. -/
def vector (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F) (n : ℕ) : ι → F :=
  (connection D A)^[n] v

lemma vector_succ (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F) (n : ℕ) :
    vector D A v (n + 1) = connection D A (vector D A v n) := by
  simp only [vector, Function.iterate_succ_apply']

theorem prefix_invariant (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F)
    (n : ℕ) (hn : vector D A v n ∈ krylovSpan (vector D A v) n)
    (x : ι → F) (hx : x ∈ krylovSpan (vector D A v) n) :
    connection D A x ∈ krylovSpan (vector D A v) n := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [← vector_succ]
      by_cases hi : i.val + 1 < n
      · exact prefix_mem _ hi
      · have hlast : i.val + 1 = n := by omega
        simpa only [hlast] using hn
  | zero => simpa only [connection_zero] using (krylovSpan (vector D A v) n).zero_mem
  | add y z _ _ hy hz =>
      simpa only [connection_add] using (krylovSpan (vector D A v) n).add_mem hy hz
  | smul c y hy hcy =>
      rw [connection_smul]
      exact (krylovSpan (vector D A v) n).add_mem
        ((krylovSpan (vector D A v) n).smul_mem (D c) hy)
        ((krylovSpan (vector D A v) n).smul_mem c hcy)

theorem later_vectors_mem (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F)
    (n : ℕ) (hn : vector D A v n ∈ krylovSpan (vector D A v) n) (k : ℕ) :
    vector D A v k ∈ krylovSpan (vector D A v) n := by
  induction k with
  | zero =>
      by_cases hn₀ : n = 0
      · simpa only [hn₀] using hn
      · exact prefix_mem _ (by omega)
  | succ k ih =>
      rw [vector_succ]
      exact prefix_invariant D A v n hn _ ih

/-- Every differential Krylov vector is spanned by the first ambient-dimension
vectors. No assumption of stability or spanning appears in the statement. -/
theorem ambient_prefix_spans (D : Derivation ℝ F F) (A : Matrix ι ι F) (v : ι → F)
    (k : ℕ) : vector D A v k ∈ krylovSpan (vector D A v) (Fintype.card ι) := by
  obtain ⟨n, hn, hdep⟩ := exists_dependence (vector D A v)
  exact prefix_mono _ hn (later_vectors_mem D A v n hdep k)


end Dev.SpanningDK
end

section
/-! The probe vectors `cv k j = (polyEval H K (probes N k j)) v` and their recurrence. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningCv
open UniformADProbes.Trace UniformADProbes.Trace.Dev.Dist

noncomputable section
variable {n : ℕ}

lemma probes_out (N k : ℕ) (j : ℤ) (h : j < 0 ∨ (k : ℤ) < j) : probes N k j = 0 := by
  cases k with
  | zero =>
    have : j ≠ 0 := by omega
    simp [probes, this]
  | succ k =>
    have : j < 0 ∨ ((k + 1 : ℕ) : ℤ) < j := h
    simp only [probes]
    rw [if_pos (by push_cast at this ⊢; exact this)]

lemma probes_succ (N k : ℕ) (j : ℤ) (h : 0 ≤ j) (h2 : j ≤ (k : ℤ) + 1) :
    probes N (k + 1) j = (y + ((N : ℤ)^2 * (j - (k : ℤ))) • (1 : NCPoly)) * probes N k j +
        (N : ℤ)^2 • (x * probes N k (j - 1)) := by
  simp only [probes]
  rw [if_neg (by push_cast; omega)]

lemma ev_x' {R : Type} [Ring R] (H K : R) : ev H K x = H :=
  (polyEval_eq_ev H K x).symm.trans (polyEval_x H K)

lemma ev_y' {R : Type} [Ring R] (H K : R) : ev H K y = K :=
  (polyEval_eq_ev H K y).symm.trans (polyEval_y H K)

/-- probe vectors -/
def cv (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k j : ℕ) : Fin n → ℝ :=
  (polyEval H K (probes N k (j : ℤ))).mulVec v

lemma cv_outside (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k j : ℕ)
    (h : k < j) : cv N H K v k j = 0 := by
  unfold cv
  rw [probes_out N k j (Or.inr (by exact_mod_cast h))]
  simp [polyEval]

lemma cv_zero (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (j : ℕ) :
    cv N H K v 0 j = if j = 0 then v else 0 := by
  unfold cv
  simp only [probes]
  by_cases hj : j = 0
  · subst hj
    simp [polyEval_eq_ev]
  · simp [hj, polyEval]

lemma cv_succ (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k j : ℕ) :
    cv N H K v (k + 1) j = K.mulVec (cv N H K v k j) +
      (((N : ℝ)^2) * ((j : ℝ) - (k : ℝ))) • cv N H K v k j +
      ((N : ℝ)^2) • H.mulVec (if j = 0 then 0 else cv N H K v k (j - 1)) := by
  by_cases hj : j ≤ k + 1
  · unfold cv
    rw [probes_succ N k (j : ℤ) (by positivity) (by exact_mod_cast hj)]
    simp only [polyEval_eq_ev, map_add, map_mul, map_zsmul, map_one, ev_x', ev_y']
    have key : ∀ (c m : ℝ) (A B : Matrix (Fin n) (Fin n) ℝ),
        ((K + c • (1 : Matrix (Fin n) (Fin n) ℝ)) * A + m • (H * B)).mulVec v =
          K.mulVec (A.mulVec v) + c • A.mulVec v + m • H.mulVec (B.mulVec v) := by
      intro c m A B
      simp [Matrix.add_mulVec, Matrix.add_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec,
        Matrix.smul_mul]
    simp only [← Int.cast_smul_eq_zsmul ℝ]
    push_cast
    rcases j with _ | j
    · have h0 : probes N k (((0 : ℕ) : ℤ) - 1) = 0 :=
        probes_out N k _ (Or.inl (by simp))
      rw [h0, map_zero]
      have := key (((N : ℝ)^2 * (((0 : ℕ) : ℝ) - k))) ((N : ℝ)^2)
        (ev H K (probes N k ((0 : ℕ) : ℤ))) 0
      simpa using this
    · have h0 : (((j + 1 : ℕ) : ℤ) - 1) = (j : ℤ) := by push_cast; ring
      rw [h0]
      simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero j)]
      exact key _ _ _ _
  · have h1 : cv N H K v (k + 1) j = 0 := cv_outside N H K v (k+1) j (by omega)
    have h2 : cv N H K v k j = 0 := cv_outside N H K v k j (by omega)
    have h3 : (if j = 0 then 0 else cv N H K v k (j - 1)) = 0 := by
      split_ifs
      · rfl
      · exact cv_outside N H K v k (j-1) (by omega)
    rw [h1, h2, h3]; simp

end
end UniformADProbes.Trace.Dev.SpanningCv
end

section
/-! Polynomial generating vectors of the probe recurrence, and the scaled connection identity.
Adapted from github.com/Lzp88/AD (Z. Lu), ADComplete (ProbePolynomial, ProbeKrylov). -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningPoly
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCv Polynomial
noncomputable section

variable {n : ℕ}

abbrev F := RatFunc ℝ

def polyAct (M : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ[X]) (i : Fin n) : ℝ[X] :=
  ∑ j, C (M i j) * p j

def G (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k : ℕ) : Fin n → ℝ[X] :=
  fun i => ∑ j ∈ Finset.range (k + 1), monomial j (cv N H K v k j i)

lemma G_coeff (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k j : ℕ) (i : Fin n) :
    (G N H K v k i).coeff j = cv N H K v k j i := by
  by_cases hj : j < k + 1
  · simp [G, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hj]
  · have hout := cv_outside N H K v k j (by omega)
    simp [G, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, hj, hout]

lemma G_zero (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (i : Fin n) :
    G N H K v 0 i = C (v i) := by
  ext j
  rw [G_coeff, cv_zero, Polynomial.coeff_C]
  by_cases hj : j = 0 <;> simp [hj]

lemma coeff_X_derivative (p : ℝ[X]) (j : ℕ) :
    (X * p.derivative).coeff j = (j : ℝ) * p.coeff j := by
  cases j with
  | zero => simp
  | succ j => rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]; push_cast; ring

theorem G_step (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k : ℕ) (i : Fin n) :
    G N H K v (k + 1) i =
      polyAct K (G N H K v k) i +
      C ((N : ℝ)^2) * (X * (G N H K v k i).derivative - C (k : ℝ) * G N H K v k i) +
      C ((N : ℝ)^2) * X * polyAct H (G N H K v k) i := by
  ext j
  rw [G_coeff]
  have haction (M : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
      (polyAct M (G N H K v k) i).coeff t = M.mulVec (cv N H K v k t) i := by
    simp [polyAct, Polynomial.finsetSum_coeff, G_coeff, Matrix.mulVec, dotProduct]
  rw [show C ((N : ℝ)^2) * X * polyAct H (G N H K v k) i =
      C ((N : ℝ)^2) * (X * polyAct H (G N H K v k) i) by ring]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub,
    coeff_X_derivative, haction, G_coeff]
  rw [cv_succ]
  by_cases hj : j = 0
  · subst j
    simp
    ring
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [Polynomial.coeff_X_mul, haction, Nat.succ_ne_zero,
      ↓reduceIte, Nat.succ_sub_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

def Amat (B H : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) F := fun i j =>
  algebraMap ℝ F (B i j) / RatFunc.X + algebraMap ℝ F (H i j)

lemma conn_eq (B H : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → F) :
    connection B H f =
      Dev.SpanningDK.connection Dev.SpanningDer.derivative (Amat B H) f := by
  ext i
  simp only [connection, Dev.SpanningDK.connection, Matrix.mulVec, dotProduct, Amat,
    Dev.SpanningDer.rd_eq]

lemma alg_C (a : ℝ) : algebraMap ℝ[X] F (C a) = algebraMap ℝ F a :=
  (IsScalarTower.algebraMap_apply ℝ ℝ[X] F a).symm

lemma alg_X : algebraMap ℝ[X] F X = RatFunc.X := RatFunc.algebraMap_X

theorem G_conn (N : ℕ) (hN : 1 ≤ N) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k : ℕ)
    (i : Fin n) :
    algebraMap ℝ[X] F (G N H K v (k + 1) i) =
      (algebraMap ℝ F ((N : ℝ)^2) * RatFunc.X) *
        connection (((N : ℝ)^2)⁻¹ • K) H (fun j => algebraMap ℝ[X] F (G N H K v k j)) i -
      algebraMap ℝ F ((N : ℝ)^2) * (k : F) * algebraMap ℝ[X] F (G N H K v k i) := by
  have hκ : ((N : ℝ)^2) ≠ 0 := by positivity
  have hκF : algebraMap ℝ F ((N : ℝ)^2) ≠ 0 := (_root_.map_ne_zero _).mpr hκ
  have hx : (RatFunc.X : F) ≠ 0 := RatFunc.X_ne_zero
  rw [G_step]
  simp only [map_add, map_sub, map_mul, alg_C, map_natCast, alg_X]
  unfold connection
  rw [Dev.SpanningDer.rd_eq, Dev.SpanningDer.derivative_polynomial]
  simp only [polyAct, map_sum, map_mul, alg_C, Matrix.smul_apply, smul_eq_mul, map_inv₀]
  have e : (algebraMap ℝ F ((N : ℝ)^2) * RatFunc.X) *
      ∑ x, (((algebraMap ℝ F ((N : ℝ)^2))⁻¹ * algebraMap ℝ F (K i x)) / RatFunc.X +
          algebraMap ℝ F (H i x)) * algebraMap ℝ[X] F (G N H K v k x) =
      ∑ x, algebraMap ℝ F (K i x) * algebraMap ℝ[X] F (G N H K v k x) +
      (algebraMap ℝ F ((N : ℝ)^2) * RatFunc.X) *
        ∑ x, algebraMap ℝ F (H i x) * algebraMap ℝ[X] F (G N H K v k x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    field_simp
  rw [mul_add, e]
  ring

def qv (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k : ℕ) : Fin n → F :=
  Dev.SpanningDK.vector Dev.SpanningDer.derivative (Amat (((N : ℝ)^2)⁻¹ • K) H)
    (fun i => algebraMap ℝ F (v i)) k

lemma qv_succ (N : ℕ) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k : ℕ) :
    qv N H K v (k + 1) = connection (((N : ℝ)^2)⁻¹ • K) H (qv N H K v k) := by
  rw [conn_eq]
  exact Dev.SpanningDK.vector_succ _ _ _ _

theorem G_qv (N : ℕ) (hN : 1 ≤ N) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (k : ℕ) :
    (fun i => algebraMap ℝ[X] F (G N H K v k i)) =
      (algebraMap ℝ F ((N : ℝ)^2) * RatFunc.X) ^ k • qv N H K v k := by
  have hκ : ((N : ℝ)^2) ≠ 0 := by positivity
  induction k with
  | zero =>
      ext i
      simp [G_zero, qv, Dev.SpanningDK.vector]
  | succ k ih =>
      let a : F := algebraMap ℝ F ((N : ℝ)^2) * RatFunc.X
      have hDa : Dev.SpanningDer.derivative a = algebraMap ℝ F ((N : ℝ)^2) := by
        have hk : Dev.SpanningDer.derivative (algebraMap ℝ F ((N : ℝ)^2)) = 0 :=
          Derivation.map_algebraMap Dev.SpanningDer.derivative _
        have hx : Dev.SpanningDer.derivative (RatFunc.X : F) = 1 := by
          rw [← alg_X, Dev.SpanningDer.derivative_polynomial]
          simp
        dsimp only [a]
        rw [Derivation.leibniz]
        change algebraMap ℝ F ((N : ℝ)^2) * Dev.SpanningDer.derivative (RatFunc.X : F) +
          (RatFunc.X : F) * Dev.SpanningDer.derivative (algebraMap ℝ F ((N : ℝ)^2)) = _
        rw [hk, hx, mul_one, mul_zero, add_zero]
      have hpow : Dev.SpanningDer.derivative (a ^ k) * a =
          algebraMap ℝ F ((N : ℝ)^2) * (k : F) * a ^ k := by
        cases k with
        | zero => simp
        | succ k =>
            rw [Derivation.leibniz_pow, hDa]
            simp only [Nat.succ_sub_one, smul_eq_mul, nsmul_eq_mul, Nat.cast_succ]
            ring
      ext i
      rw [G_conn N hN H K v k i, ih, conn_eq, Dev.SpanningDK.connection_smul]
      have hi : algebraMap ℝ[X] F (G N H K v k i) = a ^ k * qv N H K v k i :=
        congrArg (fun y : Fin n → F => y i) ih
      rw [hi]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hstep : qv N H K v (k + 1) = Dev.SpanningDK.connection Dev.SpanningDer.derivative
          (Amat (((N : ℝ)^2)⁻¹ • K) H) (qv N H K v k) := by
        rw [← conn_eq]; exact qv_succ N H K v k
      rw [hstep]
      change a * (Dev.SpanningDer.derivative (a ^ k) * _ + a ^ k * _) -
        algebraMap ℝ F ((N : ℝ)^2) * (k : F) * (a ^ k * _) = a ^ (k + 1) * _
      rw [pow_succ a k]
      linear_combination (qv N H K v k i) * hpow

end
end UniformADProbes.Trace.Dev.SpanningPoly
end

section
/-! The spanning equality for the probe family (paper Thm 1.2), from small-residue rigidity.
Adapted from github.com/Lzp88/AD (Z. Lu), ADComplete (UniformProbes, SpectralUniformProbes). -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningKry
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCv UniformADProbes.Trace.Dev.SpanningPoly
open Polynomial
open scoped Pointwise
noncomputable section

variable {n : ℕ}

lemma mem_cyclic (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (p : NCPoly) :
    (polyEval H K p).mulVec v ∈ cyclicModule H K v := by
  unfold polyEval
  rw [Finsupp.sum, Matrix.sum_mulVec]
  apply Submodule.sum_mem
  intro w _
  rw [← Int.cast_smul_eq_zsmul ℝ, Matrix.smul_mulVec]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)

lemma reflect (W : Submodule ℝ (Fin n → ℝ)) (z : Fin n → ℝ)
    (h : (fun i => algebraMap ℝ F (z i)) ∈ scalarExtension W) : z ∈ W := by
  by_contra hz
  obtain ⟨f, hf, hfW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  let Φ : (Fin n → F) →ₗ[F] F :=
    ∑ i, (algebraMap ℝ F (f (Pi.single i 1))) • LinearMap.proj i
  have hΦ : ∀ w : Fin n → ℝ, Φ (fun i => algebraMap ℝ F (w i)) = algebraMap ℝ F (f w) := by
    intro w
    have : f w = ∑ i, w i * f (Pi.single i 1) := by
      rw [LinearMap.pi_apply_eq_sum_univ f w]
      refine Finset.sum_congr rfl fun x _ => ?_
      have e : (fun j => if x = j then (1 : ℝ) else 0) = Pi.single x 1 := by
        ext j; simp [Pi.single_apply, eq_comm]
      rw [e]; rfl
    rw [this, map_sum]
    simp [Φ, mul_comm]
  have hker : scalarExtension W ≤ LinearMap.ker Φ := by
    apply Submodule.span_le.mpr
    rintro g ⟨w, hw, rfl⟩
    have : f w = 0 := by
      have : f w ∈ W.map f := Submodule.mem_map_of_mem hw
      rw [hfW] at this; simpa using this
    change Φ _ = 0
    rw [hΦ, this, map_zero]
  have := hker h
  rw [LinearMap.mem_ker, hΦ] at this
  exact hf ((map_eq_zero_iff _ (algebraMap ℝ F).injective).mp this)

lemma spectralDiameter_smul (c : ℝ) (hc : 0 < c) (K : Matrix (Fin n) (Fin n) ℝ) :
    spectralDiameter (c • K) = c * spectralDiameter K := by
  have h : spectrum ℝ (c • K) = c • spectrum ℝ K := by
    have := spectrum.unit_smul_eq_smul K (Units.mk0 c hc.ne')
    simpa using this
  unfold spectralDiameter
  rw [h, Real.sSup_smul_of_nonneg hc.le, Real.sInf_smul_of_nonneg hc.le]
  simp [mul_sub]

lemma cyclic_le (W : Submodule ℝ (Fin n → ℝ)) (H K : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ)
    (hv : v ∈ W) (hH : MatrixInvariant W H) (hK : MatrixInvariant W K) :
    cyclicModule H K v ≤ W := by
  apply Submodule.span_le.mpr
  rintro z ⟨w, rfl⟩
  have : ∀ l : List Bool, (l.foldr (fun (b : Bool) z => (if b then K else H) * z) 1).mulVec v ∈ W := by
    intro l
    induction l with
    | nil => simpa using hv
    | cons b l ih =>
      simp only [List.foldr_cons]
      rw [← Matrix.mulVec_mulVec]
      cases b
      · exact hH _ ih
      · exact hK _ ih
  exact this w.toList

theorem span_eq (N : ℕ) (hN : 1 ≤ N) (hnN : n ≤ N)
    (H K : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm) (hK : K.IsSymm)
    (hdiam : spectralDiameter K ≤ (N : ℝ) - 1) (v : Fin n → ℝ) :
    responseSpan H K v (probeList N) = cyclicModule H K v := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ : (0 : ℝ) < (N : ℝ)^2 := by positivity
  set κ : ℝ := (N : ℝ)^2 with hκdef
  set B : Matrix (Fin n) (Fin n) ℝ := κ⁻¹ • K with hBdef
  have hBs : B.IsSymm := by
    unfold Matrix.IsSymm
    rw [hBdef, Matrix.transpose_smul, hK.eq]
  let q := qv N H K v
  let V : Submodule F (Fin n → F) := Dev.SpanningDK.krylovSpan q (Fintype.card (Fin n))
  have hq : ∀ k, q k ∈ V := fun k =>
    Dev.SpanningDK.ambient_prefix_spans Dev.SpanningDer.derivative (Amat B H) _ k
  have hV : ∀ f ∈ V, connection B H f ∈ V := by
    intro f hf
    rw [conn_eq]
    exact Dev.SpanningDK.prefix_invariant Dev.SpanningDer.derivative (Amat B H) _
      (Fintype.card (Fin n)) (hq _) f hf
  have hrank : (Module.finrank F V : ℝ) ≤ n := by
    have := Submodule.finrank_le V
    rw [Module.finrank_fin_fun] at this
    exact_mod_cast this
  have hsmall : (Module.finrank F V : ℝ) * spectralDiameter B < 1 := by
    rw [hBdef, spectralDiameter_smul _ (inv_pos.mpr hκ)]
    set d := spectralDiameter K
    have hr0 : (0 : ℝ) ≤ Module.finrank F V := Nat.cast_nonneg _
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    by_cases hd : d ≤ 0
    · have : κ⁻¹ * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr hκ.le) hd
      nlinarith
    · push Not at hd
      have h1 : κ⁻¹ * d ≤ κ⁻¹ * ((N : ℝ) - 1) := mul_le_mul_of_nonneg_left hdiam (inv_nonneg.mpr hκ.le)
      have h2 : (Module.finrank F V : ℝ) * (κ⁻¹ * d) ≤ N * (κ⁻¹ * ((N : ℝ) - 1)) :=
        mul_le_mul (hrank.trans hnN') h1 (by positivity) hNpos.le
      have h3 : (N : ℝ) * (κ⁻¹ * ((N : ℝ) - 1)) < 1 := by
        rw [hκdef]
        field_simp
        nlinarith
      linarith
  obtain ⟨W, hVW, hWB, hWH⟩ := small_residue_rigidity n B H hBs hH V hV hsmall
  have hWK : MatrixInvariant W K := by
    intro w hw
    have := W.smul_mem κ (hWB w hw)
    have e : K.mulVec w = κ • B.mulVec w := by
      rw [hBdef, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hκ.ne', one_smul]
    rw [e]; exact this
  have hconstW : ∀ w ∈ W, (fun i => algebraMap ℝ F (w i)) ∈ V := by
    intro w hw
    rw [hVW]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  have hvW : v ∈ W := by
    apply reflect
    rw [← hVW]
    exact hq 0
  have hcyc : cyclicModule H K v ≤ W := cyclic_le W H K v hvW hWH hWK
  let U : Submodule ℝ (Fin n → ℝ) :=
    Submodule.span ℝ {z | ∃ k < N, ∃ j ≤ k, z = cv N H K v k j}
  have hGU : ∀ k < N, (fun i => algebraMap ℝ[X] F (G N H K v k i)) ∈ scalarExtension U := by
    intro k hk
    have e : (fun i => algebraMap ℝ[X] F (G N H K v k i)) =
        ∑ j ∈ Finset.range (k + 1), (RatFunc.X : F) ^ j •
          (fun i => algebraMap ℝ F (cv N H K v k j i)) := by
      ext i
      simp only [G, map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, alg_C, map_pow, alg_X, mul_comm]
    rw [e]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨cv N H K v k j, Submodule.subset_span
      ⟨k, hk, j, by have := Finset.mem_range.mp hj; omega, rfl⟩, rfl⟩
  have hVU : V ≤ scalarExtension U := by
    apply Submodule.span_le.mpr
    rintro z ⟨k, rfl⟩
    have hk : k.val < N := lt_of_lt_of_le (by simpa using k.isLt) hnN
    have ha : algebraMap ℝ F ((N : ℝ)^2) * (RatFunc.X : F) ≠ 0 :=
      mul_ne_zero ((_root_.map_ne_zero _).mpr hκ.ne') RatFunc.X_ne_zero
    have hm := (scalarExtension U).smul_mem
      (((algebraMap ℝ F ((N : ℝ)^2) * (RatFunc.X : F)) ^ k.val)⁻¹) (hGU k.val hk)
    rw [G_qv N hN] at hm
    change qv N H K v k.val ∈ scalarExtension U
    simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ ha), one_smul] using hm
  have hWU : W ≤ U := by
    intro z hz
    apply reflect
    exact hVU (hconstW z hz)
  have hUR : U ≤ responseSpan H K v (probeList N) := by
    apply Submodule.span_le.mpr
    rintro z ⟨k, hk, j, hj, rfl⟩
    apply Submodule.subset_span
    refine ⟨probes N k (j : ℤ), ?_, rfl⟩
    simp only [probeList, probeIndices, List.mem_map, List.mem_flatMap, List.mem_range]
    exact ⟨(k, j), ⟨k, hk, j, by omega, rfl⟩, rfl⟩
  have hRC : responseSpan H K v (probeList N) ≤ cyclicModule H K v := by
    apply Submodule.span_le.mpr
    rintro z ⟨p, _, rfl⟩
    exact mem_cyclic H K v p
  exact le_antisymm hRC (hcyc.trans (hWU.trans hUR))

end
end UniformADProbes.Trace.Dev.SpanningKry
end

section
/-! Register and degree arrays of a code array under `push`. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningCode
open UniformADProbes.Trace
noncomputable section

section
variable {R : Type} [Ring R]

def regs (H K : R) (c : Array Instruction) : Array R := registers ⟨c, 0⟩ H K

lemma regs_push (H K : R) (c : Array Instruction) (I : Instruction) :
    regs H K (c.push I) = (regs H K c).push (runInstruction H K (regs H K c) I) := by
  unfold regs registers
  simp [Array.foldl_push]

lemma regs_size (H K : R) (c : Array Instruction) : (regs H K c).size = c.size := by
  have : ∀ (l : List Instruction), ((l.foldl (fun regs instr => regs.push (runInstruction H K regs instr)) #[]) : Array R).size = l.length := by
    intro l
    suffices ∀ (acc : Array R), (l.foldl (fun regs instr => regs.push (runInstruction H K regs instr)) acc).size = acc.size + l.length by
      simpa using this #[]
    induction l with
    | nil => simp
    | cons a l ih => intro acc; simp [List.foldl_cons, ih]; omega
  unfold regs registers
  rw [← Array.foldl_toList]
  simpa using this c.toList

end

def degs (c : Array Instruction) : Array ℕ := degrees ⟨c, 0⟩

lemma degs_push (c : Array Instruction) (I : Instruction) :
    degs (c.push I) = (degs c).push (degreeInstruction (degs c) I) := by
  unfold degs degrees
  simp [Array.foldl_push]

lemma degs_empty : degs #[] = #[] := by simp [degs, degrees]

lemma degs_size (c : Array Instruction) : (degs c).size = c.size := by
  have : ∀ (l : List Instruction), ((l.foldl (fun d instr => d.push (degreeInstruction d instr)) #[]) : Array ℕ).size = l.length := by
    intro l
    suffices ∀ (acc : Array ℕ), (l.foldl (fun d instr => d.push (degreeInstruction d instr)) acc).size = acc.size + l.length by
      simpa using this #[]
    induction l with
    | nil => simp
    | cons a l ih => intro acc; simp [List.foldl_cons, ih]; omega
  unfold degs degrees
  rw [← Array.foldl_toList]
  simpa using this c.toList


/-- value of register `r` at (x,y) -/
abbrev rv (c : Array Instruction) (r : ℕ) : NCPoly := (regs x y c)[r]?.getD 0

abbrev dg (c : Array Instruction) (r : ℕ) : ℕ := (degs c)[r]?.getD 0

lemma rv_push (c : Array Instruction) (I : Instruction) (r : ℕ) :
    rv (c.push I) r = if r < c.size then rv c r else if r = c.size then
      runInstruction x y (regs x y c) I else 0 := by
  unfold rv
  rw [regs_push, Array.getElem?_push, regs_size]
  by_cases h1 : r < c.size
  · have : r ≠ c.size := by omega
    simp [h1, this]
  · by_cases h2 : r = c.size
    · simp [h2]
    · have : (regs x y c)[r]? = none := by
        rw [Array.getElem?_eq_none]; rw [regs_size]; omega
      simp [h1, h2, this]

lemma dg_push (c : Array Instruction) (I : Instruction) (r : ℕ) :
    dg (c.push I) r = if r < c.size then dg c r else if r = c.size then
      degreeInstruction (degs c) I else 0 := by
  unfold dg
  rw [degs_push, Array.getElem?_push, degs_size]
  by_cases h1 : r < c.size
  · have : r ≠ c.size := by omega
    simp [h1, this]
  · by_cases h2 : r = c.size
    · simp [h2]
    · have : (degs c)[r]? = none := by
        rw [Array.getElem?_eq_none]; rw [degs_size]; omega
      simp [h1, h2, this]

lemma rv_push_old (c : Array Instruction) (I : Instruction) (r : ℕ) (h : r < c.size) :
    rv (c.push I) r = rv c r := by
  rw [rv_push, if_pos h]

lemma rv_push_new (c : Array Instruction) (I : Instruction) :
    rv (c.push I) c.size = runInstruction x y (regs x y c) I := by
  rw [rv_push, if_neg (lt_irrefl _), if_pos rfl]

lemma dg_push_old (c : Array Instruction) (I : Instruction) (r : ℕ) (h : r < c.size) :
    dg (c.push I) r = dg c r := by
  rw [dg_push, if_pos h]

lemma dg_push_new (c : Array Instruction) (I : Instruction) :
    dg (c.push I) c.size = degreeInstruction (degs c) I := by
  rw [dg_push, if_neg (lt_irrefl _), if_pos rfl]

/-- the extension relation: old registers and degrees are unchanged -/
def Ext (c c' : Array Instruction) : Prop :=
  c.size ≤ c'.size ∧ ∀ r < c.size, rv c' r = rv c r ∧ dg c' r = dg c r

lemma Ext.refl (c : Array Instruction) : Ext c c := ⟨le_rfl, fun _ _ => ⟨rfl, rfl⟩⟩

lemma Ext.trans {c c' c'' : Array Instruction} (h : Ext c c') (h' : Ext c' c'') : Ext c c'' :=
  ⟨h.1.trans h'.1, fun r hr => by
    rw [(h'.2 r (lt_of_lt_of_le hr h.1)).1, (h'.2 r (lt_of_lt_of_le hr h.1)).2,
      (h.2 r hr).1, (h.2 r hr).2]
    exact ⟨rfl, rfl⟩⟩

lemma ext_push (c : Array Instruction) (I : Instruction) : Ext c (c.push I) := by
  refine ⟨by simp, fun r hr => ?_⟩
  rw [rv_push, dg_push, if_pos hr, if_pos hr]
  exact ⟨rfl, rfl⟩

end
end UniformADProbes.Trace.Dev.SpanningCode
end

section
/-! Pure versions of the dual-emission primitives and their semantic specifications. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningBody
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningAdj
noncomputable section

def pMul (c : Array Instruction) (a b : DualRef) : Array Instruction × DualRef :=
  ((c.push (.mul a.1 b.1)).push (.mul b.2 a.2), (c.size, c.size + 1))

def pAdd (c : Array Instruction) (a b : DualRef) : Array Instruction × DualRef :=
  ((c.push (.add a.1 b.1)).push (.add a.2 b.2), (c.size, c.size + 1))

def pScale (c : Array Instruction) (k : ℤ) (a : DualRef) : Array Instruction × DualRef :=
  ((c.push (.scale k a.1)).push (.scale k a.2), (c.size, c.size + 1))

def Sem (c : Array Instruction) (r : DualRef) (P : NCPoly) (e : ℕ) : Prop :=
  r.1 < c.size ∧ r.2 < c.size ∧ rv c r.1 = P ∧ rv c r.2 = adjoint P ∧ dg c r.1 ≤ e ∧
    dg c r.2 ≤ e

lemma Sem.mono {c c' : Array Instruction} {r : DualRef} {P : NCPoly} {e : ℕ}
    (h : Sem c r P e) (hx : Ext c c') : Sem c' r P e := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨lt_of_lt_of_le h1 hx.1, lt_of_lt_of_le h2 hx.1, ?_, ?_, ?_, ?_⟩
  · rw [(hx.2 _ h1).1]; exact h3
  · rw [(hx.2 _ h2).1]; exact h4
  · rw [(hx.2 _ h1).2]; exact h5
  · rw [(hx.2 _ h2).2]; exact h6

lemma Sem.le {c : Array Instruction} {r : DualRef} {P : NCPoly} {e e' : ℕ}
    (h : Sem c r P e) (he : e ≤ e') : Sem c r P e' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1.trans he, h.2.2.2.2.2.trans he⟩

lemma pMul_size (c a b) : (pMul c a b).1.size = c.size + 2 := by simp [pMul]
lemma pAdd_size (c a b) : (pAdd c a b).1.size = c.size + 2 := by simp [pAdd]
lemma pScale_size (c k a) : (pScale c k a).1.size = c.size + 2 := by simp [pScale]

lemma pMul_ext (c a b) : Ext c (pMul c a b).1 := (ext_push _ _).trans (ext_push _ _)
lemma pAdd_ext (c a b) : Ext c (pAdd c a b).1 := (ext_push _ _).trans (ext_push _ _)
lemma pScale_ext (c k a) : Ext c (pScale c k a).1 := (ext_push _ _).trans (ext_push _ _)

lemma pMul_sem {c : Array Instruction} {a b : DualRef} {A B : NCPoly} {ea eb : ℕ}
    (ha : Sem c a A ea) (hb : Sem c b B eb) :
    Sem (pMul c a b).1 (pMul c a b).2 (A * B) (ea + eb) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have hs : c.size + 1 = (c.push (Instruction.mul a.1 b.1)).size := by simp
  have e1 := (ext_push c (Instruction.mul a.1 b.1)).2
  unfold pMul Sem
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [rv_push_old _ _ _ (by simp), rv_push_new]
    show rv c a.1 * rv c b.1 = _
    rw [a3, b3]
  · simp only
    rw [hs, rv_push_new]
    show rv _ b.2 * rv _ a.2 = _
    rw [(e1 _ b2).1, (e1 _ a2).1, a4, b4,
      adjoint_mul]
  · simp only
    rw [dg_push_old _ _ _ (by simp), dg_push_new]
    show dg c a.1 + dg c b.1 ≤ _
    omega
  · simp only
    rw [hs, dg_push_new]
    show dg _ b.2 + dg _ a.2 ≤ _
    rw [(e1 _ b2).2, (e1 _ a2).2]
    omega

lemma pAdd_sem {c : Array Instruction} {a b : DualRef} {A B : NCPoly} {ea eb : ℕ}
    (ha : Sem c a A ea) (hb : Sem c b B eb) :
    Sem (pAdd c a b).1 (pAdd c a b).2 (A + B) (max ea eb) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have hs : c.size + 1 = (c.push (Instruction.add a.1 b.1)).size := by simp
  have e1 := (ext_push c (Instruction.add a.1 b.1)).2
  unfold pAdd Sem
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [rv_push_old _ _ _ (by simp), rv_push_new]
    show rv c a.1 + rv c b.1 = _
    rw [a3, b3]
  · simp only
    rw [hs, rv_push_new]
    show rv _ a.2 + rv _ b.2 = _
    rw [(e1 _ b2).1, (e1 _ a2).1, a4, b4,
      adjoint_add]
  · simp only
    rw [dg_push_old _ _ _ (by simp), dg_push_new]
    show max (dg c a.1) (dg c b.1) ≤ _
    omega
  · simp only
    rw [hs, dg_push_new]
    show max (dg _ a.2) (dg _ b.2) ≤ _
    rw [(e1 _ b2).2, (e1 _ a2).2]
    omega

lemma pScale_sem {c : Array Instruction} {a : DualRef} {A : NCPoly} {ea : ℕ} (k : ℤ)
    (ha : Sem c a A ea) :
    Sem (pScale c k a).1 (pScale c k a).2 (k • A) ea := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  have hs : c.size + 1 = (c.push (Instruction.scale k a.1)).size := by simp
  have e1 := (ext_push c (Instruction.scale k a.1)).2
  unfold pScale Sem
  refine ⟨by simp, by simp, ?_, ?_, ?_, ?_⟩
  · simp only
    rw [rv_push_old _ _ _ (by simp), rv_push_new]
    show k • rv c a.1 = _
    rw [a3]
  · simp only
    rw [hs, rv_push_new]
    show k • rv _ a.2 = _
    rw [(e1 _ a2).1, a4, adjoint_zsmul]
  · simp only
    rw [dg_push_old _ _ _ (by simp), dg_push_new]
    show dg c a.1 ≤ _
    omega
  · simp only
    rw [hs, dg_push_new]
    show dg _ a.2 ≤ _
    rw [(e1 _ a2).2]
    omega

def BW (cd : Array Instruction) : Prop := ∀ r (h : r < cd.size), backward r cd[r]
def Lit (L : ℕ) (c : Array Instruction) : Prop :=
  ∀ I ∈ c.toList, ∀ k a, I = .scale k a → signedBits k ≤ L
def DGB (B : ℕ) (c : Array Instruction) : Prop := ∀ r, dg c r ≤ B

lemma BW.push {c : Array Instruction} (h : BW c) (I : Instruction) (hI : backward c.size I) :
    BW (c.push I) := by
  intro r hr
  rw [Array.getElem_push]
  by_cases h' : r < c.size
  · rw [dif_pos h']; exact h r h'
  · rw [dif_neg h']
    have : r = c.size := by simp at hr; omega
    subst this; exact hI

lemma BW.empty : BW #[] := fun r hr => by simp at hr

lemma Lit.push {L : ℕ} {c : Array Instruction} (h : Lit L c) (I : Instruction)
    (hI : ∀ k a, I = .scale k a → signedBits k ≤ L) : Lit L (c.push I) := by
  intro J hJ k a hk
  rw [Array.toList_push, List.mem_append] at hJ
  rcases hJ with hJ | hJ
  · exact h J hJ k a hk
  · simp at hJ; subst hJ; exact hI k a hk

lemma DGB.push {B : ℕ} {c : Array Instruction} (h : DGB B c) (I : Instruction)
    (hI : degreeInstruction (degs c) I ≤ B) : DGB B (c.push I) := by
  intro r
  rw [dg_push]
  split_ifs
  · exact h r
  · exact hI
  · exact Nat.zero_le _

lemma pMul_good {B L : ℕ} {c : Array Instruction} {a b : DualRef} {A A' : NCPoly} {ea eb : ℕ}
    (hbw : BW c) (hl : Lit L c) (hd : DGB B c) (ha : Sem c a A ea) (hb : Sem c b A' eb)
    (hB : ea + eb ≤ B) : BW (pMul c a b).1 ∧ Lit L (pMul c a b).1 ∧ DGB B (pMul c a b).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have e1 := (ext_push c (Instruction.mul a.1 b.1)).2
  unfold pMul
  refine ⟨?_, ?_, ?_⟩
  · refine (hbw.push (Instruction.mul a.1 b.1) ⟨a1, b1⟩).push (Instruction.mul b.2 a.2) ?_
    show b.2 < (c.push (Instruction.mul a.1 b.1)).size ∧ a.2 < (c.push (Instruction.mul a.1 b.1)).size
    simp only [Array.size_push]
    omega
  · exact (hl.push _ (by intro k a h; cases h)).push _ (by intro k a h; cases h)
  · refine (hd.push (Instruction.mul a.1 b.1) ?_).push (Instruction.mul b.2 a.2) ?_
    · show dg c a.1 + dg c b.1 ≤ B
      omega
    · show dg (c.push (Instruction.mul a.1 b.1)) b.2 + dg (c.push (Instruction.mul a.1 b.1)) a.2 ≤ B
      rw [(e1 _ b2).2, (e1 _ a2).2]
      omega

lemma pAdd_good {B L : ℕ} {c : Array Instruction} {a b : DualRef} {A A' : NCPoly} {ea eb : ℕ}
    (hbw : BW c) (hl : Lit L c) (hd : DGB B c) (ha : Sem c a A ea) (hb : Sem c b A' eb)
    (hB : max ea eb ≤ B) : BW (pAdd c a b).1 ∧ Lit L (pAdd c a b).1 ∧ DGB B (pAdd c a b).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hb
  have e1 := (ext_push c (Instruction.add a.1 b.1)).2
  unfold pAdd
  refine ⟨?_, ?_, ?_⟩
  · refine (hbw.push (Instruction.add a.1 b.1) ⟨a1, b1⟩).push (Instruction.add a.2 b.2) ?_
    show a.2 < (c.push (Instruction.add a.1 b.1)).size ∧ b.2 < (c.push (Instruction.add a.1 b.1)).size
    simp only [Array.size_push]
    omega
  · exact (hl.push _ (by intro k a h; cases h)).push _ (by intro k a h; cases h)
  · refine (hd.push (Instruction.add a.1 b.1) ?_).push (Instruction.add a.2 b.2) ?_
    · show max (dg c a.1) (dg c b.1) ≤ B
      omega
    · show max (dg (c.push (Instruction.add a.1 b.1)) a.2) (dg (c.push (Instruction.add a.1 b.1)) b.2) ≤ B
      rw [(e1 _ b2).2, (e1 _ a2).2]
      omega

lemma pScale_good {B L : ℕ} {c : Array Instruction} {a : DualRef} {A : NCPoly} {ea : ℕ} (k : ℤ)
    (hbw : BW c) (hl : Lit L c) (hd : DGB B c) (ha : Sem c a A ea)
    (hB : ea ≤ B) (hk : signedBits k ≤ L) :
    BW (pScale c k a).1 ∧ Lit L (pScale c k a).1 ∧ DGB B (pScale c k a).1 := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha
  have e1 := (ext_push c (Instruction.scale k a.1)).2
  unfold pScale
  refine ⟨?_, ?_, ?_⟩
  · refine (hbw.push (Instruction.scale k a.1) a1).push (Instruction.scale k a.2) ?_
    show a.2 < (c.push (Instruction.scale k a.1)).size
    simp only [Array.size_push]
    omega
  · refine (hl.push _ ?_).push _ ?_ <;> (intro k' a' h; cases h; exact hk)
  · refine (hd.push (Instruction.scale k a.1) ?_).push (Instruction.scale k a.2) ?_
    · show dg c a.1 ≤ B
      omega
    · show dg (c.push (Instruction.scale k a.1)) a.2 ≤ B
      rw [(e1 _ a2).2]
      omega

end
end UniformADProbes.Trace.Dev.SpanningBody
end

section
/-! Deterministic Hoare-style specifications of the emitter monad on the code array. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningRun
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
noncomputable section

/-- Running `m` on any state whose code is `c` returns `r` and leaves code `c'`. -/
def Trip {α : Type} (m : Emit α) (c : Array Instruction) (r : α) (c' : Array Instruction) : Prop :=
  ∀ st : Builder, st.code = c → (m.run st).1 = r ∧ (m.run st).2.code = c'

lemma Trip.bind {α β : Type} {m : Emit α} {f : α → Emit β} {c c1 c2 : Array Instruction}
    {r : α} {r2 : β} (hm : Trip m c r c1) (hf : Trip (f r) c1 r2 c2) :
    Trip (m >>= f) c r2 c2 := by
  intro st hst
  obtain ⟨h1, h2⟩ := hm st hst
  have := hf (m.run st).2 h2
  change ((f (m.run st).1).run (m.run st).2).1 = r2 ∧
    ((f (m.run st).1).run (m.run st).2).2.code = c2
  rw [h1]
  exact this

lemma Trip.pure' {α : Type} (x : α) (c : Array Instruction) : Trip (pure x : Emit α) c x c := by
  intro st hst
  exact ⟨rfl, hst⟩

lemma trip_emit (c : Array Instruction) (I : Instruction) :
    Trip (emit I) c c.size (c.push I) := by
  intro st hst
  subst hst
  exact ⟨rfl, rfl⟩

lemma trip_charge (c : Array Instruction) (k : ℕ) : Trip (charge k) c () c := by
  intro st hst
  exact ⟨rfl, hst⟩

lemma trip_tableGet (c : Array Instruction) (a : Array DualRef) (i : ℕ) (fb : DualRef) :
    Trip (tableGet a i fb) c (a[i]?.getD fb) c := by
  intro st hst
  exact ⟨rfl, hst⟩

lemma trip_dualMul (c : Array Instruction) (a b : DualRef) :
    Trip (dualMul a b) c (pMul c a b).2 (pMul c a b).1 := by
  unfold dualMul
  refine Trip.bind (trip_emit c _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  have := Trip.pure' ((c.size, (c.push (Instruction.mul a.1 b.1)).size) : DualRef) ((c.push (Instruction.mul a.1 b.1)).push (Instruction.mul b.2 a.2))
  simpa [pMul, Array.size_push] using this

lemma trip_dualAdd (c : Array Instruction) (a b : DualRef) :
    Trip (dualAdd a b) c (pAdd c a b).2 (pAdd c a b).1 := by
  unfold dualAdd
  refine Trip.bind (trip_emit c _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  have := Trip.pure' ((c.size, (c.push (Instruction.add a.1 b.1)).size) : DualRef) ((c.push (Instruction.add a.1 b.1)).push (Instruction.add a.2 b.2))
  simpa [pAdd, Array.size_push] using this

lemma trip_dualScale (c : Array Instruction) (k : ℤ) (a : DualRef) :
    Trip (dualScale k a) c (pScale c k a).2 (pScale c k a).1 := by
  unfold dualScale
  refine Trip.bind (trip_emit c _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  have := Trip.pure' ((c.size, (c.push (Instruction.scale k a.1)).size) : DualRef) ((c.push (Instruction.scale k a.1)).push (Instruction.scale k a.2))
  simpa [pScale, Array.size_push] using this

lemma forIn_range'_trip {β : Type} (f : ℕ → β → Emit (ForInStep β))
    (P : ℕ → β → Array Instruction → Prop) :
    ∀ (m s : ℕ) (b : β) (c : Array Instruction), P s b c →
      (∀ j, s ≤ j → j < s + m → ∀ b c, P j b c →
        ∃ b' c', Trip (f j b) c (ForInStep.yield b') c' ∧ P (j + 1) b' c') →
      ∃ b' c', Trip (forIn (List.range' s m) b f) c b' c' ∧ P (s + m) b' c' := by
  intro m
  induction m with
  | zero =>
    intro s b c hP _
    refine ⟨b, c, ?_, by simpa using hP⟩
    rw [List.range'_zero, List.forIn_nil]
    exact Trip.pure' b c
  | succ m ih =>
    intro s b c hP hstep
    obtain ⟨b', c', hT, hP'⟩ := hstep s le_rfl (by omega) b c hP
    obtain ⟨b'', c'', hT2, hP''⟩ := ih (s + 1) b' c' hP' (fun j h1 h2 => hstep j (by omega)
      (by omega))
    refine ⟨b'', c'', ?_, by rw [show s + (m + 1) = s + 1 + m by omega]; exact hP''⟩
    rw [List.range'_succ, List.forIn_cons]
    exact Trip.bind hT hT2

end
end UniformADProbes.Trace.Dev.SpanningRun
end

section
/-! The row emitter: one probe step as a pure code transformation. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningRows
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun
noncomputable section

def rowBody (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ)
    (s : Array DualRef × Array DualRef) : Emit (ForInStep (Array DualRef × Array DualRef)) := do
  let u ← tableGet row j zero
  let v ← if j = 0 then pure zero else tableGet row (j - 1) zero
  let n2 := binaryMul N N
  let coeff : ℤ := (n2.value : ℤ) * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ))
  charge (n2.cost + (1 + refBits j + refBits (row.size - 1)) * (1 + refBits n2.value) +
    refBits j + refBits (row.size - 1) + 2)
  let du ← dualMul d u
  let cu ← dualScale coeff u
  let av ← dualMul a v
  let nv ← dualScale (n2.value : ℤ) av
  let q ← dualAdd (← dualAdd du cu) nv
  charge (1 + s.2.size * (1 + refBits q.1 + refBits q.2) +
    s.1.size * (1 + refBits q.1 + refBits q.2))
  pure (ForInStep.yield (s.1.push q, s.2.push q))

lemma emitProbeRows_succ (N : ℕ) (a d zero : DualRef) (k : ℕ) (row all : Array DualRef) :
    emitProbeRows N a d zero (k + 1) row all =
      (forIn (List.range (row.size - 1 + 2)) ((#[] : Array DualRef), all)
        (rowBody N a d zero row)) >>= fun p => emitProbeRows N a d zero k p.1 p.2 := by
  rfl

def vOf (zero : DualRef) (row : Array DualRef) (j : ℕ) : DualRef :=
  if j = 0 then zero else row[j - 1]?.getD zero

def bodyRes (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ) (c : Array Instruction) :
    Array Instruction × DualRef :=
  let u := row[j]?.getD zero
  let v := vOf zero row j
  let κ := N * N
  let coeff : ℤ := (κ : ℤ) * ((j : ℤ) - ((row.size - 1 : ℕ) : ℤ))
  let r1 := pMul c d u
  let r2 := pScale r1.1 coeff u
  let r3 := pMul r2.1 a v
  let r4 := pScale r3.1 (κ : ℤ) r3.2
  let r5 := pAdd r4.1 r1.2 r2.2
  pAdd r5.1 r5.2 r4.2

lemma trip_rowBody (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ)
    (s : Array DualRef × Array DualRef) (c : Array Instruction) :
    Trip (rowBody N a d zero row j s) c
      (ForInStep.yield (s.1.push (bodyRes N a d zero row j c).2, s.2.push (bodyRes N a d zero row j c).2))
      (bodyRes N a d zero row j c).1 := by
  unfold rowBody
  refine Trip.bind (trip_tableGet c row j zero) ?_
  by_cases hj : j = 0
  · simp only [hj, if_true]
    refine Trip.bind (Trip.pure' _ _) ?_
    refine Trip.bind (trip_charge c _) ?_
    refine Trip.bind (trip_dualMul c d _) ?_
    refine Trip.bind (trip_dualScale _ _ _) ?_
    refine Trip.bind (trip_dualMul _ a _) ?_
    refine Trip.bind (trip_dualScale _ _ _) ?_
    refine Trip.bind (trip_dualAdd _ _ _) ?_
    refine Trip.bind (trip_dualAdd _ _ _) ?_
    refine Trip.bind (trip_charge _ _) ?_
    simp only [bodyRes, vOf, hj, if_true]
    exact Trip.pure' _ _
  · simp only [hj, if_false]
    refine Trip.bind (trip_tableGet _ _ _ _) ?_
    refine Trip.bind (trip_charge c _) ?_
    refine Trip.bind (trip_dualMul c d _) ?_
    refine Trip.bind (trip_dualScale _ _ _) ?_
    refine Trip.bind (trip_dualMul _ a _) ?_
    refine Trip.bind (trip_dualScale _ _ _) ?_
    refine Trip.bind (trip_dualAdd _ _ _) ?_
    refine Trip.bind (trip_dualAdd _ _ _) ?_
    refine Trip.bind (trip_charge _ _) ?_
    simp only [bodyRes, vOf, hj, if_false]
    exact Trip.pure' _ _

lemma bodyRes_spec (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j i B L : ℕ)
    (c : Array Instruction) (hi : i = row.size - 1)
    (hbw : BW c) (hl : Lit L c) (hd : DGB B c)
    (ha : Sem c a x 1) (hdd : Sem c d y 1)
    (hu : Sem c (row[j]?.getD zero) (probes N i j) i)
    (hv : Sem c (vOf zero row j) (probes N i ((j : ℤ) - 1)) i)
    (hj : j ≤ i + 1) (hB : i + 1 ≤ B)
    (hκ : signedBits ((N * N : ℕ) : ℤ) ≤ L)
    (hco : signedBits (((N * N : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ))) ≤ L) :
    Sem (bodyRes N a d zero row j c).1 (bodyRes N a d zero row j c).2 (probes N (i + 1) j) (i + 1) ∧
    Ext c (bodyRes N a d zero row j c).1 ∧ BW (bodyRes N a d zero row j c).1 ∧
    Lit L (bodyRes N a d zero row j c).1 ∧ DGB B (bodyRes N a d zero row j c).1 := by
  subst hi
  generalize hu' : row[j]?.getD zero = u at hu
  generalize hv' : vOf zero row j = v at hv
  unfold bodyRes
  simp only [hu', hv']
  set i := row.size - 1 with hi
  set κ := N * N with hκdef
  set coeff : ℤ := (κ : ℤ) * ((j : ℤ) - ((i : ℕ) : ℤ)) with hcoeff
  set P1 := pMul c d u with hP1
  set P2 := pScale P1.1 coeff u with hP2
  set P3 := pMul P2.1 a v with hP3
  set P4 := pScale P3.1 (κ : ℤ) P3.2 with hP4
  set P5 := pAdd P4.1 P1.2 P2.2 with hP5
  set P6 := pAdd P5.1 P5.2 P4.2 with hP6
  have s1 : Sem P1.1 P1.2 (y * probes N i j) (1 + i) := pMul_sem hdd hu
  have g1 := pMul_good (B := B) (L := L) hbw hl hd hdd hu (by omega)
  have e1 : Ext c P1.1 := pMul_ext c d u
  have hu2 := hu.mono e1
  have s2 : Sem P2.1 P2.2 (coeff • probes N i j) i := pScale_sem coeff hu2
  have g2 := pScale_good (B := B) (L := L) coeff g1.1 g1.2.1 g1.2.2 hu2 (by omega) hco
  have e2 : Ext P1.1 P2.1 := pScale_ext P1.1 coeff u
  have ha3 := (ha.mono e1).mono e2
  have hv3 := (hv.mono e1).mono e2
  have s3 : Sem P3.1 P3.2 (x * probes N i ((j : ℤ) - 1)) (1 + i) := pMul_sem ha3 hv3
  have g3 := pMul_good (B := B) (L := L) g2.1 g2.2.1 g2.2.2 ha3 hv3 (by omega)
  have e3 : Ext P2.1 P3.1 := pMul_ext P2.1 a v
  have s4 : Sem P4.1 P4.2 ((κ : ℤ) • (x * probes N i ((j : ℤ) - 1))) (1 + i) :=
    pScale_sem (κ : ℤ) s3
  have g4 := pScale_good (B := B) (L := L) (κ : ℤ) g3.1 g3.2.1 g3.2.2 s3 (by omega) hκ
  have e4 : Ext P3.1 P4.1 := pScale_ext P3.1 (κ : ℤ) P3.2
  have h5a : Sem P4.1 P1.2 (y * probes N i j) (1 + i) := (s1.mono e2 |>.mono e3).mono e4
  have h5b : Sem P4.1 P2.2 (coeff • probes N i j) i := (s2.mono e3).mono e4
  have s5 : Sem P5.1 P5.2 (y * probes N i j + coeff • probes N i j) (max (1 + i) i) :=
    pAdd_sem h5a h5b
  have g5 := pAdd_good (B := B) (L := L) g4.1 g4.2.1 g4.2.2 h5a h5b (by omega)
  have e5 : Ext P4.1 P5.1 := pAdd_ext P4.1 P1.2 P2.2
  have h6b : Sem P5.1 P4.2 ((κ : ℤ) • (x * probes N i ((j : ℤ) - 1))) (1 + i) := s4.mono e5
  have s6 : Sem P6.1 P6.2 ((y * probes N i j + coeff • probes N i j) +
      (κ : ℤ) • (x * probes N i ((j : ℤ) - 1))) (max (max (1 + i) i) (1 + i)) :=
    pAdd_sem s5 h6b
  have g6 := pAdd_good (B := B) (L := L) g5.1 g5.2.1 g5.2.2 s5 h6b (by omega)
  have e6 : Ext P5.1 P6.1 := pAdd_ext P5.1 P5.2 P4.2
  refine ⟨?_, ((((e1.trans e2).trans e3).trans e4).trans e5).trans e6, g6.1, g6.2.1, g6.2.2⟩
  have hP : probes N (i + 1) j = (y * probes N i j + coeff • probes N i j) +
      (κ : ℤ) • (x * probes N i ((j : ℤ) - 1)) := by
    rw [UniformADProbes.Trace.Dev.SpanningCv.probes_succ N i j (by positivity) (by omega)]
    rw [hcoeff, hκdef]
    push_cast
    rw [add_mul, smul_mul_assoc, one_mul, pow_two]
  rw [hP]
  exact s6.le (by omega)

end
end UniformADProbes.Trace.Dev.SpanningRows
end

section
/-! The row loops of `emitProbeRows`. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningLoop
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.SpanningRows
  UniformADProbes.Trace.Dev.SpanningCv
noncomputable section

def rowList (N i : ℕ) : List NCPoly := (List.range (i + 1)).map fun (j : ℕ) => probes N i (j : ℤ)

def upto (N m : ℕ) : List NCPoly := (List.range m).flatMap fun i => rowList N i

lemma upto_succ (N m : ℕ) : upto N (m + 1) = upto N m ++ rowList N m := by
  simp [upto, List.range_succ]

lemma probeList_eq (N : ℕ) : probeList N = upto N N := by
  unfold probeList probeIndices upto rowList
  rw [List.map_flatMap]
  simp only [List.map_map]
  rfl

lemma bodyRes_size (N : ℕ) (a d zero : DualRef) (row : Array DualRef) (j : ℕ) (c : Array Instruction) :
    (bodyRes N a d zero row j c).1.size = c.size + 12 := by
  simp [bodyRes, pMul_size, pAdd_size, pScale_size]

/-- The literal bound `8 * clog 2 (N+1)`. -/
lemma signedBits_le (N : ℕ) (hN : 1 ≤ N) (m : ℤ) (hm : m.natAbs ≤ N ^ 3) :
    signedBits m ≤ 8 * Nat.clog 2 (N + 1) := by
  have hc : 1 ≤ Nat.clog 2 (N + 1) := Nat.clog_pos (by norm_num) (by omega)
  have h1 : N + 1 ≤ 2 ^ Nat.clog 2 (N + 1) := Nat.le_pow_clog (by norm_num) _
  have h2 : m.natAbs < 2 ^ (3 * Nat.clog 2 (N + 1)) := by
    calc m.natAbs ≤ N ^ 3 := hm
      _ < (N + 1) ^ 3 := by gcongr; omega
      _ ≤ (2 ^ Nat.clog 2 (N + 1)) ^ 3 := by gcongr
      _ = 2 ^ (3 * Nat.clog 2 (N + 1)) := by rw [← pow_mul]; ring_nf
  have h3 : m.natAbs.size ≤ 3 * Nat.clog 2 (N + 1) := Nat.size_le.mpr h2
  unfold signedBits
  omega

lemma rowSem_get (N i : ℕ) (row : Array DualRef) (c : Array Instruction)
    (hrow : row.size = i + 1)
    (h : List.Forall₂ (fun r P => Sem c r P i) row.toList (rowList N i)) (t : ℕ) (ht : t < row.size) :
    Sem c row[t] (probes N i (t : ℤ)) i := by
  have hl : row.toList.length = (rowList N i).length := h.length_eq
  have hlen : (rowList N i).length = i + 1 := by simp [rowList]
  have := (List.forall₂_iff_get.mp h).2 t (by simp; omega) (by omega)
  simpa [rowList] using this

lemma probes_zero_row (N i : ℕ) (j : ℤ) (h : j < 0 ∨ (i : ℤ) < j) : probes N i j = 0 :=
  probes_out N i j h

lemma inner_trip (N : ℕ) (hN : 2 ≤ N) (a d zr : DualRef) (i : ℕ) (row all : Array DualRef)
    (c : Array Instruction) (hi : i + 2 ≤ N) (hrow : row.size = i + 1)
    (hbw : BW c) (hl : Lit (8 * Nat.clog 2 (N + 1)) c) (hd : DGB (N - 1) c)
    (hsz : c.size + 8 = 12 * all.size)
    (ha : Sem c a x 1) (hdd : Sem c d y 1) (hz : Sem c zr 0 0)
    (hrowS : List.Forall₂ (fun r P => Sem c r P i) row.toList (rowList N i)) :
    ∃ (next total : Array DualRef) (c' : Array Instruction),
      Trip (forIn (List.range (row.size - 1 + 2)) ((#[] : Array DualRef), all)
        (rowBody N a d zr row)) c (next, total) c' ∧
      Ext c c' ∧ BW c' ∧ Lit (8 * Nat.clog 2 (N + 1)) c' ∧ DGB (N - 1) c' ∧
      c'.size + 8 = 12 * total.size ∧
      List.Forall₂ (fun r P => Sem c' r P (i + 1)) next.toList (rowList N (i + 1)) ∧
      total.toList = all.toList ++ next.toList := by
  set L := 8 * Nat.clog 2 (N + 1) with hL
  have hrs : row.size - 1 + 2 = i + 2 := by omega
  rw [hrs, List.range_eq_range']
  let P : ℕ → (Array DualRef × Array DualRef) → Array Instruction → Prop :=
    fun j b c' => Ext c c' ∧ c'.size + 8 = 12 * (all.size + j) ∧ BW c' ∧ Lit L c' ∧
      DGB (N - 1) c' ∧
      List.Forall₂ (fun r P => Sem c' r P (i + 1)) b.1.toList
        ((List.range j).map fun (t : ℕ) => probes N (i + 1) (t : ℤ)) ∧
      b.2.toList = all.toList ++ b.1.toList
  have hP0 : P 0 ((#[] : Array DualRef), all) c :=
    ⟨Ext.refl c, by simpa using hsz, hbw, hl, hd, by simp, by simp⟩
  obtain ⟨b', c', hT, hPfin⟩ := forIn_range'_trip (rowBody N a d zr row) P (i + 2) 0 _ c hP0 (by
    intro j _ hj b cc hPj
    obtain ⟨hExt, hsz', hbw', hl', hd', hnext, htot⟩ := hPj
    have hj' : j ≤ i + 1 := by omega
    refine ⟨_, _, trip_rowBody N a d zr row j b cc, ?_⟩
    have ha' := ha.mono hExt
    have hdd' := hdd.mono hExt
    have hz' := hz.mono hExt
    have hu : Sem cc (row[j]?.getD zr) (probes N i (j : ℤ)) i := by
      by_cases hjr : j < row.size
      · rw [Array.getElem?_eq_getElem hjr, Option.getD_some]
        exact (rowSem_get N i row c hrow hrowS j hjr).mono hExt
      · have hjj : j = i + 1 := by omega
        rw [Array.getElem?_eq_none (by omega), Option.getD_none]
        have := probes_zero_row N i (j : ℤ) (Or.inr (by omega))
        rw [this]
        exact (hz'.le (Nat.zero_le _))
    have hv : Sem cc (vOf zr row j) (probes N i ((j : ℤ) - 1)) i := by
      unfold vOf
      by_cases hj0 : j = 0
      · rw [if_pos hj0]
        have := probes_zero_row N i ((j : ℤ) - 1) (Or.inl (by omega))
        rw [this]
        exact (hz'.le (Nat.zero_le _))
      · rw [if_neg hj0]
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
        have hjr : j' < row.size := by omega
        rw [Nat.succ_sub_one, Array.getElem?_eq_getElem hjr, Option.getD_some]
        have := (rowSem_get N i row c hrow hrowS j' hjr).mono hExt
        have e : ((j' + 1 : ℕ) : ℤ) - 1 = (j' : ℤ) := by push_cast; ring
        rw [e]; exact this
    have hκ : signedBits ((N * N : ℕ) : ℤ) ≤ L :=
      signedBits_le N (by omega) _ (by
        simp only [Int.natAbs_natCast]
        calc N * N ≤ N * N * N := Nat.le_mul_of_pos_right _ (by omega)
          _ = N ^ 3 := by ring)
    have hco : signedBits (((N * N : ℕ) : ℤ) * ((j : ℤ) - (i : ℤ))) ≤ L :=
      signedBits_le N (by omega) _ (by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
        have : ((j : ℤ) - (i : ℤ)).natAbs ≤ N := by omega
        calc N * N * ((j : ℤ) - (i : ℤ)).natAbs ≤ N * N * N := Nat.mul_le_mul_left _ this
          _ = N ^ 3 := by ring)
    obtain ⟨hS, hE, hB2, hL2, hD2⟩ := bodyRes_spec N a d zr row j i (N - 1) L cc
      (by omega) hbw' hl' hd' ha' hdd' hu hv hj' (by omega) hκ hco
    refine ⟨hExt.trans hE, ?_, hB2, hL2, hD2, ?_, ?_⟩
    · rw [bodyRes_size]; omega
    · simp only [Array.toList_push]
      rw [List.range_succ, List.map_append]
      refine List.rel_append ?_ ?_
      · exact hnext.imp (fun r P h => h.mono hE)
      · exact List.Forall₂.cons hS List.Forall₂.nil
    · simp only [Array.toList_push, htot]
      simp)
  obtain ⟨hExt, hsz', hbw', hl', hd', hnext, htot⟩ := hPfin
  have hlen : b'.1.toList.length = i + 2 := by
    have := hnext.length_eq
    simpa using this
  refine ⟨b'.1, b'.2, c', hT, hExt, hbw', hl', hd', ?_, ?_, htot⟩
  · have : b'.2.size = all.size + (i + 2) := by
      have := congrArg List.length htot
      simp at this
      simp at hlen
      omega
    rw [this]; rw [hsz']; ring
  · have : rowList N (i + 1) = (List.range (0 + (i + 2))).map fun (t : ℕ) => probes N (i + 1) (t : ℤ) := by
      simp [rowList]
    rw [this]; exact hnext

end
end UniformADProbes.Trace.Dev.SpanningLoop
end

section
/-! The whole row emitter and the initial segment. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.SpanningProg
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningRun UniformADProbes.Trace.Dev.SpanningRows
  UniformADProbes.Trace.Dev.SpanningCv UniformADProbes.Trace.Dev.SpanningLoop
noncomputable section

lemma rows_trip (N : ℕ) (hN : 2 ≤ N) (a d zr : DualRef) :
    ∀ (k i : ℕ) (row all : Array DualRef) (c : Array Instruction),
      i + k + 1 = N → row.size = i + 1 → BW c → Lit (8 * Nat.clog 2 (N + 1)) c →
      DGB (N - 1) c → c.size + 8 = 12 * all.size →
      Sem c a x 1 → Sem c d y 1 → Sem c zr 0 0 →
      List.Forall₂ (fun r P => Sem c r P i) row.toList (rowList N i) →
      List.Forall₂ (fun r P => Sem c r P (N - 1)) all.toList (upto N (i + 1)) →
      ∃ (R : Array DualRef) (c' : Array Instruction),
        Trip (emitProbeRows N a d zr k row all) c R c' ∧ BW c' ∧
        Lit (8 * Nat.clog 2 (N + 1)) c' ∧ DGB (N - 1) c' ∧ c'.size + 8 = 12 * R.size ∧
        List.Forall₂ (fun r P => Sem c' r P (N - 1)) R.toList (upto N N) := by
  intro k
  induction k with
  | zero =>
    intro i row all c hk hrow hbw hl hd hsz ha hdd hz hrowS hallS
    have hN' : i + 1 = N := by omega
    refine ⟨all, c, ?_, hbw, hl, hd, hsz, by rw [hN'] at hallS; exact hallS⟩
    unfold emitProbeRows
    exact Trip.pure' _ _
  | succ k ih =>
    intro i row all c hk hrow hbw hl hd hsz ha hdd hz hrowS hallS
    obtain ⟨next, total, c', hT, hExt, hbw', hl', hd', hsz', hnextS, htot⟩ :=
      inner_trip N hN a d zr i row all c (by omega) hrow hbw hl hd hsz ha hdd hz hrowS
    have hnl : next.toList.length = i + 2 := by
      have := hnextS.length_eq
      simpa [rowList] using this
    have hnsize : next.size = (i + 1) + 1 := by simpa using hnl
    have hall' : List.Forall₂ (fun r P => Sem c' r P (N - 1)) total.toList (upto N (i + 1 + 1)) := by
      rw [htot, upto_succ]
      refine List.rel_append ?_ ?_
      · exact hallS.imp (fun r P h => h.mono hExt)
      · exact hnextS.imp (fun r P h => h.le (by omega))
    obtain ⟨R, c'', hT2, h1, h2, h3, h4, h5⟩ := ih (i + 1) next total c' (by omega) hnsize hbw' hl' hd'
      hsz' (ha.mono hExt) (hdd.mono hExt) (hz.mono hExt) hnextS hall'
    refine ⟨R, c'', ?_, h1, h2, h3, h4, h5⟩
    rw [emitProbeRows_succ]
    have hrs : row.size - 1 + 2 = i + 2 := by omega
    exact Trip.bind hT hT2

def code0 : Array Instruction :=
  (((#[].push .identity).push .first).push .second).push (.scale 0 0)

lemma trip_initial : Trip initial #[] ((0, 0), (1, 1), (2, 2), (3, 3)) code0 := by
  unfold initial
  refine Trip.bind (trip_emit #[] _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  refine Trip.bind (trip_emit _ _) ?_
  have := Trip.pure' (((0, 0), (1, 1), (2, 2), (3, 3)) : DualRef × DualRef × DualRef × DualRef) code0
  simpa [code0, Array.size_push] using this

lemma code0_size : code0.size = 4 := by simp [code0]

lemma sem_identity (c : Array Instruction) : Sem (c.push .identity) (c.size, c.size) 1 0 := by
  have h := rv_push_new c .identity
  have h' := dg_push_new c .identity
  refine ⟨by simp, by simp, h, ?_, h'.le, h'.le⟩
  show rv (c.push .identity) c.size = adjoint 1
  rw [SpanningAdj.adjoint_one]; exact h

lemma sem_first (c : Array Instruction) : Sem (c.push .first) (c.size, c.size) x 1 := by
  have h := rv_push_new c .first
  have h' := dg_push_new c .first
  refine ⟨by simp, by simp, h, ?_, h'.le, h'.le⟩
  show rv (c.push .first) c.size = adjoint x
  rw [SpanningAdj.adjoint_x]; exact h

lemma sem_second (c : Array Instruction) : Sem (c.push .second) (c.size, c.size) y 1 := by
  have h := rv_push_new c .second
  have h' := dg_push_new c .second
  refine ⟨by simp, by simp, h, ?_, h'.le, h'.le⟩
  show rv (c.push .second) c.size = adjoint y
  rw [SpanningAdj.adjoint_y]; exact h

lemma sem_zero (c : Array Instruction) (r : ℕ) (hr : r < c.size) (h0 : dg c r = 0) :
    Sem (c.push (.scale 0 r)) (c.size, c.size) 0 0 := by
  have h := rv_push_new c (.scale 0 r)
  have h' := dg_push_new c (.scale 0 r)
  have hv : rv (c.push (.scale 0 r)) c.size = 0 := by
    rw [h]
    show (0 : ℤ) • rv c r = 0
    rw [zero_smul]
  refine ⟨by simp, by simp, hv, ?_, ?_, ?_⟩
  · show rv (c.push (.scale 0 r)) c.size = adjoint 0
    rw [SpanningAdj.adjoint_zero]; exact hv
  · rw [h']; show dg c r ≤ 0; omega
  · rw [h']; show dg c r ≤ 0; omega

lemma init_facts (N : ℕ) (hN : 2 ≤ N) :
    Sem code0 (0, 0) 1 0 ∧ Sem code0 (1, 1) x 1 ∧ Sem code0 (2, 2) y 1 ∧ Sem code0 (3, 3) 0 0 ∧
    BW code0 ∧ Lit (8 * Nat.clog 2 (N + 1)) code0 ∧ DGB (N - 1) code0 := by
  have hc : 1 ≤ Nat.clog 2 (N + 1) := Nat.clog_pos (by norm_num) (by omega)
  have hE1 : (#[] : Array Instruction) = #[] := rfl
  set c1 : Array Instruction := (#[] : Array Instruction).push .identity with hc1
  set c2 := c1.push .first with hc2
  set c3 := c2.push .second with hc3
  have hs1 : c1.size = 1 := by simp [hc1]
  have hs2 : c2.size = 2 := by simp [hc2, hs1]
  have hs3 : c3.size = 3 := by simp [hc3, hs2]
  have hcode : code0 = c3.push (.scale 0 0) := rfl
  have S0 : Sem c1 (0, 0) 1 0 := sem_identity #[]
  have S1 : Sem c2 (1, 1) x 1 := by
    have := sem_first c1; rw [hs1] at this; exact this
  have S2 : Sem c3 (2, 2) y 1 := by
    have := sem_second c2; rw [hs2] at this; exact this
  have x1 : Ext c1 c2 := ext_push c1 .first
  have x2 : Ext c2 c3 := ext_push c2 .second
  have x3 : Ext c3 code0 := ext_push c3 (.scale 0 0)
  have S0' : Sem c3 (0, 0) 1 0 := (S0.mono x1).mono x2
  have d0 : dg c3 0 = 0 := Nat.le_zero.mp S0'.2.2.2.2.1
  have S3 : Sem code0 (3, 3) 0 0 := by
    have := sem_zero c3 0 (by omega) d0
    rw [hs3] at this
    exact this
  have hB : BW code0 := by
    have B1 : BW c1 := BW.empty.push .identity trivial
    have B2 : BW c2 := B1.push .first trivial
    have B3 : BW c3 := B2.push .second trivial
    exact B3.push (.scale 0 0) (by show 0 < c3.size; omega)
  have hL : Lit (8 * Nat.clog 2 (N + 1)) code0 := by
    have e : Lit (8 * Nat.clog 2 (N + 1)) (#[] : Array Instruction) := fun I hI => by simp at hI
    have L1 : Lit (8 * Nat.clog 2 (N + 1)) c1 := e.push .identity (by intro k a h; cases h)
    have L2 : Lit (8 * Nat.clog 2 (N + 1)) c2 := L1.push .first (by intro k a h; cases h)
    have L3 : Lit (8 * Nat.clog 2 (N + 1)) c3 := L2.push .second (by intro k a h; cases h)
    refine L3.push (.scale 0 0) ?_
    intro k a h
    cases h
    unfold signedBits
    simp
    omega
  have hD : DGB (N - 1) code0 := by
    have e : DGB 1 (#[] : Array Instruction) := fun r => by simp [dg, degs_empty]
    have D1 : DGB 1 c1 := e.push .identity (by simp [degreeInstruction])
    have D2 : DGB 1 c2 := D1.push .first (by simp [degreeInstruction])
    have D3 : DGB 1 c3 := D2.push .second (by simp [degreeInstruction])
    have D4 : DGB 1 code0 := D3.push (.scale 0 0) (by
      simp only [degreeInstruction]
      show dg c3 0 ≤ 1
      omega)
    intro r
    have := D4 r
    omega
  exact ⟨(S0.mono (x1.trans x2 |>.trans x3)), (S1.mono x2 |>.mono x3), S2.mono x3, S3, hB, hL, hD⟩

lemma probe_trip (N : ℕ) (hN : 2 ≤ N) :
    ∃ (R : Array DualRef) (c' : Array Instruction),
      (probeProgram N).1 = R ∧ (probeProgram N).2.code = c' ∧ BW c' ∧
      Lit (8 * Nat.clog 2 (N + 1)) c' ∧ DGB (N - 1) c' ∧ c'.size + 8 = 12 * R.size ∧
      List.Forall₂ (fun r P => Sem c' r P (N - 1)) R.toList (probeList N) := by
  obtain ⟨s0, s1, s2, s3, hB, hL, hD⟩ := init_facts N hN
  have e : rowList N 0 = [1] := by simp [rowList, probes]
  have hrow : List.Forall₂ (fun r P => Sem code0 r P 0) (#[((0 : ℕ), (0 : ℕ))] : Array DualRef).toList
      (rowList N 0) := by
    rw [e]
    exact List.Forall₂.cons s0 List.Forall₂.nil
  have hall : List.Forall₂ (fun r P => Sem code0 r P (N - 1))
      (#[((0 : ℕ), (0 : ℕ))] : Array DualRef).toList (upto N (0 + 1)) := by
    have : upto N (0 + 1) = rowList N 0 := by simp [upto]
    rw [this]
    exact hrow.imp (fun r P h => h.le (by omega))
  obtain ⟨R, c', hT, h1, h2, h3, h4, h5⟩ := rows_trip N hN (1, 1) (2, 2) (3, 3) (N - 1) 0
    #[((0 : ℕ), (0 : ℕ))] #[((0 : ℕ), (0 : ℕ))] code0 (by omega) (by simp) hB hL hD
    (by rw [code0_size]; simp) s1 s2 s3 hrow hall
  have hT' : Trip (emitProbes N (0, 0) (1, 1) (2, 2) (3, 3)) code0 R c' := by
    unfold emitProbes
    rw [if_neg (by omega)]
    exact hT
  have hpp : probeProgram N =
      (initial >>= fun t => emitProbes N t.1 t.2.1 t.2.2.1 t.2.2.2).run {} := by
    unfold probeProgram
    rw [if_neg (by omega)]
  have hfull : Trip (initial >>= fun t => emitProbes N t.1 t.2.1 t.2.2.1 t.2.2.2) #[] R c' :=
    Trip.bind trip_initial hT'
  obtain ⟨e1, e2⟩ := hfull {} rfl
  refine ⟨R, c', ?_, ?_, h1, h2, h3, h4, by rw [probeList_eq]; exact h5⟩
  · rw [hpp]; exact e1
  · rw [hpp]; exact e2

end
end UniformADProbes.Trace.Dev.SpanningProg
end

section
/-! Adapted from github.com/Lzp88/AD (Z. Lu), ADComplete.
Uniform spanning probes: bookkeeping of the probe emitter, and the span equality. -/
set_option autoImplicit false
namespace UniformADProbes.Trace.Dev.Spanning
open UniformADProbes.Trace UniformADProbes.Trace.Dev.SpanningCode UniformADProbes.Trace.Dev.SpanningBody
  UniformADProbes.Trace.Dev.SpanningProg UniformADProbes.Trace.Dev.SpanningLoop
  UniformADProbes.Trace.Dev.SpanningCv
noncomputable section

lemma upto_length (N m : ℕ) : (upto N m).length = m * (m + 1) / 2 := by
  induction m with
  | zero => simp [upto]
  | succ m ih =>
    rw [upto_succ, List.length_append, ih]
    have : (rowList N m).length = m + 1 := by simp [rowList]
    rw [this]
    have h : (m + 1) * (m + 1 + 1) = m * (m + 1) + (m + 1) * 2 := by ring
    rw [h, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]

lemma probeList_length (N : ℕ) : (probeList N).length = N * (N + 1) / 2 := by
  rw [probeList_eq, upto_length]

lemma regs_one : rv #[Instruction.identity] 0 = 1 := by
  have := rv_push_new (#[] : Array Instruction) .identity
  exact this

lemma partA_one :
    ∃ (R : Array DualRef) (c' : Array Instruction),
      (probeProgram 1).1 = R ∧ (probeProgram 1).2.code = c' ∧ BW c' ∧ 0 < c'.size ∧
      R.size = 1 * (1 + 1) / 2 ∧ c'.size ≤ 100 * 1 ^ 2 ∧ DGB (1 - 1) c' ∧
      Lit (8 * Nat.clog 2 (1 + 1)) c' ∧
      ∀ j (h : j < R.size), R[j].1 < c'.size ∧ R[j].2 < c'.size ∧
        rv c' R[j].1 = (probeList 1)[j]?.getD 0 ∧ rv c' R[j].2 = adjoint ((probeList 1)[j]?.getD 0) := by
  refine ⟨#[((0 : ℕ), (0 : ℕ))], #[Instruction.identity], rfl, rfl, ?_, by simp, by simp, by simp, ?_, ?_, ?_⟩
  · intro r hr
    simp at hr
    subst hr
    trivial
  · intro r
    simp [dg, degs, degrees, degreeInstruction]
  · intro I hI k a h
    simp at hI
    subst hI
    cases h
  · intro j hj
    simp at hj
    subst hj
    have e : (probeList 1)[0]?.getD 0 = 1 := by
      simp [probeList, probeIndices, probes]
    rw [e]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · exact regs_one
    · rw [SpanningAdj.adjoint_one]; exact regs_one

lemma partA_ge2 (N : ℕ) (hN : 2 ≤ N) :
    ∃ (R : Array DualRef) (c' : Array Instruction),
      (probeProgram N).1 = R ∧ (probeProgram N).2.code = c' ∧ BW c' ∧ 0 < c'.size ∧
      R.size = N * (N + 1) / 2 ∧ c'.size ≤ 100 * N ^ 2 ∧ DGB (N - 1) c' ∧
      Lit (8 * Nat.clog 2 (N + 1)) c' ∧
      ∀ j (h : j < R.size), R[j].1 < c'.size ∧ R[j].2 < c'.size ∧
        rv c' R[j].1 = (probeList N)[j]?.getD 0 ∧ rv c' R[j].2 = adjoint ((probeList N)[j]?.getD 0) := by
  obtain ⟨R, c', h1, h2, hbw, hl, hd, hsz, hS⟩ := probe_trip N hN
  have hlen : R.size = N * (N + 1) / 2 := by
    have := hS.length_eq
    rw [probeList_length] at this
    simpa using this
  have hM : N * (N + 1) / 2 ≤ N * N := by
    apply Nat.div_le_of_le_mul
    nlinarith
  refine ⟨R, c', h1, h2, hbw, ?_, hlen, ?_, hd, hl, ?_⟩
  · have : 3 ≤ N * (N + 1) / 2 := by
      apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
      nlinarith
    omega
  · have : N ^ 2 = N * N := by ring
    rw [this]
    nlinarith
  · intro j hj
    have := (List.forall₂_iff_get.mp hS).2 j (by simpa using hj)
      (by rw [← hS.length_eq]; simpa using hj)
    have hj2 : j < (probeList N).length := by rw [← hS.length_eq]; simpa using hj
    specialize this
    simp only [List.get_eq_getElem, Array.getElem_toList] at this
    rw [List.getElem?_eq_getElem hj2, Option.getD_some]
    obtain ⟨a1, a2, a3, a4, -, -⟩ := this
    exact ⟨a1, a2, a3, a4⟩

lemma conc (N : ℕ) (hN : 1 ≤ N) (p : Array DualRef × Builder) (R : Array DualRef)
    (c' : Array Instruction) (h1 : p.1 = R) (h2 : p.2.code = c') (hbw : BW c') (hpos : 0 < c'.size)
    (hRs : R.size = N * (N + 1) / 2) (hsz : c'.size ≤ 100 * N ^ 2) (hd : DGB (N - 1) c')
    (hl : Lit (8 * Nat.clog 2 (N + 1)) c')
    (hreg : ∀ j (h : j < R.size), R[j].1 < c'.size ∧ R[j].2 < c'.size ∧
        rv c' R[j].1 = (probeList N)[j]?.getD 0 ∧
        rv c' R[j].2 = adjoint ((probeList N)[j]?.getD 0)) :
    (⟨p.2.code, 0⟩ : Circuit).Valid ∧
      (probeList N).length = N * (N + 1) / 2 ∧
      p.1.size = N * (N + 1) / 2 ∧
      (⟨p.2.code, 0⟩ : Circuit).code.size ≤ 100 * N ^ 2 ∧
      (⟨p.2.code, 0⟩ : Circuit).DegreeBound (N - 1) ∧
      (⟨p.2.code, 0⟩ : Circuit).LiteralBound (8 * Nat.clog 2 (N + 1)) ∧
      (∀ j : Fin p.1.size,
        (p.1[j]).1 < (⟨p.2.code, 0⟩ : Circuit).code.size ∧
        (p.1[j]).2 < (⟨p.2.code, 0⟩ : Circuit).code.size ∧
        (registers (⟨p.2.code, 0⟩ : Circuit) x y)[(p.1[j]).1]?.getD 0 = (probeList N)[j.val]?.getD 0 ∧
        (registers (⟨p.2.code, 0⟩ : Circuit) x y)[(p.1[j]).2]?.getD 0 =
          adjoint ((probeList N)[j.val]?.getD 0)) := by
  obtain ⟨q1, q2⟩ := p
  simp only at h1 h2
  subst h1 h2
  refine ⟨⟨hpos, fun k => hbw k.1 k.2⟩, probeList_length N, hRs, hsz, ?_, hl, ?_⟩
  · intro i
    have h := hd i.1
    change (degs q2.code)[i.1]?.getD 0 ≤ N - 1 at h
    have hi : i.1 < (degs q2.code).size := i.2
    rw [Array.getElem?_eq_getElem hi, Option.getD_some] at h
    exact h
  · intro j
    exact hreg j.1 j.2

end
end UniformADProbes.Trace.Dev.Spanning

namespace UniformADProbes.Trace
open UniformADProbes.Trace.Dev.Spanning UniformADProbes.Trace.Dev.SpanningCode
  UniformADProbes.Trace.Dev.SpanningBody in
theorem chk_uniform_spanning_probes :
    ∀ N : ℕ, 1 ≤ N →
      let p := probeProgram N
      let C : Circuit := ⟨p.2.code, 0⟩
      C.Valid ∧
      (probeList N).length = N * (N + 1) / 2 ∧
      p.1.size = N * (N + 1) / 2 ∧
      C.code.size ≤ 100 * N^2 ∧
      C.DegreeBound (N - 1) ∧
      C.LiteralBound (8 * (Nat.clog 2 (N + 1))) ∧
      (∀ j : Fin p.1.size,
        (p.1[j]).1 < C.code.size ∧ (p.1[j]).2 < C.code.size ∧
        (registers C x y)[(p.1[j]).1]?.getD 0 = (probeList N)[j.val]?.getD 0 ∧
        (registers C x y)[(p.1[j]).2]?.getD 0 = adjoint ((probeList N)[j.val]?.getD 0)) ∧
      (∀ n : ℕ, 1 ≤ n → n ≤ N → ∀ H K : Matrix (Fin n) (Fin n) ℝ,
        H.IsSymm → K.IsSymm → spectralDiameter K ≤ (N : ℝ) - 1 →
        ∀ v : Fin n → ℝ, responseSpan H K v (probeList N) = cyclicModule H K v) := by
  intro N hN
  dsimp only
  have hA : ∃ (R : Array DualRef) (c' : Array Instruction),
      (probeProgram N).1 = R ∧ (probeProgram N).2.code = c' ∧ BW c' ∧ 0 < c'.size ∧
      R.size = N * (N + 1) / 2 ∧ c'.size ≤ 100 * N ^ 2 ∧ DGB (N - 1) c' ∧
      Lit (8 * Nat.clog 2 (N + 1)) c' ∧
      ∀ j (h : j < R.size), R[j].1 < c'.size ∧ R[j].2 < c'.size ∧
        rv c' R[j].1 = (probeList N)[j]?.getD 0 ∧
        rv c' R[j].2 = adjoint ((probeList N)[j]?.getD 0) := by
    by_cases h1 : N = 1
    · subst h1; exact partA_one
    · exact partA_ge2 N (by omega)
  obtain ⟨R, c', h1, h2, hbw, hpos, hRs, hsz, hd, hl, hreg⟩ := hA
  have key := conc N hN (probeProgram N) R c' h1 h2 hbw hpos hRs hsz hd hl hreg
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
  refine ⟨k1, k2, k3, k4, k5, k6, k7, ?_⟩
  intro n hn hnN H K hH hK hdiam v
  exact Dev.SpanningKry.span_eq N hN hnN H K hH hK hdiam v

end UniformADProbes.Trace
end

theorem solution : type_of% @UniformADProbes.Trace.chk_uniform_spanning_probes := @UniformADProbes.Trace.chk_uniform_spanning_probes
