-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P15.so9_rank_cartan
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T01:14:14.5351+00:00
-- url     : https://prove2.me/submissions/5397532c-3e37-4e77-95e1-5a4315988194

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P15

open QAlgorithms.Papers.Independent.Gap48.P15

attribute [local instance 100] LieRing.ofAssociativeRing

-- Reuse Mathlib Matrix and Matrix.single directly. Natural one-based
-- coordinates are restricted to Fin coordinates with Matrix.submatrix.


namespace RkFW
open LieAlgebra LieSubalgebra Module Polynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

lemma le_rank (r : ℕ) (h : ∀ x : L, r ≤ (LieAlgebra.ad ℝ L x).charpoly.natTrailingDegree) :
    r ≤ LieAlgebra.rank ℝ L := by
  obtain ⟨x, hx⟩ := LieAlgebra.exists_isRegular ℝ L
  rw [← (LieAlgebra.isRegular_iff_natTrailingDegree_charpoly_eq_rank ℝ x).1 hx]
  exact h x

lemma rank_eq (r : ℕ) (h : ∀ x : L, r ≤ (LieAlgebra.ad ℝ L x).charpoly.natTrailingDegree)
    (x0 : L) (h0 : finrank ℝ (engel ℝ x0) ≤ r) : LieAlgebra.rank ℝ L = r :=
  le_antisymm ((LieAlgebra.rank_le_finrank_engel ℝ x0).trans h0) (le_rank r h)

lemma cartan_engel (x : L) (hx : finrank ℝ (engel ℝ x) ≤ LieAlgebra.rank ℝ L) :
    (engel ℝ x).IsCartanSubalgebra := by
  have h : finrank ℝ L ≤ Cardinal.mk ℝ :=
    (Cardinal.natCast_le_aleph0).trans (Cardinal.infinite_iff.mp inferInstance)
  have hreg : finrank ℝ (engel ℝ x) = LieAlgebra.rank ℝ L :=
    le_antisymm hx (LieAlgebra.rank_le_finrank_engel ℝ x)
  refine ⟨?_, normalizer_engel _ _⟩
  apply isNilpotent_of_forall_le_engel
  intro y hy
  set Ex : {engel ℝ z | z ∈ engel ℝ x} := ⟨engel ℝ x, x, self_mem_engel _ _, rfl⟩
  suffices IsBot Ex from @this ⟨engel ℝ y, y, hy, rfl⟩
  apply LieAlgebra.engel_isBot_of_isMin h (engel ℝ x) Ex le_rfl
  rintro ⟨_, y, hy, rfl⟩ hyx
  suffices finrank ℝ (engel ℝ x) ≤ finrank ℝ (engel ℝ y) by
    suffices engel ℝ y = engel ℝ x from this.ge
    apply LieSubalgebra.toSubmodule_injective
    exact Submodule.eq_of_le_of_finrank_le hyx this
  rw [hreg]
  apply LieAlgebra.rank_le_finrank_engel

/-- engel x0 ≤ H if ad x0 reflects membership in H. -/
lemma engel_le (x0 : L) (H : Submodule ℝ L) (hH : ∀ y, ⁅x0, y⁆ ∈ H → y ∈ H) :
    (engel ℝ x0).toSubmodule ≤ H := by
  intro y hy
  rw [LieSubalgebra.mem_toSubmodule, mem_engel_iff] at hy
  obtain ⟨n, hn⟩ := hy
  induction n generalizing y with
  | zero => simp at hn; rw [hn]; exact H.zero_mem
  | succ n ih =>
    apply hH
    apply ih
    rw [pow_succ, Module.End.mul_apply] at hn
    exact hn

end RkFW

namespace RkFW
open Polynomial

lemma neg_cp {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) :
    (-M).charpoly = (-1) ^ Fintype.card n * M.charpoly.comp (-X) := by
  have h : M.charpoly.comp (-X) = (-1) ^ Fintype.card n * (-M).charpoly := by
    rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    have : (Polynomial.compRingHom (-X : ℝ[X])).mapMatrix M.charmatrix = -((-M).charmatrix) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp; ring
      · simp [hij]
    rw [this, Matrix.det_neg, Matrix.charpoly]
  rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp

lemma coeff_one_comp_neg (p : ℝ[X]) : (p.comp (-X)).coeff 1 = - p.coeff 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [add_comp, hp, hq]; ring
  | monomial k a =>
    rw [← C_mul_X_pow_eq_monomial]
    have : ((C a * X ^ k).comp (-X)) = C (a * (-1) ^ k) * X ^ k := by
      rw [mul_comp, C_comp, X_pow_comp, neg_pow, C_mul, C_pow, C_neg, C_1]; ring
    rw [this, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with hk
    · subst hk; ring
    · simp

lemma even_cp {N : ℕ} (M G : Matrix (Fin N) (Fin N) ℝ) (hG : IsUnit G.det)
    (h : M.transpose * G = -(G * M)) (hN : Even N) : M.charpoly.coeff 1 = 0 := by
  have h1 : M.transpose = G * (-M) * G⁻¹ := by
    rw [Matrix.mul_neg, ← h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.mul_one]
  have h2 : M.charpoly = (-M).charpoly := by
    rw [← Matrix.charpoly_transpose, h1]
    have := Matrix.charpoly_units_conj (Matrix.nonsingInvUnit G hG) (-M)
    exact this
  have h3 := congrArg (fun p => p.coeff 1) h2
  simp only [neg_cp, Fintype.card_fin, hN.neg_one_pow, one_mul, coeff_one_comp_neg] at h3
  linarith

end RkFW

namespace RkFW
open Polynomial Module LieAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {t : ℕ} (L : LieSubalgebra ℝ (Matrix (Fin t) (Fin t) ℝ))

noncomputable def trB : LinearMap.BilinForm ℝ L :=
  LinearMap.mk₂ ℝ (fun y z => Matrix.trace ((y : Matrix (Fin t) (Fin t) ℝ) * (z : Matrix (Fin t) (Fin t) ℝ)))
    (by intros; simp [add_mul, Matrix.trace_add])
    (by intros; simp [Matrix.trace_smul])
    (by intros; simp [mul_add, Matrix.trace_add])
    (by intros; simp [Matrix.trace_smul])

lemma trB_apply (y z : L) : trB L y z = Matrix.trace ((y : Matrix (Fin t) (Fin t) ℝ) * (z : Matrix (Fin t) (Fin t) ℝ)) := rfl

lemma tr_self_transpose (y : Matrix (Fin t) (Fin t) ℝ) (h : Matrix.trace (y * y.transpose) = 0) :
    y = 0 := by
  have h2 : ∀ i, ∀ j, y i j = 0 := by
    have hs : ∑ i, ∑ j, y i j * y i j = 0 := by
      rw [← h]; simp [Matrix.trace, Matrix.mul_apply]
    intro i j
    have hnn : ∀ i, 0 ≤ ∑ j, y i j * y i j := fun i =>
      Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hs i (Finset.mem_univ _)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (y i j))).1 hi j
      (Finset.mem_univ _)
    exact mul_self_eq_zero.1 hj
  ext i j; exact h2 i j

lemma trB_nondeg (hT : ∀ y ∈ L, y.transpose ∈ L) : (trB L).Nondegenerate := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have := hy ⟨(y : Matrix (Fin t) (Fin t) ℝ).transpose, hT _ y.2⟩
    rw [trB_apply] at this
    exact Subtype.ext (tr_self_transpose _ this)
  · have := hy ⟨(y : Matrix (Fin t) (Fin t) ℝ).transpose, hT _ y.2⟩
    rw [trB_apply, Matrix.trace_mul_comm] at this
    exact Subtype.ext (tr_self_transpose _ this)

lemma parity (hT : ∀ y ∈ L, y.transpose ∈ L) (hN : Even (finrank ℝ L)) (hpos : 0 < finrank ℝ L)
    (x : L) : 2 ≤ (ad ℝ L x).charpoly.natTrailingDegree := by
  set b := Module.finBasis ℝ L
  set M := LinearMap.toMatrix b b (ad ℝ L x)
  set G := LinearMap.BilinForm.toMatrix b (trB L)
  have hinv : (trB L).compLeft (ad ℝ L x) = -((trB L).compRight (ad ℝ L x)) := by
    ext y z
    simp only [LinearMap.BilinForm.compLeft_apply, LinearMap.BilinForm.compRight_apply,
      LinearMap.neg_apply, trB_apply, LieAlgebra.ad_apply, LieSubalgebra.coe_bracket, Ring.lie_def]
    rw [sub_mul, mul_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.mul_assoc,
      Matrix.trace_mul_comm (x : Matrix (Fin t) (Fin t) ℝ), Matrix.mul_assoc]
    simp only [Matrix.mul_assoc]; ring
  have h : M.transpose * G = -(G * M) := by
    rw [← LinearMap.BilinForm.toMatrix_compLeft, ← LinearMap.BilinForm.toMatrix_compRight, hinv]
    exact map_neg (LinearMap.BilinForm.toMatrix b) _
  have hG : IsUnit G.det :=
    isUnit_iff_ne_zero.2 ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).1 (trB_nondeg L hT))
  have c1 : M.charpoly.coeff 1 = 0 := even_cp M G hG h hN
  have hdet : M.det = 0 := by
    by_cases hx : x = 0
    · have hM0 : M = 0 := by simp [M, hx]
      have hne : Nonempty (Fin (finrank ℝ L)) := ⟨⟨0, hpos⟩⟩
      rw [hM0]; exact Matrix.det_zero
    · rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨b.repr x, by simpa using hx, ?_⟩
      rw [LinearMap.toMatrix_mulVec_repr]; simp
  have c0 : M.charpoly.coeff 0 = 0 := by
    have := Matrix.det_eq_sign_charpoly_coeff M
    rw [hdet] at this
    have hs : ((-1 : ℝ) ^ Fintype.card (Fin (finrank ℝ L))) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (mul_eq_zero.1 this.symm).resolve_left hs
  rw [← LinearMap.charpoly_toMatrix (ad ℝ L x) b]
  apply Polynomial.le_natTrailingDegree (Matrix.charpoly_monic M).ne_zero
  intro m hm
  interval_cases m
  · exact c0
  · exact c1

end RkFW

namespace RkFW
open Module LieAlgebra LieSubalgebra

attribute [local instance 100] LieRing.ofAssociativeRing

lemma finish {t m : ℕ} (L : LieSubalgebra ℝ (Matrix (Fin t) (Fin t) ℝ))
    (v : Fin m → Matrix (Fin t) (Fin t) ℝ)
    (hlow : ∀ x : L, m ≤ (LieAlgebra.ad ℝ L x).charpoly.natTrailingDegree)
    (x0 : L) (hvL : ∀ i, v i ∈ L) (hcomm : ∀ i, ⁅(x0 : Matrix (Fin t) (Fin t) ℝ), v i⁆ = 0)
    (hlin : LinearIndependent ℝ v)
    (hrefl : ∀ y ∈ L, ⁅(x0 : Matrix (Fin t) (Fin t) ℝ), y⁆ ∈ Submodule.span ℝ (Set.range v) →
      y ∈ Submodule.span ℝ (Set.range v)) :
    LieAlgebra.rank ℝ L = m ∧
    ∃ H : LieSubalgebra ℝ L, H.IsCartanSubalgebra ∧ LinearIndependent ℝ v ∧
      Submodule.span ℝ (Set.range v) = H.toSubmodule.map L.toSubmodule.subtype := by
  set S := Submodule.span ℝ (Set.range v)
  have he : (engel ℝ x0).toSubmodule ≤ S.comap L.toSubmodule.subtype := by
    apply engel_le x0
    intro y hy
    rw [Submodule.mem_comap] at hy ⊢
    exact hrefl y y.2 hy
  have hmap : (engel ℝ x0).toSubmodule.map L.toSubmodule.subtype = S := by
    apply le_antisymm (Submodule.map_le_iff_le_comap.2 he)
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨v i, hvL i⟩, ?_, rfl⟩
    show _ ∈ engel ℝ x0
    rw [mem_engel_iff]
    refine ⟨1, ?_⟩
    rw [pow_one, LieAlgebra.ad_apply]
    exact Subtype.ext (hcomm i)
  have hfin : finrank ℝ (engel ℝ x0) = m := by
    have h1 := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L.toSubmodule.subtype
      Subtype.val_injective (engel ℝ x0).toSubmodule)
    have h2 : finrank ℝ S = m := by
      rw [finrank_span_eq_card hlin, Fintype.card_fin]
    rw [hmap] at h1
    exact h1.trans h2
  have hrank : LieAlgebra.rank ℝ L = m := rank_eq m hlow x0 hfin.le
  exact ⟨hrank, engel ℝ x0, cartan_engel x0 (by rw [hrank, hfin]), hlin, hmap.symm⟩

end RkFW

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace RkLow
open Module LieAlgebra LieSubalgebra Polynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {t m : ℕ} (L : LieSubalgebra ℝ (Matrix (Fin t) (Fin t) ℝ))

/-- the m×m test matrix -/
def G (A : Fin m → Matrix (Fin t) (Fin t) ℝ) (e : Fin m → ℕ) (p q : Fin m → Fin t)
    (y : Matrix (Fin t) (Fin t) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun j k => (A j * y ^ e j) (p k) (q k)

lemma pointwise (A : Fin m → Matrix (Fin t) (Fin t) ℝ) (e : Fin m → ℕ) (p q : Fin m → Fin t)
    (W : Fin m → Matrix (Fin t) (Fin t) ℝ → Matrix (Fin t) (Fin t) ℝ)
    (hW : ∀ x ∈ L, ∀ j, W j x ∈ L ∧ x * W j x = W j x * x)
    (hent : ∀ y j k, W j y (p k) (q k) = (A j * y ^ e j) (p k) (q k))
    (x : L) (hx : (G A e p q x).det ≠ 0) :
    m ≤ (LieAlgebra.ad ℝ L x).charpoly.natTrailingDegree := by
  rw [← LieAlgebra.finrank_engel]
  let w : Fin m → engel ℝ x := fun j =>
    ⟨⟨W j x, (hW x x.2 j).1⟩, by
      rw [mem_engel_iff]; refine ⟨1, ?_⟩
      rw [pow_one, LieAlgebra.ad_apply]
      apply Subtype.ext
      simp only [LieSubalgebra.coe_bracket, Ring.lie_def, ZeroMemClass.coe_zero]
      rw [(hW x x.2 j).2, sub_self]⟩
  have hlin : LinearIndependent ℝ w := by
    apply LinearIndependent.of_comp (L.toSubmodule.subtype ∘ₗ (engel ℝ x).toSubmodule.subtype)
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have he : ∀ k, ∑ j, c j * G A e p q x j k = 0 := by
      intro k
      have := congrFun (congrFun hc (p k)) (q k)
      simp only [Function.comp_apply, LinearMap.coe_comp, Submodule.coe_subtype, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, w] at this
      simpa [G, hent] using this
    by_contra hne
    push Not at hne
    have : ∃ v ≠ 0, Matrix.mulVec (G A e p q x).transpose v = 0 := by
      refine ⟨c, fun h => ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hne; exact hi (congrFun h i)
      · funext k; simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
        rw [← he k]; exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [Matrix.exists_mulVec_eq_zero_iff, Matrix.det_transpose] at this
    exact hx this
  have := hlin.fintype_card_le_finrank
  simpa using this

lemma le_rank (A : Fin m → Matrix (Fin t) (Fin t) ℝ) (e : Fin m → ℕ) (p q : Fin m → Fin t)
    (W : Fin m → Matrix (Fin t) (Fin t) ℝ → Matrix (Fin t) (Fin t) ℝ)
    (hW : ∀ x ∈ L, ∀ j, W j x ∈ L ∧ x * W j x = W j x * x)
    (hent : ∀ y j k, W j y (p k) (q k) = (A j * y ^ e j) (p k) (q k))
    (x0 : L) (h0 : (G A e p q x0).det ≠ 0) :
    m ≤ LieAlgebra.rank ℝ L := by
  set b := Module.finBasis ℝ L
  set N := finrank ℝ L
  let Xb : Matrix (Fin t) (Fin t) (MvPolynomial (Fin N) ℝ) :=
    Matrix.of fun i j => ∑ k, MvPolynomial.C ((b k : Matrix (Fin t) (Fin t) ℝ) i j) * MvPolynomial.X k
  let Q : MvPolynomial (Fin N) ℝ :=
    (Matrix.of fun j k => (((A j).map MvPolynomial.C * Xb ^ e j :
      Matrix (Fin t) (Fin t) (MvPolynomial (Fin N) ℝ))) (p k) (q k)).det
  have hX : ∀ x : L, (MvPolynomial.eval (b.repr x)).mapMatrix Xb = (x : Matrix (Fin t) (Fin t) ℝ) := by
    intro x; ext i j
    have h1 : (x : Matrix (Fin t) (Fin t) ℝ) = ∑ k, b.repr x k • (b k : Matrix (Fin t) (Fin t) ℝ) := by
      conv_lhs => rw [← b.sum_repr x]
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    have h := congrFun (congrFun h1 i) j
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at h
    simp [Xb, Matrix.map_apply]
    rw [h]
    refine Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hA : ∀ (x : L) j, (MvPolynomial.eval (b.repr x)).mapMatrix ((A j).map MvPolynomial.C) = A j := by
    intro x j; ext i i'; simp
  have hev : ∀ x : L, MvPolynomial.eval (b.repr x) Q = (G A e p q x).det := by
    intro x
    rw [RingHom.map_det]
    congr 1
    ext j k
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, G]
    have := congrFun (congrFun (map_mul (MvPolynomial.eval (b.repr x)).mapMatrix
      ((A j).map MvPolynomial.C) (Xb ^ e j)) (p k)) (q k)
    rw [map_pow, hA, hX] at this
    simpa [RingHom.mapMatrix_apply] using this
  have hQ : Q ≠ 0 := by
    intro h; apply h0; rw [← hev, h, map_zero]
  rw [LieAlgebra.rank_eq_natTrailingDegree (b := b)]
  apply Polynomial.le_natTrailingDegree (LinearMap.polyCharpoly_ne_zero _ b)
  intro k hk
  have hz : (LinearMap.polyCharpoly (ad ℝ L).toLinearMap b).coeff k * Q = 0 := by
    apply MvPolynomial.funext
    intro pt
    set x : L := b.equivFun.symm pt
    have hpt : (b.repr x : Fin N → ℝ) = pt := by
      funext i; rw [← b.equivFun_apply]; simp [x, Finsupp.single_apply]
    rw [map_mul, map_zero, ← hpt, LinearMap.polyCharpoly_coeff_eval, hev]
    by_cases hd : (G A e p q x).det = 0
    · rw [hd, mul_zero]
    · have := pointwise L A e p q W hW hent x hd
      show (LinearMap.charpoly ((ad ℝ L) x)).coeff k * _ = 0
      rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hk this), zero_mul]
  exact (mul_eq_zero.1 hz).resolve_right hQ

end RkLow

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace SoR
open Matrix

variable {n m : ℕ} (p q : Fin m → Fin n) (lam : Fin m → ℝ)

def Jm (a b : Fin n) : Matrix (Fin n) (Fin n) ℝ := single a b 1 - single b a 1

noncomputable def X0 : Matrix (Fin n) (Fin n) ℝ := ∑ k, lam k • Jm (p k) (q k)

variable {p q}
lemma X0_apply (a c : Fin n) : X0 p q lam a c =
    ∑ k, lam k * ((if p k = a ∧ q k = c then 1 else 0) - (if q k = a ∧ p k = c then 1 else 0)) := by
  simp [X0, Jm, Matrix.sum_apply, Matrix.single_apply]

variable (hp : Function.Injective p) (hq : Function.Injective q) (hpq : ∀ k l, p k ≠ q l)
include hp hq hpq

lemma col_q (c : Fin n) (l : Fin m) : X0 p q lam c (q l) = if c = p l then lam l else 0 := by
  rw [X0_apply, Finset.sum_eq_single l]
  · have : ¬ (q l = p l) := fun h => hpq l l h.symm
    by_cases hc : c = p l <;> simp [hc, this, Ne.symm this, eq_comm]
  · intro k _ hk
    have h1 : ¬ (q l = q k) := fun h => hk (hq h).symm
    have h2 : ¬ (q l = p k) := fun h => hpq k l h.symm
    simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · simp

lemma col_p (c : Fin n) (l : Fin m) : X0 p q lam c (p l) = if c = q l then -lam l else 0 := by
  rw [X0_apply, Finset.sum_eq_single l]
  · have : ¬ (p l = q l) := hpq l l
    by_cases hc : c = q l <;> simp [hc, this, Ne.symm this, eq_comm]
  · intro k _ hk
    have h1 : ¬ (p l = p k) := fun h => hk (hp h).symm
    have h2 : ¬ (p l = q k) := hpq l k
    simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · simp

lemma row_p (c : Fin n) (k : Fin m) : X0 p q lam (p k) c = if c = q k then lam k else 0 := by
  rw [X0_apply, Finset.sum_eq_single k]
  · have : ¬ (p k = q k) := hpq k k
    by_cases hc : c = q k <;> simp [hc, this, Ne.symm this, eq_comm]
  · intro l _ hl
    have h1 : ¬ (p k = p l) := fun h => hl (hp h).symm
    have h2 : ¬ (p k = q l) := hpq k l
    simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · simp

lemma row_q (c : Fin n) (k : Fin m) : X0 p q lam (q k) c = if c = p k then -lam k else 0 := by
  rw [X0_apply, Finset.sum_eq_single k]
  · have : ¬ (q k = p k) := fun h => hpq k k h.symm
    by_cases hc : c = p k <;> simp [hc, this, Ne.symm this, eq_comm]
  · intro l _ hl
    have h1 : ¬ (q k = q l) := fun h => hl (hq h).symm
    have h2 : ¬ (q k = p l) := fun h => hpq l k h.symm
    simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · simp

lemma unp_row (r c : Fin n) (hr1 : ∀ k, r ≠ p k) (hr2 : ∀ k, r ≠ q k) : X0 p q lam r c = 0 := by
  rw [X0_apply]; apply Finset.sum_eq_zero; intro k _; simp [hr1 k, hr2 k, Ne.symm (hr1 k), Ne.symm (hr2 k)]

lemma unp_col (r c : Fin n) (hr1 : ∀ k, r ≠ p k) (hr2 : ∀ k, r ≠ q k) : X0 p q lam c r = 0 := by
  rw [X0_apply]; apply Finset.sum_eq_zero; intro k _; simp [hr1 k, hr2 k, Ne.symm (hr1 k), Ne.symm (hr2 k)]

lemma mul_q (M : Matrix (Fin n) (Fin n) ℝ) (a : Fin n) (l : Fin m) :
    (M * X0 p q lam) a (q l) = M a (p l) * lam l := by
  rw [Matrix.mul_apply]; simp_rw [col_q lam hp hq hpq]; simp

lemma mul_p (M : Matrix (Fin n) (Fin n) ℝ) (a : Fin n) (l : Fin m) :
    (M * X0 p q lam) a (p l) = M a (q l) * (-lam l) := by
  rw [Matrix.mul_apply]; simp_rw [col_p lam hp hq hpq]; simp

lemma pmul (M : Matrix (Fin n) (Fin n) ℝ) (b : Fin n) (k : Fin m) :
    (X0 p q lam * M) (p k) b = lam k * M (q k) b := by
  rw [Matrix.mul_apply]; simp_rw [row_p lam hp hq hpq]; simp

lemma qmul (M : Matrix (Fin n) (Fin n) ℝ) (b : Fin n) (k : Fin m) :
    (X0 p q lam * M) (q k) b = -lam k * M (p k) b := by
  rw [Matrix.mul_apply]; simp_rw [row_q lam hp hq hpq]; simp

lemma pow_q (j : ℕ) (a : Fin n) (l : Fin m) :
    (X0 p q lam ^ (2 * j + 1)) a (q l) = if a = p l then (-1) ^ j * lam l ^ (2 * j + 1) else 0 := by
  induction j with
  | zero => simp [col_q lam hp hq hpq]
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by ring, pow_succ, pow_succ, mul_q lam hp hq hpq,
      mul_p lam hp hq hpq, ih]
    split_ifs <;> ring

lemma unp_mul (M : Matrix (Fin n) (Fin n) ℝ) (r b : Fin n) (hr1 : ∀ k, r ≠ p k) (hr2 : ∀ k, r ≠ q k) :
    (X0 p q lam * M) r b = 0 := by
  rw [Matrix.mul_apply]; simp [unp_row lam hp hq hpq r _ hr1 hr2]

lemma cls (a : Fin n) : (∃ k, a = p k) ∨ (∃ k, a = q k) ∨ ((∀ k, a ≠ p k) ∧ (∀ k, a ≠ q k)) := by
  by_cases h1 : ∃ k, a = p k
  · exact Or.inl h1
  · by_cases h2 : ∃ k, a = q k
    · exact Or.inr (Or.inl h2)
    · push Not at h1 h2; exact Or.inr (Or.inr ⟨h1, h2⟩)

lemma central (hlam0 : ∀ k, lam k ≠ 0) (hlam : ∀ k l, k ≠ l → lam k ^ 2 ≠ lam l ^ 2)
    (hunp : ∀ r s : Fin n, (∀ k, r ≠ p k) → (∀ k, r ≠ q k) → (∀ k, s ≠ p k) → (∀ k, s ≠ q k) → r = s)
    (y : Matrix (Fin n) (Fin n) ℝ) (hy : y.transpose = -y) (hc : X0 p q lam * y = y * X0 p q lam) :
    y = X0 p q (fun k => y (p k) (q k)) := by
  have E : ∀ a b, (X0 p q lam * y) a b = (y * X0 p q lam) a b := fun a b => by rw [hc]
  have sk : ∀ a b, y b a = - y a b := fun a b => by
    have := congrFun (congrFun hy a) b; simpa using this
  have key : ∀ (Y Y' : ℝ) (k l : Fin m), k ≠ l → lam k * Y' = Y * lam l → lam k * Y = Y' * lam l → Y = 0 := by
    intro Y Y' k l hkl h1 h2
    have : (lam k ^ 2 - lam l ^ 2) * Y = 0 := by linear_combination lam k * h2 + lam l * h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (hlam k l hkl))
  have key2 : ∀ (Y Y' : ℝ) (k l : Fin m), k ≠ l → lam k * Y' = Y * (-lam l) → -lam k * Y = Y' * lam l → Y = 0 := by
    intro Y Y' k l hkl h1 h2
    have : (lam k ^ 2 - lam l ^ 2) * Y = 0 := by linear_combination (-lam k) * h2 - lam l * h1
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 (hlam k l hkl))
  have dz : ∀ a, y a a = 0 := fun a => by linarith [sk a a]
  set c := fun k => y (p k) (q k)
  ext a b
  rcases cls hp hq hpq a with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨ha1, ha2⟩ <;>
  rcases cls hp hq hpq b with ⟨l, rfl⟩ | ⟨l, rfl⟩ | ⟨hb1, hb2⟩
  · -- (p k, p l)
    rw [row_p c hp hq hpq, if_neg (hpq l k)]
    by_cases hkl : k = l
    · subst hkl; exact dz _
    · have e1 := E (p k) (q l); have e2 := E (q k) (p l)
      rw [pmul lam hp hq hpq, mul_q lam hp hq hpq] at e1
      rw [qmul lam hp hq hpq, mul_p lam hp hq hpq] at e2
      exact key _ _ k l hkl e1 (by linarith)
  · -- (p k, q l)
    rw [row_p c hp hq hpq]
    by_cases hkl : k = l
    · subst hkl; simp [c]
    · rw [if_neg (fun h => hkl (hq h).symm)]
      have e1 := E (p k) (p l); have e2 := E (q k) (q l)
      rw [pmul lam hp hq hpq, mul_p lam hp hq hpq] at e1
      rw [qmul lam hp hq hpq, mul_q lam hp hq hpq] at e2
      exact key2 _ _ k l hkl e1 e2
  · -- (p k, r)
    rw [row_p c hp hq hpq, if_neg (hb2 k), sk]
    have e := E b (q k)
    rw [unp_mul lam hp hq hpq _ _ _ hb1 hb2, mul_q lam hp hq hpq] at e
    have := (mul_eq_zero.1 e.symm).resolve_right (hlam0 k)
    rw [this, neg_zero]
  · -- (q k, p l)
    rw [row_q c hp hq hpq]
    by_cases hkl : k = l
    · subst hkl; simp only [c, if_true]; rw [sk]
    · rw [if_neg (fun h => hkl (hp h).symm)]
      have e1 := E (p k) (p l); have e2 := E (q k) (q l)
      rw [pmul lam hp hq hpq, mul_p lam hp hq hpq] at e1
      rw [qmul lam hp hq hpq, mul_q lam hp hq hpq] at e2
      have hY := key2 _ _ k l hkl e1 e2
      rw [hY] at e1
      have : lam k * y (q k) (p l) = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left (hlam0 k)
  · -- (q k, q l)
    rw [row_q c hp hq hpq, if_neg (fun h => hpq k l h.symm)]
    by_cases hkl : k = l
    · subst hkl; exact dz _
    · have e1 := E (p k) (q l); have e2 := E (q k) (p l)
      rw [pmul lam hp hq hpq, mul_q lam hp hq hpq] at e1
      rw [qmul lam hp hq hpq, mul_p lam hp hq hpq] at e2
      exact key _ _ k l hkl (by linarith) e1
  · -- (q k, r)
    rw [row_q c hp hq hpq, if_neg (hb1 k), sk]
    have e := E b (p k)
    rw [unp_mul lam hp hq hpq _ _ _ hb1 hb2, mul_p lam hp hq hpq] at e
    have : y b (q k) = 0 := by
      have h' : y b (q k) * lam k = 0 := by linarith
      exact (mul_eq_zero.1 h').resolve_right (hlam0 k)
    rw [this, neg_zero]
  · -- (r, p l)
    rw [unp_row c hp hq hpq _ _ ha1 ha2]
    have e := E a (q l)
    rw [unp_mul lam hp hq hpq _ _ _ ha1 ha2, mul_q lam hp hq hpq] at e
    exact (mul_eq_zero.1 e.symm).resolve_right (hlam0 l)
  · -- (r, q l)
    rw [unp_row c hp hq hpq _ _ ha1 ha2]
    have e := E a (p l)
    rw [unp_mul lam hp hq hpq _ _ _ ha1 ha2, mul_p lam hp hq hpq] at e
    have h' : y a (q l) * lam l = 0 := by linarith
    exact (mul_eq_zero.1 h').resolve_right (hlam0 l)
  · -- (r, s)
    rw [unp_row c hp hq hpq _ _ ha1 ha2, hunp a b ha1 ha2 hb1 hb2]; exact dz _

lemma X0_comm (mu : Fin m → ℝ) : X0 p q lam * X0 p q mu = X0 p q mu * X0 p q lam := by
  ext a b
  rcases cls hp hq hpq a with ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨ha1, ha2⟩
  · rw [pmul lam hp hq hpq, pmul mu hp hq hpq, row_q mu hp hq hpq, row_q lam hp hq hpq]
    split_ifs <;> ring
  · rw [qmul lam hp hq hpq, qmul mu hp hq hpq, row_p mu hp hq hpq, row_p lam hp hq hpq]
    split_ifs <;> ring
  · rw [unp_mul lam hp hq hpq _ _ _ ha1 ha2, unp_mul mu hp hq hpq _ _ _ ha1 ha2]

omit hp hq hpq in
lemma X0_skew : (X0 p q lam).transpose = -(X0 p q lam) := by
  simp only [X0, Jm, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_sub,
    Matrix.transpose_single, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← smul_neg, neg_sub]

omit hp hq hpq in
lemma Jm_eq (l : Fin m) : Jm (p l) (q l) = X0 p q (Pi.single l 1) := by
  simp [X0, Pi.single_apply]

omit hp hq hpq in
lemma tr_self_transpose (y : Matrix (Fin n) (Fin n) ℝ) (h : Matrix.trace (y * y.transpose) = 0) :
    y = 0 := by
  have h2 : ∀ i, ∀ j, y i j = 0 := by
    have hs : ∑ i, ∑ j, y i j * y i j = 0 := by
      rw [← h]; simp [Matrix.trace, Matrix.mul_apply]
    intro i j
    have hnn : ∀ i, 0 ≤ ∑ j, y i j * y i j := fun i =>
      Finset.sum_nonneg (fun j _ => mul_self_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hs i (Finset.mem_univ _)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (y i j))).1 hi j
      (Finset.mem_univ _)
    exact mul_self_eq_zero.1 hj
  ext i j; exact h2 i j

omit hp hq hpq in
lemma frob (X y : Matrix (Fin n) (Fin n) ℝ) (hX : X.transpose = -X)
    (hc : X * (X * y - y * X) = (X * y - y * X) * X) : X * y - y * X = 0 := by
  apply tr_self_transpose
  set Z := X * y - y * X with hZ
  have hZt : Z.transpose = X * y.transpose - y.transpose * X := by
    rw [hZ, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul, hX]
    simp [Matrix.mul_neg, Matrix.neg_mul]; abel
  rw [hZt, Matrix.mul_sub, Matrix.trace_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc Z,
    Matrix.trace_mul_comm (Z * y.transpose) X, ← Matrix.mul_assoc, hc, sub_self]

end SoR
namespace RkFW
open Module LieAlgebra LieSubalgebra

attribute [local instance 100] LieRing.ofAssociativeRing

lemma finish2 {t m : ℕ} (L : LieSubalgebra ℝ (Matrix (Fin t) (Fin t) ℝ))
    (v : Fin m → Matrix (Fin t) (Fin t) ℝ)
    (hlow : m ≤ LieAlgebra.rank ℝ L)
    (x0 : L) (hvL : ∀ i, v i ∈ L) (hcomm : ∀ i, ⁅(x0 : Matrix (Fin t) (Fin t) ℝ), v i⁆ = 0)
    (hlin : LinearIndependent ℝ v)
    (hrefl : ∀ y ∈ L, ⁅(x0 : Matrix (Fin t) (Fin t) ℝ), y⁆ ∈ Submodule.span ℝ (Set.range v) →
      y ∈ Submodule.span ℝ (Set.range v)) :
    LieAlgebra.rank ℝ L = m ∧
    ∃ H : LieSubalgebra ℝ L, H.IsCartanSubalgebra ∧ LinearIndependent ℝ v ∧
      Submodule.span ℝ (Set.range v) = H.toSubmodule.map L.toSubmodule.subtype := by
  set S := Submodule.span ℝ (Set.range v)
  have he : (engel ℝ x0).toSubmodule ≤ S.comap L.toSubmodule.subtype := by
    apply engel_le x0
    intro y hy
    rw [Submodule.mem_comap] at hy ⊢
    exact hrefl y y.2 hy
  have hmap : (engel ℝ x0).toSubmodule.map L.toSubmodule.subtype = S := by
    apply le_antisymm (Submodule.map_le_iff_le_comap.2 he)
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨v i, hvL i⟩, ?_, rfl⟩
    show _ ∈ engel ℝ x0
    rw [mem_engel_iff]
    refine ⟨1, ?_⟩
    rw [pow_one, LieAlgebra.ad_apply]
    exact Subtype.ext (hcomm i)
  have hfin : finrank ℝ (engel ℝ x0) = m := by
    have h1 := LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L.toSubmodule.subtype
      Subtype.val_injective (engel ℝ x0).toSubmodule)
    have h2 : finrank ℝ S = m := by
      rw [finrank_span_eq_card hlin, Fintype.card_fin]
    rw [hmap] at h1
    exact h1.trans h2
  have hrank : LieAlgebra.rank ℝ L = m :=
    le_antisymm ((LieAlgebra.rank_le_finrank_engel ℝ x0).trans hfin.le) hlow
  exact ⟨hrank, engel ℝ x0, cartan_engel x0 (by rw [hrank, hfin]), hlin, hmap.symm⟩

end RkFW

namespace SoR
open Matrix Module

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n m : ℕ} {p q : Fin m → Fin n}

lemma so_main (hp : Function.Injective p) (hq : Function.Injective q) (hpq : ∀ k l, p k ≠ q l)
    (hcov : ∀ r s : Fin n, (∀ k, r ≠ p k) → (∀ k, r ≠ q k) → (∀ k, s ≠ p k) → (∀ k, s ≠ q k) → r = s) :
    LieAlgebra.rank ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ) = m ∧
    ∃ H : LieSubalgebra ℝ (LieAlgebra.Orthogonal.so (Fin n) ℝ), H.IsCartanSubalgebra ∧
      LinearIndependent ℝ (fun k => Jm (p k) (q k)) ∧
      Submodule.span ℝ (Set.range (fun k => Jm (p k) (q k))) =
        H.toSubmodule.map (LieAlgebra.Orthogonal.so (Fin n) ℝ).toSubmodule.subtype := by
  set L := LieAlgebra.Orthogonal.so (Fin n) ℝ
  set lam : Fin m → ℝ := fun k => (k : ℝ) + 1 with hlamdef
  have hlam0 : ∀ k, lam k ≠ 0 := fun k => by simp only [lam]; positivity
  have hlam : ∀ k l, k ≠ l → lam k ^ 2 ≠ lam l ^ 2 := by
    intro k l hkl h
    apply hkl
    have h' : ((k : ℝ) + 1 - ((l : ℝ) + 1)) * (((k : ℝ) + 1) + ((l : ℝ) + 1)) = 0 := by
      simp only [lam] at h; linear_combination h
    have hpos : ((k : ℝ) + 1) + ((l : ℝ) + 1) ≠ 0 := by positivity
    have := (mul_eq_zero.1 h').resolve_right hpos
    exact Fin.ext (by exact_mod_cast (by linarith : (k : ℝ) = l))
  have memso : ∀ y : Matrix (Fin n) (Fin n) ℝ, y ∈ L ↔ y.transpose = -y :=
    fun y => LieAlgebra.Orthogonal.mem_so (n := Fin n) (R := ℝ) y
  let x0 : L := ⟨X0 p q lam, (memso _).2 (X0_skew lam)⟩
  apply RkFW.finish2 L (fun k => Jm (p k) (q k)) _ x0
  · intro i; rw [memso, Jm_eq, X0_skew]
  · intro i
    show ⁅X0 p q lam, Jm (p i) (q i)⁆ = 0
    rw [Jm_eq, Ring.lie_def, X0_comm lam hp hq hpq, sub_self]
  · rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h : X0 p q c = 0 := hc
    have := congrFun (congrFun h (p k)) (q k)
    rwa [row_p c hp hq hpq, if_pos rfl] at this
  · intro y hy hb
    have hcm : ∀ Z ∈ Submodule.span ℝ (Set.range (fun k => Jm (p k) (q k))),
        X0 p q lam * Z = Z * X0 p q lam := by
      intro Z hZ
      induction hZ using Submodule.span_induction with
      | mem x hx => obtain ⟨k, rfl⟩ := hx; simp only; rw [Jm_eq, X0_comm lam hp hq hpq]
      | zero => simp
      | add a b _ _ ha hb => rw [Matrix.mul_add, Matrix.add_mul, ha, hb]
      | smul r a _ ha => rw [Matrix.mul_smul, Matrix.smul_mul, ha]
    have hZ := frob (X0 p q lam) y (X0_skew lam) (by
      have := hcm _ hb; rwa [Ring.lie_def] at this)
    have hc : X0 p q lam * y = y * X0 p q lam := sub_eq_zero.1 hZ
    rw [central lam hp hq hpq hlam0 hlam hcov y ((memso y).1 hy) hc]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  · -- lower bound
    apply RkLow.le_rank L (fun _ => 1) (fun j => 2 * (j : ℕ) + 1) p q (fun j y => y ^ (2 * (j : ℕ) + 1))
      _ (by intro y j k; simp) x0
    · -- det at x0
      have hG : RkLow.G (fun _ => 1) (fun j => 2 * (j : ℕ) + 1) p q (x0 : Matrix (Fin n) (Fin n) ℝ) =
          Matrix.diagonal (fun j : Fin m => (-1 : ℝ) ^ (j : ℕ)) *
            (Matrix.vandermonde (fun k => lam k ^ 2)).transpose * Matrix.diagonal lam := by
        ext j k
        simp only [RkLow.G, Matrix.of_apply, one_mul, x0, pow_q lam hp hq hpq, if_pos rfl, if_true, ↓reduceIte,
          Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.vandermonde_apply]
        ring
      rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
        Matrix.det_transpose]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact Finset.prod_ne_zero_iff.2 (fun j _ => pow_ne_zero _ (by norm_num))
      · rw [Matrix.det_vandermonde_ne_zero_iff]
        intro a b h
        by_contra hab
        exact hlam a b hab h
      · exact Finset.prod_ne_zero_iff.2 (fun j _ => hlam0 j)
    · intro x hx j
      refine ⟨?_, (Commute.self_pow x _).eq⟩
      rw [memso] at hx ⊢
      rw [Matrix.transpose_pow, hx, Odd.neg_pow ⟨j, rfl⟩]

end SoR

namespace SoInst
open QAlgorithms.Papers.Independent.Gap48.P15

lemma J_eq (t a b : ℕ) (i j : Fin t) (hi : i.val + 1 = a) (hj : j.val + 1 = b) :
    J t a b = SoR.Jm i j := by
  subst hi hj
  ext r c
  simp [J, SoR.Jm, Matrix.single_apply, Fin.ext_iff]

lemma hcov_of {n m : ℕ} (p q : Fin m → Fin n) (h : ∀ r : Fin n, (∃ k, r = p k) ∨ (∃ k, r = q k)) :
    ∀ r s : Fin n, (∀ k, r ≠ p k) → (∀ k, r ≠ q k) → (∀ k, s ≠ p k) → (∀ k, s ≠ q k) → r = s := by
  intro r s h1 h2 _ _
  rcases h r with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact absurd hk (h1 k)
  · exact absurd hk (h2 k)

end SoInst

namespace SoInst
def p : Fin 4 → Fin 9 := ![0, 7, 5, 3]
def q : Fin 4 → Fin 9 := ![1, 8, 6, 4]
end SoInst

/-- so(9) has rank 4 and Cartan basis [b1,b36,b31,b22].
Source: PDF p. 7, RankOfSo[9,{b1}]. -/
theorem solution :
    LieAlgebra.rank ℝ (LieAlgebra.Orthogonal.so (Fin 9) ℝ) = 4 ∧
    isCartanBasisFor (LieAlgebra.Orthogonal.so (Fin 9) ℝ)
      ![J 9 1 2, J 9 8 9, J 9 6 7, J 9 4 5] := by
  have hv : (![J 9 1 2, J 9 8 9, J 9 6 7, J 9 4 5] : Fin 4 → Matrix (Fin 9) (Fin 9) ℝ) =
      fun k => SoR.Jm (SoInst.p k) (SoInst.q k) := by
    funext k; fin_cases k <;> exact SoInst.J_eq _ _ _ _ _ rfl rfl
  rw [hv]
  exact SoR.so_main (by decide) (by decide) (by decide) (by decide)


