-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P15.sl3_rank_cartan
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-22T00:54:12.893848+00:00
-- url     : https://prove2.me/submissions/09869fc8-464e-4320-a195-a35f82ad04c2

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

namespace Sl3H
open Module

abbrev M3 := Matrix (Fin 3) (Fin 3) ℝ

noncomputable def D1 : M3 := ((Matrix.single 1 1 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)) - ((Matrix.single 2 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))
noncomputable def D2 : M3 := ((Matrix.single 1 1 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)) - ((Matrix.single 3 3 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))

lemma hD1 : D1 = Matrix.diagonal ![1, -1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D1, Matrix.submatrix_apply, Matrix.single_apply]
lemma hD2 : D2 = Matrix.diagonal ![1, 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [D2, Matrix.submatrix_apply, Matrix.single_apply]

lemma mem_sl (y : M3) : y ∈ LieAlgebra.SpecialLinear.sl (Fin 3) ℝ ↔ y.trace = 0 := by
  show y ∈ LinearMap.ker (Matrix.traceLinearMap (Fin 3) ℝ ℝ) ↔ _
  rw [LinearMap.mem_ker, Matrix.traceLinearMap_apply]

lemma finrank_sl (t : ℕ) (ht : 0 < t) :
    Module.finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin t) ℝ).toSubmodule = t^2 - 1 := by
  have hk : (LieAlgebra.SpecialLinear.sl (Fin t) ℝ).toSubmodule =
      LinearMap.ker (Matrix.traceLinearMap (Fin t) ℝ ℝ) := rfl
  rw [hk]
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.traceLinearMap (Fin t) ℝ ℝ)
  have hr : LinearMap.range (Matrix.traceLinearMap (Fin t) ℝ ℝ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Matrix.single ⟨0, ht⟩ ⟨0, ht⟩ c, by simp [Matrix.traceLinearMap_apply]⟩
  rw [hr, finrank_top, Module.finrank_matrix, Fintype.card_fin] at h
  simp only [Module.finrank_self, mul_one] at h
  rw [sq]; omega

lemma fr : finrank ℝ (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ) = 8 := finrank_sl 3 (by norm_num)

noncomputable def x0 : LieAlgebra.SpecialLinear.sl (Fin 3) ℝ :=
  ⟨Matrix.diagonal ![4, -1, -3], by rw [mem_sl]; simp [Matrix.trace, Fin.sum_univ_three]; norm_num⟩

lemma main : LieAlgebra.rank ℝ (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ) = 2 ∧
    ∃ H : LieSubalgebra ℝ (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ), H.IsCartanSubalgebra ∧
      LinearIndependent ℝ ![D1, D2] ∧
      Submodule.span ℝ (Set.range ![D1, D2]) =
        H.toSubmodule.map (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ).toSubmodule.subtype := by
  apply RkFW.finish _ ![D1, D2] _ x0
  · intro i; fin_cases i <;> simp [hD1, hD2, mem_sl, Matrix.trace, Fin.sum_univ_three]
  · intro i
    fin_cases i <;> simp [x0, hD1, hD2, Ring.lie_def, Matrix.diagonal_mul_diagonal, mul_comm]
  · rw [LinearIndependent.pair_iff]
    intro s u h
    have h1 := congrFun (congrFun h 1) 1
    have h2 := congrFun (congrFun h 2) 2
    simp [hD1, hD2] at h1 h2
    exact ⟨h1, h2⟩
  · intro y hy hb
    rw [mem_sl] at hy
    simp only [Matrix.trace, Fin.sum_univ_three, Matrix.diag_apply] at hy
    have hS : Set.range ![D1, D2] = {D1, D2} := by
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty]; rfl
    rw [hS, Submodule.mem_span_pair] at hb ⊢
    obtain ⟨s, u, h⟩ := hb
    have e : ∀ i j, (s • D1 + u • D2) i j = ⁅(x0 : M3), y⁆ i j := fun i j => by rw [h]
    simp only [x0, hD1, hD2, Ring.lie_def, Matrix.sub_apply, Matrix.diagonal_mul,
      Matrix.mul_diagonal, Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply] at e
    have e01 := e 0 1; have e02 := e 0 2; have e10 := e 1 0
    have e12 := e 1 2; have e20 := e 2 0; have e21 := e 2 1
    simp at e01 e02 e10 e12 e20 e21
    refine ⟨-y 1 1, -y 2 2, ?_⟩
    rw [hD1, hD2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> linarith
  · exact RkFW.parity _ (fun y hy => by rw [mem_sl] at hy ⊢; rwa [Matrix.trace_transpose])
      (by rw [fr]; decide) (by rw [fr]; norm_num)

end Sl3H

/-- sl(3) has rank 2 and Cartan basis [b7,b8].
Source: PDF p. 11. The displayed input and matrices use b7; the preceding prose
says b8. We follow the input/output formulas, without correcting the general routine. -/
theorem solution :
    LieAlgebra.rank ℝ (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ) = 2 ∧
    isCartanBasisFor (LieAlgebra.SpecialLinear.sl (Fin 3) ℝ)
      ![((Matrix.single 1 1 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)) - ((Matrix.single 2 2 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)),
        ((Matrix.single 1 1 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1)) - ((Matrix.single 3 3 (1 : ℝ)).submatrix
      (fun i : Fin 3 => i.val + 1) (fun j : Fin 3 => j.val + 1))] := by
  exact Sl3H.main


