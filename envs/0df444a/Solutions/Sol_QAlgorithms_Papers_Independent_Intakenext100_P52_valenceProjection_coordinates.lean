-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.valenceProjection_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:14:52.212854+00:00
-- url     : https://prove2.me/submissions/7698b74a-9cc9-406d-b97a-e13cee33189d

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
noncomputable section
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 QAlgorithms.Papers.Independent.Information100.P21 QAlgorithms.Papers.Independent.Gap20.P01
open scoped Matrix ComplexConjugate
private theorem hBond_apply (a b : Bool) : hBond (a,b) = (1 / 2 : ℂ) * czPhase a b := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  cases a <;> cases b <;>
    norm_num [hBond, czPhase, act, tensorVec, hadamard, ket, controlled, pauliZ,
      Matrix.mulVec, dotProduct, Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      Complex.ofReal_inv, ← pow_two, inv_pow, h2]
private theorem valenceProjection_apply {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (x : V → Bool) (w : (EdgeLabel E × Bool) → Bool) :
    valenceProjection E x w =
      if w = (fun p => if p.2 then x p.1.val.2 else x p.1.val.1) then 1 else 0 := by
  unfold valenceProjection
  congr 1
  apply propext
  constructor
  · intro h
    funext p
    rcases p with ⟨e,b⟩
    cases b
    · exact (h e).1
    · exact (h e).2
  · intro h e
    subst w
    simp

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) (x : V → Bool) :
    applyRect (valenceProjection E) (bondGrid E) x = (1 / 2 : ℂ)^E.card * edgePhase E x := by
  simp only [applyRect, PiLp.toLp_apply, Matrix.mulVec, dotProduct, valenceProjection_apply]
  rw [Finset.sum_eq_single (fun p : EdgeLabel E × Bool =>
    if p.2 then x p.1.val.2 else x p.1.val.1)]
  · simp only [ite_true, mul_one, one_mul, bondGrid, PiLp.toLp_apply, hBond_apply]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    congr 1
    simpa [edgePhase] using (Finset.prod_coe_sort E (fun e => czPhase (x e.1) (x e.2)))
  · intro w hw hne
    simp [hne]
  · intro hn
    exact (hn (Finset.mem_univ _)).elim