-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.equatorial_measurement_as_projected_teleportation
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:21:53.592638+00:00
-- url     : https://prove2.me/submissions/493648c0-64a9-405e-ab66-91e2c5ac2f1e

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
set_option maxHeartbeats 1500000

set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Projected teleportation, PDF pp.17–18: all four kets and their even/odd
placement, and the exact pullback of the two normalized equatorial effects.
Odd alternatives vanish upon projection; this is a conditional identity, not
a deterministic postselection procedure for an arbitrary teleportation. -/
theorem solution (theta : ℝ) :
    (∀ a : Fin 4, cutDownKet theta a = cutDownFormula theta a) ∧
    Orthonormal ℂ (cutDownKet theta) ∧
    (∀ p : QubitPair, p.1 ≠ p.2 → cutDownKet theta 0 p = 0 ∧ cutDownKet theta 1 p = 0) ∧
    (∀ p : QubitPair, p.1 = p.2 → cutDownKet theta 2 p = 0 ∧ cutDownKet theta 3 p = 0) ∧
    (∀ s : Bool, fuseᴴ * pureDensity (equatorial theta s) * fuse =
      pureDensity (cutDownKet theta (if s then 1 else 0))) ∧
    fuse * pureDensity (cutDownKet theta 2) * fuseᴴ = 0 ∧
    fuse * pureDensity (cutDownKet theta 3) * fuseᴴ = 0 := by
  have hc : ∀ a : Fin 4, cutDownKet theta a = cutDownFormula theta a := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    intro a
    ext ⟨b,c⟩
    fin_cases a <;> cases b <;> cases c <;>
      norm_num [cutDownKet, cutDownFormula, act, bellPauliRepresentative, wGate,
        phaseGate, hadamard, pauliX, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Matrix.mulVec, dotProduct, Matrix.kronecker, Fintype.sum_prod_type, Fintype.sum_bool,
        hBond_apply, czPhase, ← Complex.exp_conj, Complex.ofReal_inv,
        ← pow_two, inv_pow, h2] <;> ring
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have he : Complex.exp (Complex.I * theta) * Complex.exp (-(Complex.I * theta)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  refine ⟨hc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro a b
    simp only [hc, PiLp.inner_apply, Fintype.sum_prod_type, RCLike.inner_apply]
    fin_cases a <;> fin_cases b <;>
      norm_num [cutDownFormula, Fintype.sum_bool, ← Complex.exp_conj, ← Complex.exp_add,
        Complex.ofReal_inv, ← pow_two, inv_pow, h2] <;> ring_nf <;>
        norm_num [inv_pow, h2, mul_assoc, he]
  · rintro ⟨a,b⟩ h
    cases a <;> cases b <;> simp_all [hc, cutDownFormula]
  · rintro ⟨a,b⟩ h
    cases a <;> cases b <;> simp_all [hc, cutDownFormula]
  · intro s
    ext ⟨a,b⟩ ⟨c,d⟩
    cases s <;> cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [hc, pureDensity, equatorial, fuse, cutDownFormula, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_bool, Matrix.kronecker] <;> ring
  · ext a b
    cases a <;> cases b <;>
      norm_num [hc, pureDensity, fuse, cutDownFormula, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  · ext a b
    cases a <;> cases b <;>
      norm_num [hc, pureDensity, fuse, cutDownFormula, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type, Fintype.sum_bool]