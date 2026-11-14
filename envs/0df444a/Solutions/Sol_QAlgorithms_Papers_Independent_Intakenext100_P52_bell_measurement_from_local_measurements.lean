-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P52.bell_measurement_from_local_measurements
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T04:42:44.769734+00:00
-- url     : https://prove2.me/submissions/d1979e8c-4d1e-4726-834c-378bba1b1f63

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P52
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_one_qubit_gate_teleportation
import Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P52_cxWires_shared_target_commute
noncomputable section
open scoped Matrix ComplexConjugate
open QAlgorithms QAlgorithms.Papers.Independent.Intakenext100.P52 QAlgorithms.Papers.Independent.Information100.P21
set_option autoImplicit false
set_option maxHeartbeats 1500000
private theorem cxWires_act {V : Type*} [Fintype V] [DecidableEq V]
    (a t : V) (ha : a ≠ t) (psi : Vec (V → Bool)) (y : V → Bool) :
    act (cxWires a t) psi y = psi (Function.update y t (xor (y t) (y a))) := by
  have hInv (z : V → Bool) :
      Function.update (Function.update z t (xor (z t) (z a))) t
        (xor ((Function.update z t (xor (z t) (z a))) t)
          ((Function.update z t (xor (z t) (z a))) a)) = z := by
    funext i
    by_cases hi : i = t
    · subst i
      simp [Function.update_self, Function.update_of_ne ha]
    · simp [Function.update_of_ne hi]
  have hh (z : V → Bool) : (y = Function.update z t (xor (z t) (z a))) ↔
      z = Function.update y t (xor (y t) (y a)) := by
    constructor
    · intro h
      rw [h, hInv]
    · intro h
      rw [h, hInv]
  simp only [act, PiLp.toLp_apply, Matrix.mulVec, dotProduct, cxWires, hh,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
private theorem act_mul {I : Type*} [Fintype I] (A B : Matrix I I ℂ) (x : Vec I) :
    act (A * B) x = act A (act B x) := by
  exact congrArg (WithLp.toLp 2) (Matrix.mulVec_mulVec x.ofLp A B).symm


set_option autoImplicit false

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Intakenext100.P52
noncomputable section

open scoped Matrix ComplexConjugate



open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap20.P01 (applyRect)

/-- Bell measurement decomposition, PDF pp.15–16. Printed CX B_ij label map
is interchanged; changed to CX B_cd=|(-1)^c> |d>, consistent with p.2.
The bra identity holds with any reference, hence gives the full destructive
measurement instrument. Fig.12's two CXs share a target and commute. -/
theorem solution :
    (∀ c d : Bool, act cnot (sourceBellBasis c d) =
      tensorVec (equatorial 0 c) (ket d)) ∧
    (∀ (R : Type) [Fintype R] [DecidableEq R] (psi : Vec (QubitPair × R)) (c d : Bool),
      pairBra (sourceBellBasis c d) psi = localBellAnalysis c d psi) ∧
    cxWires (0 : Fin 3) 1 * cxWires (2 : Fin 3) 1 =
      cxWires (2 : Fin 3) 1 * cxWires (0 : Fin 3) 1 ∧
    (∀ (psi : Vec Bool), IsState psi → ∀ c d : Bool,
      figure12Branch c d psi =
        teleportContraction psi (finiteMaxEntangled Bool) (sourceBellBasis c d) ∧
      figure12Branch c d psi = (1 / 2 : ℂ) • act (pauliByproduct d c) psi ∧
      ‖figure12Branch c d psi‖ ^ 2 = (1 / 4 : ℝ)) := by
  have hbell : ∀ c d : Bool, act cnot (sourceBellBasis c d) =
      tensorVec (equatorial 0 c) (ket d) := by
    intro c d
    ext ⟨a,b⟩
    cases c <;> cases d <;> cases a <;> cases b <;>
      norm_num [act, cnot, sourceBellBasis, finiteMaxEntangled, tensorVec,
        equatorial, ket, pauliX, pauliZ, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Matrix.kronecker, Matrix.one_apply, Fintype.sum_prod_type,
        Fintype.sum_bool]
  have hbra (R : Type) [Fintype R] [DecidableEq R] (psi : Vec (QubitPair × R))
      (c d : Bool) : pairBra (sourceBellBasis c d) psi = localBellAnalysis c d psi := by
    ext r
    cases c <;> cases d <;>
      norm_num [pairBra, sourceBellBasis, localBellAnalysis, act, cnot,
        finiteMaxEntangled, tensorVec, equatorial, ket, pauliX, pauliZ,
        Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.kronecker,
        Matrix.one_apply, Fintype.sum_prod_type, Fintype.sum_bool,
        Complex.ofReal_inv] <;> norm_num [Complex.conj_ofNat] <;> ring
  have hfig (c d : Bool) (psi : Vec Bool) : figure12Branch c d psi =
      (1/2 : ℂ) • act (pauliByproduct d c) psi := by
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
    ext b
    simp only [figure12Branch, act_mul, PiLp.toLp_apply]
    simp_rw [cxWires_act (0 : Fin 3) 1 (by decide), cxWires_act (2 : Fin 3) 1 (by decide)]
    cases c <;> cases d <;> cases b <;>
      norm_num [figure12Input, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.update_apply, equatorial, act, pauliByproduct,
        pauliX, pauliZ, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_bool,
        Complex.ofReal_inv, ← pow_two, inv_pow, h2] <;>
        norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.update_apply,
          show (2 : Fin 3) ≠ 1 by decide, show (0 : Fin 3) ≠ 1 by decide,
          Complex.ofReal_inv, ← pow_two, inv_pow, h2] <;>
        simp [Function.update, inv_pow, h2] <;> ring_nf <;> norm_num [inv_pow,h2] <;> ring
  have hk : Matrix.kronecker (1 : Matrix Bool Bool ℂ) 1 = (1 : Matrix QubitPair QubitPair ℂ) := by
    ext ⟨a,b⟩ ⟨c,d⟩
    by_cases ha : a = c <;> by_cases hb : b = d <;>
      simp [Matrix.kronecker, Matrix.one_apply, ha,hb]
  have hrot (c d : Bool) : rotatedBell (1 : Matrix Bool Bool ℂ) c d = sourceBellBasis c d := by
    simp [rotatedBell, hk, act]
  refine ⟨hbell, hbra, cxWires_shared_target_commute (0 : Fin 3) 2 1 (by decide) (by decide), ?_⟩
  intro psi hpsi c d
  have hi := (one_qubit_gate_teleportation (1 : Matrix Bool Bool ℂ)
    (Matrix.unitaryGroup Bool ℂ).one_mem).2 psi hpsi c d
  dsimp only at hi
  simp only [hrot, Matrix.mul_one] at hi
  have heq : figure12Branch c d psi =
      teleportContraction psi (finiteMaxEntangled Bool) (sourceBellBasis c d) :=
    (hfig c d psi).trans hi.1.symm
  refine ⟨heq, hfig c d psi, ?_⟩
  rw [heq]
  exact hi.2.1