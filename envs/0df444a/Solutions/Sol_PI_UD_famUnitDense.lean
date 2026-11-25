-- Prove2me | solution 1 for PI.UD.famUnitDense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:49:55.336484+00:00
-- url     : https://prove2.me/submissions/4d016e6d-cdb9-4196-b27a-ac2002f1f2fb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_EvalBindTorusSubst
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_VanishInvertible
import Theorems.Thm_PI_UD_vanish_invertible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI PI.UD
namespace PI.UD
theorem _root_.solution (hs : SVDStep) {ι : Type} [Fintype ι] {n : ℕ}
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hP : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ)ᴴ * y τ = 1) →
      eval (fun x : ι × Fin n × Fin n => y x.1 x.2.1 x.2.2) P = 0) : P = 0 := by
  classical
  let D : MvPolynomial (ι × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun i j : Fin n => (X (τ, i, j) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
  have hD : D ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun τ _ => ?_
    have e : (Matrix.of fun i j : Fin n => (X (τ, i, j) : MvPolynomial (ι × Fin n × Fin n) ℂ)) =
        (rename (fun p : Fin n × Fin n => (τ, p.1, p.2))).toRingHom.mapMatrix
          (mvPolynomialX (Fin n) (Fin n) ℂ) := by
      ext i j
      simp [mvPolynomialX]
    rw [e, ← RingHom.map_det]
    intro h0
    apply det_mvPolynomialX_ne_zero (Fin n) ℂ
    have hinj : Function.Injective (fun p : Fin n × Fin n => (τ, p.1, p.2)) := by
      intro a b h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2.1 h.2.2
    apply rename_injective _ hinj
    simpa using h0
  have hPD : P * D = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : ∀ τ, (Matrix.of fun i j : Fin n => x (τ, i, j)).det ≠ 0
    · have h1 := vanish_invertible hs P hP (fun τ => Matrix.of fun i j => x (τ, i, j)) hx
      simp only [Matrix.of_apply] at h1
      have e : (fun p : ι × Fin n × Fin n => x (p.1, p.2.1, p.2.2)) = x := rfl
      rw [e] at h1
      rw [h1, zero_mul]
    · push Not at hx
      obtain ⟨τ, hτ⟩ := hx
      have h3 : eval x D = 0 := by
        simp only [D, map_prod]
        apply Finset.prod_eq_zero (Finset.mem_univ τ)
        rw [RingHom.map_det]
        convert hτ using 2
        ext i j
        simp
      rw [h3, mul_zero]
  exact (mul_eq_zero.mp hPD).resolve_right hD
end PI.UD
