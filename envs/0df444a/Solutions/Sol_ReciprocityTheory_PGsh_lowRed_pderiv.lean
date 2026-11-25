-- Prove2me | solution 1 for ReciprocityTheory.PGsh.lowRed_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:39:27.433949+00:00
-- url     : https://prove2.me/submissions/69f35ee8-641c-4fdd-b5e2-0bd21e073f32

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_RidConvolutionDerivation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial TensorProduct
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R : Type*} [CommRing R] {d p : ℕ}
namespace ReciprocityTheory.PGsh
theorem _root_.solution {m : ℕ} (hp0 : (p : R) = 0) {P : MvPolynomial (Fin d) R}
    (hP : LowRed p (m + 1) P) (j : Fin d) : LowRed p m (pderiv j P) := by
  classical
  intro γ hγ hdeg
  rw [coeff_pderiv]
  by_cases hlt : γ j + 1 < p
  · rw [hP, zero_mul]
    · intro i
      by_cases hij : i = j
      · subst hij; simpa using hlt
      · simpa [Finsupp.single_apply, Ne.symm hij] using hγ i
    · rw [map_add, Finsupp.degree_single]; omega
  · have h : γ j + 1 = p := by have := hγ j; omega
    have hc : ((γ j : R) + 1) = 0 := by
      have : ((γ j + 1 : ℕ) : R) = 0 := by rw [h, hp0]
      exact_mod_cast this
    rw [hc, mul_zero]
end ReciprocityTheory.PGsh
