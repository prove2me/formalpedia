-- Prove2me | solution 1 for ReciprocityTheory.PGsh.lowRed_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:39:26.141612+00:00
-- url     : https://prove2.me/submissions/ce77d895-f547-4d05-9699-31164aab59d0

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
theorem _root_.solution {m : ℕ} {F G : MvPolynomial (Fin d) R} (hF : LowRed p m F)
    (hG : constantCoeff G = 0) (β : Fin d →₀ ℕ) (hβ : ∀ j, β j < p) (hdeg : β.degree ≤ m) :
    coeff β (F * G) = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun y hy => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
  by_cases h2 : y.2 = 0
  · rw [h2, ← congrFun constantCoeff_eq G, hG, mul_zero]
  · have hle : ∀ j, y.1 j ≤ β j := fun j => by rw [← hy]; simp
    have h2' : y.2.degree ≠ 0 := fun h => h2 ((Finsupp.degree_eq_zero_iff _).1 h)
    have hdeg1 : y.1.degree < β.degree := by
      rw [← hy, map_add]; omega
    rw [hF y.1 (fun j => lt_of_le_of_lt (hle j) (hβ j)) (by omega), zero_mul]
end ReciprocityTheory.PGsh
