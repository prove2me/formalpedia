-- Prove2me | solution 1 for PI.LocCartanPair.lag_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:49:42.914659+00:00
-- url     : https://prove2.me/submissions/aad2cd51-3202-44e7-8b20-624c8824fedc

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PairBaseOfLag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocCartanPair
open Matrix IsLocalRing
variable {R : Type} [CommRing R] [StarRing R]
namespace PI.LocCartanPair
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (A B P e : Matrix ι ι R)
    (hP : IsUnit P.det) (hPAB : Pᴴ * A * P = B) (he : e * e = e)
    (heB : eᴴ * B = B * (1 - e)) :
    (P * e * P⁻¹) * (P * e * P⁻¹) = P * e * P⁻¹ ∧
      (P * e * P⁻¹)ᴴ * A = A * (1 - P * e * P⁻¹) := by
  have h1 : P⁻¹ * P = 1 := nonsing_inv_mul P hP
  have h2 : P * P⁻¹ = 1 := mul_nonsing_inv P hP
  have hPX : ∀ X : Matrix ι ι R, P⁻¹ * (P * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← conjTranspose_mul, h2, conjTranspose_one]
  have h4 : Pᴴ * (P⁻¹)ᴴ = 1 := by rw [← conjTranspose_mul, h1, conjTranspose_one]
  have hQX : ∀ X : Matrix ι ι R, Pᴴ * ((P⁻¹)ᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  have hA : A = (P⁻¹)ᴴ * B * P⁻¹ := by
    rw [← hPAB]
    simp only [Matrix.mul_assoc]
    rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  constructor
  · simp only [Matrix.mul_assoc, hPX]
    rw [← Matrix.mul_assoc e e, he]
  · calc (P * e * P⁻¹)ᴴ * A = (P⁻¹)ᴴ * (eᴴ * B) * P⁻¹ := by
          rw [hA]
          simp only [conjTranspose_mul, Matrix.mul_assoc, hQX]
      _ = (P⁻¹)ᴴ * (B * (1 - e)) * P⁻¹ := by rw [heB]
      _ = A * (1 - P * e * P⁻¹) := by
          rw [hA]
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc, hPX]
end PI.LocCartanPair
