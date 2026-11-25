-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncidenceGeneric_aeval_genSubst_genSubst_5af28047283e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:55:58.539581+00:00
-- url     : https://prove2.me/submissions/d0d5a415-e24f-4232-a9a3-e02c207ce58b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceGeneric
namespace GroundTheory.Heights₂.Heights.IncidenceGeneric
theorem _root_.solution {R : Type*} [CommRing R] {n k : ℕ} (ζ c c' : Fin n → R)
    (hc : ∑ l, c l * ζ l = 1) (ij : Fin k × Fin n) :
    aeval (genSubst ζ c) (genSubst ζ c' ij) = genSubst ζ c ij := by
  have hC : ∑ l, C (c l) * C (ζ l) = (1 : MvPolynomial (Fin k × Fin n) R) := by
    rw [← C_1, ← hc, map_sum]
    simp only [C_mul]
  have h0 : ∑ l, genSubst ζ c (ij.1, l) * C (ζ l) = 0 := by
    simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one,
      sub_self]
  rw [show genSubst ζ c' ij = X ij - (∑ l, X (ij.1, l) * C (ζ l)) * C (c' ij.2) from rfl]
  simp only [map_sub, map_mul, map_sum, aeval_X, aeval_C, algebraMap_eq, h0, zero_mul, sub_zero]
end GroundTheory.Heights₂.Heights.IncidenceGeneric
