-- Prove2me | solution 1 for P2M_GlobalTheory_SW_HAct_det_den__4c81421ae817
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:35.889438+00:00
-- url     : https://prove2.me/submissions/58f2220b-7564-4a01-9fb4-86083e6b55c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {N : ℕ} {A B C D Z : Matrix (Fin N) (Fin N) ℂ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution (h1 : Aᴴ * C = Cᴴ * A) (h2 : Aᴴ * D = Cᴴ * B + 1) (h3 : Dᴴ * A = Bᴴ * C + 1)
    (h4 : Bᴴ * D = Dᴴ * B) (hQ : (C * Z + D).det ≠ 0) :
    (Z * Cᴴ + Dᴴ).det * (fromBlocks A B C D).det = (C * Z + D).det := by
  have hd := den'_act h1 h2 h3 h4 hQ
  set W := (A * Z + B) * (C * Z + D)⁻¹ with hW
  have e1 : W * (C * Z + D) = A * Z + B := by
    rw [hW, Matrix.mul_assoc, nonsing_inv_mul _ (Ne.isUnit hQ), Matrix.mul_one]
  have e2 : (Z * Cᴴ + Dᴴ) * (A - W * C) = 1 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, hd]
    have e : (Z * Cᴴ + Dᴴ) * A - (Z * Aᴴ + Bᴴ) * C =
      Z * (Cᴴ * A) + Dᴴ * A - (Z * (Aᴴ * C) + Bᴴ * C) := by noncomm_ring
    rw [e, h1, h3]
    noncomm_ring
  have e3 : fromBlocks A B C D * fromBlocks 1 Z 0 1 =
      fromBlocks 1 W 0 1 * fromBlocks (A - W * C) 0 C (C * Z + D) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp [e1]
  have e4 := congrArg det e3
  rw [det_mul, det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at e4
  simp only [det_one, mul_one, one_mul] at e4
  rw [e4, ← mul_assoc, ← det_mul, e2, det_one, one_mul]
end GlobalTheory.SW.HAct
