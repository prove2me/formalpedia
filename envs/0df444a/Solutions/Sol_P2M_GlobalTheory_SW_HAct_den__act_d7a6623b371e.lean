-- Prove2me | solution 1 for P2M_GlobalTheory_SW_HAct_den__act_d7a6623b371e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:04.996675+00:00
-- url     : https://prove2.me/submissions/b259bc7e-02a5-405e-af13-f10dd51f7b9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Theorems.Thm_GlobalTheory_SW_HAct_skew

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
    (Z * Cᴴ + Dᴴ) * ((A * Z + B) * (C * Z + D)⁻¹) = Z * Aᴴ + Bᴴ := by
  have h := skew h1 h2 h3 h4 Z Z
  rw [sub_self, sub_eq_zero] at h
  rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, mul_nonsing_inv _ (Ne.isUnit hQ), Matrix.mul_one]
end GlobalTheory.SW.HAct
