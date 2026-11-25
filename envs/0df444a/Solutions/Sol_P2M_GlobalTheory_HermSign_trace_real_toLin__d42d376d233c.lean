-- Prove2me | solution 1 for P2M_GlobalTheory_HermSign_trace_real_toLin__d42d376d233c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:31:24.848346+00:00
-- url     : https://prove2.me/submissions/9ec26fb3-330d-4f4e-8531-951d9dc0138a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_MemIffConjugateNotMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors TensorProduct ComplexConjugate ComplexOrder MatrixOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermSign
namespace GlobalTheory.HermSign
theorem _root_.solution {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) :
    LinearMap.trace ℝ _ ((toLin' N).restrictScalars ℝ) = 2 * N.trace.re := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower (Pi.basisFun ℂ (Fin r)))]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_prod_type, two_mul,
    Finset.sum_add_distrib]
end GlobalTheory.HermSign
