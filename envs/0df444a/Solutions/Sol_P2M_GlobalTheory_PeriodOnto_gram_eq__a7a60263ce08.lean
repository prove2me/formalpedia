-- Prove2me | solution 1 for P2M_GlobalTheory_PeriodOnto_gram_eq__a7a60263ce08
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:31:15.693652+00:00
-- url     : https://prove2.me/submissions/b541d3b5-343c-4e97-a4b7-df1b334b329a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.PeriodOnto
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]
namespace GlobalTheory.PeriodOnto
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G x = xᵀ * G.map τ * x.map conj := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, of_apply, Matrix.mul_apply, transpose_apply, map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm
end GlobalTheory.PeriodOnto
