-- Prove2me | solution 1 for P2M_GlobalTheory_Square_TwoStep_normAlg_coords__aac41224ad99
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:02.515369+00:00
-- url     : https://prove2.me/submissions/9114abda-5ebe-4a81-963a-508fbfd5a147

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
open GlobalTheory.Square.TwoStep
namespace GlobalTheory.Square.TwoStep
theorem _root_.solution (t : ℕ) : normAlg (square K).G (coords K t).gam (coords K t).z' = 1 := by
  show (∑ _x : Fin 2, ((2 : ℕ) : K)⁻¹ * ∑ _k : Unit, ∑ _l : Unit, (1 : K) * star (1 : K) * 1) = _
  simp
end GlobalTheory.Square.TwoStep
