-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockBridge_funHom_mkF_e1a919750cdc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:03:11.5458+00:00
-- url     : https://prove2.me/submissions/d35d801a-68fd-41ca-a26a-8b1bccfe3a36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PAddHeightsridge

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.AddBlockBridge
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
set_option linter.unusedSectionVars false
variable (P : ArithVariety n) (y : Coord n → Ω) (hP : P.ideal = Geo.mCoordIdeal (ι := blockIdx n) y)
namespace GroundTheory.Heights₂.Heights.AddBlockBridge
theorem _root_.solution (f : MvPolynomial (Coord n) ℤ) : funHom P y hP (P.mkF f) = coneHom y f := by
  simp only [funHom, ArithVariety.mkF, RingHom.comp_apply, IsFractionRing.lift_algebraMap, coordHom,
    Ideal.Quotient.lift_mk]
end GroundTheory.Heights₂.Heights.AddBlockBridge
