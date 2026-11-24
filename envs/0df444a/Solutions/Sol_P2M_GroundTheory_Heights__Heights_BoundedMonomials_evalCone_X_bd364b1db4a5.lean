-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_evalCone_X_bd364b1db4a5
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T00:52:17.243729+00:00
-- url     : https://prove2.me/submissions/f643de76-7493-466d-a35b-3ed4e80d220c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [Fintype ι] [DecidableEq ι]


theorem solution {F : Type*} [CommRing F] (z : Cone n F) (k : ι) (i : Fin (n k + 1)) :
    evalCone z (X ⟨k, i⟩) = z k i := by
  simp [evalCone]
