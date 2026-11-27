-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ArithVariety_whole_isHomogGenerators_abdd91caeef4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:54:45.377746+00:00
-- url     : https://prove2.me/submissions/e81b9c13-0d9a-40c0-8440-af819f1abb18

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples

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
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
open GroundTheory.Heights₂.Heights.ArithVariety
variable (n : ι → ℕ)
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution :
    (whole n).IsHomogGenerators (fun i : Fin 0 ↦ i.elim0) (fun i : Fin 0 ↦ i.elim0) where
  homog i := i.elim0
  span_eq := by
    rw [Set.range_eq_empty, Ideal.span_empty]
    rfl
end GroundTheory.Heights₂.Heights.ArithVariety
