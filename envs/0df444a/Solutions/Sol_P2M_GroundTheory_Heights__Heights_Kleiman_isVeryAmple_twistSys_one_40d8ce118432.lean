-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_twistSys_one_40d8ce118432
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:33:37.250639+00:00
-- url     : https://prove2.me/submissions/1ea96ce9-c12e-457a-abd8-879752931019

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmpleBy_twistSys_one_0b95c573b325

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u v w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution : IsVeryAmple (twistSys S x 1) := ⟨N, x, isVeryAmpleBy_twistSys_one⟩
end GroundTheory.Heights₂.Heights.Kleiman
