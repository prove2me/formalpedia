-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_pullSys_self_aa64784590c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:33:46.326451+00:00
-- url     : https://prove2.me/submissions/02ae219d-267f-4850-8034-21db9dae6e7d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_span_range_eq_twistMod_one_cf9eb67143e0


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
theorem _root_.solution : pullSys (S := S) x x = twistSys S x 1 :=
  SubSystem.ext_sub fun I => span_range_eq_twistMod_one I
end GroundTheory.Heights₂.Heights.Kleiman
