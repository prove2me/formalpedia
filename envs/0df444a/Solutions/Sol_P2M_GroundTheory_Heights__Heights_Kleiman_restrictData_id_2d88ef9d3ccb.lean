-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_restrictData_id_2d88ef9d3ccb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:03:35.701082+00:00
-- url     : https://prove2.me/submissions/5b12defa-52c4-4b91-b061-06da800fd01b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_AlgebraMapMemChartRingLine

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
theorem _root_.solution (Q : SubSystem S x Ω) :
    RestrictData (K' := Ω) Q (y := x) (fun _ h => h) Q id where
  mem _ _ hq := hq
  add _ _ _ _ _ := rfl
  smul _ _ _ _ _ _ _ _ _ := rfl
  span I := by rw [Set.image_id]; exact Submodule.span_eq _
end GroundTheory.Heights₂.Heights.Kleiman
