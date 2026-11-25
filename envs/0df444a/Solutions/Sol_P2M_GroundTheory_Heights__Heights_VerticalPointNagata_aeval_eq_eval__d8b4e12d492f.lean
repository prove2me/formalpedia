-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_VerticalPointNagata_aeval_eq_eval__d8b4e12d492f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:42.94698+00:00
-- url     : https://prove2.me/submissions/ffecd8d0-4703-43e6-816e-a214d8f6c738

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointNagata
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointMultChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PVertPointNagata

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.VerticalPointNagata
variable {T : Type} [Fintype T]
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.VerticalPointNagata
theorem _root_.solution {S : Type*} [CommRing S] [Algebra ℤ S] (v : (Σ _ : Unit, T) → S)
    (f : MRing (fun _ : Unit => T)) : aeval v f = eval₂ (Int.castRingHom S) v f := by
  rw [aeval_def, show algebraMap ℤ S = Int.castRingHom S from RingHom.ext_int _ _]
end GroundTheory.Heights₂.Heights.VerticalPointNagata
