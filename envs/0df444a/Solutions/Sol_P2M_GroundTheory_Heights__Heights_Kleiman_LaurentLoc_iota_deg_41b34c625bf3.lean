-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_deg_41b34c625bf3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:51.106644+00:00
-- url     : https://prove2.me/submissions/b4322eb4-ca02-43ac-a87c-2752a93e9a7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsSerrePoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSerrePolyLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_iota_gen_mem_9183a2006dec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LaurentLoc_single_mem_map_fd3a6c454df1

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
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
variable {S : Type u} [CommRing S] {N : ℕ}
attribute [local instance] algP
namespace GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
theorem _root_.solution (c : ℤ) (I : StdCell N) :
    (degLoc (polyGraded S N) c I).map (iota I) = laurentDeg S N c I := by
  apply le_antisymm
  · rw [degLoc, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨z, ⟨m, s, a, e, hm, hs, hc, rfl⟩, rfl⟩
    exact iota_gen_mem c I m s a e hm hs hc
  · rw [laurentDeg, Finsupp.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact single_mem_map c I x hx
end GroundTheory.Heights₂.Heights.Kleiman.LaurentLoc
