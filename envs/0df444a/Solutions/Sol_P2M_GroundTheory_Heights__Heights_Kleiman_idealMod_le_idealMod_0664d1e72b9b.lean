-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_idealMod_le_idealMod_0664d1e72b9b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:25:47.466935+00:00
-- url     : https://prove2.me/submissions/57de5499-b302-4419-a82e-ef09b54cbecd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreRestrKer

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
open scoped Pointwise nonZeroDivisors
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    idealMod (x := x) J I ≤ idealMod (x := x) J' I := by
  refine Submodule.span_mono ?_
  rintro _ ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
  exact ⟨f, s, e, h hf, hs, hfe, hse, rfl⟩
end GroundTheory.Heights₂.Heights.Kleiman
