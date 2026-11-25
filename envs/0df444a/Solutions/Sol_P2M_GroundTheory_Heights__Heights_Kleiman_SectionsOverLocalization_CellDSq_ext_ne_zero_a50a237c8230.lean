-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_ne_zero_a50a237c8230
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:14.47644+00:00
-- url     : https://prove2.me/submissions/3e357a82-9652-4b84-bc72-f5df51374ea9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsBisFurther
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DoubleSumEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
variable {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, LinearOrder (ι k)]
variable (S : Type) [CommRing S] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω]
omit [LinearOrder K] [∀ k, LinearOrder (ι k)] [∀ k, Fintype (ι k)] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution {m : ℕ} (t : Cell K ι m → Ω) (J : ∀ k, Finset (ι k)) (h : ext m t J ≠ 0) :
    ∀ l, (J l).Nonempty := by
  unfold ext at h
  split_ifs at h with hc
  · exact hc.1
  · exact absurd rfl h
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
