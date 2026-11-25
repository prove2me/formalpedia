-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_ext_of_empty_29cb4583223d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:18.054655+00:00
-- url     : https://prove2.me/submissions/f352c2ae-1644-4c4e-88ff-742b785d9a01

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
omit [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [LinearOrder K] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution {m : ℕ} (t : Cell K ι m → Ω) {J : ∀ k, Finset (ι k)} {k : K} (h : J k = ∅) :
    ext m t J = 0 := by
  unfold ext
  rw [dif_neg]
  rintro ⟨hc, -⟩
  simpa [h] using hc k
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
