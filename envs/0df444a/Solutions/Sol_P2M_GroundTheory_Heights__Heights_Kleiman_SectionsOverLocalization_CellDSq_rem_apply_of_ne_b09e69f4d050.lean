-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_apply_of_ne_b09e69f4d050
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:27.638739+00:00
-- url     : https://prove2.me/submissions/f2045ed2-4401-41b6-ad39-31b8738a4484

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
omit [Fintype K]
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
theorem _root_.solution {I : ∀ k, Finset (ι k)} {k l : K} (i : ι k) (h : l ≠ k) :
    rem I ⟨k, i⟩ l = I l :=
  Function.update_of_ne h _ _
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
