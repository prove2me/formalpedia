-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_CellDSq_rem_rem_comm_6b3e204c1d90
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:21.674934+00:00
-- url     : https://prove2.me/submissions/df711342-b766-4003-b20f-6e49485d1a83

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
theorem _root_.solution (I : ∀ k, Finset (ι k)) (p q : Σ k, ι k) :
    rem (rem I p) q = rem (rem I q) p := by
  obtain ⟨k, i⟩ := p
  obtain ⟨k', i'⟩ := q
  by_cases hk : k' = k
  · subst hk
    simp only [rem, Function.update_self, Function.update_idem, Finset.erase_right_comm]
  · simp only [rem]
    rw [Function.update_of_ne hk, Function.update_of_ne (Ne.symm hk),
      Function.update_comm (Ne.symm hk)]
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.CellDSq
