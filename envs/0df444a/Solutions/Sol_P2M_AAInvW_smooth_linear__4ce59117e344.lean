-- Prove2me | solution 1 for P2M_AAInvW_smooth_linear__4ce59117e344
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:54:10.717459+00:00
-- url     : https://prove2.me/submissions/dffacec7-21c9-46a9-b24d-a15b764ba7fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace AAInvW
theorem _root_.solution : SmoothLin := by
  unfold SmoothLin
  intro n H E _ _ f f' c hf hf'
  unfold SmoothOnH at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩, ?_, ?_⟩
  · exact (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)
  · intro g hg hgH
    simp only [hfF g hg.1 hgH, hfF' g hg.2 hgH]
end AAInvW
