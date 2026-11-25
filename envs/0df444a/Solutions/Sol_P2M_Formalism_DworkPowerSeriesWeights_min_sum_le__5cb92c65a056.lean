-- Prove2me | solution 1 for P2M_Formalism_DworkPowerSeriesWeights_min_sum_le__5cb92c65a056
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:08.975855+00:00
-- url     : https://prove2.me/submissions/1f443fc6-b8f5-4e44-b58a-7a61a0948e3d

import Definitions.Def_Formalism_GaussJetBounds_StatementN
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_MfactEqProdUniv
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FirstRowMinorDegreeLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {σ : Type} [Fintype σ] (Pr : σ → Prop) [DecidablePred Pr] (u u' : σ →₀ ℕ) :
    (∑ y, min (u y) (u' y)) + ∑ y ∈ Finset.univ.filter Pr, u y ≤
      (∑ y ∈ Finset.univ.filter Pr, u' y) + ∑ y, u y := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ Pr (fun y => min (u y) (u' y)),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ Pr (fun y => u y)]
  have h1 : (∑ y ∈ Finset.univ.filter Pr, min (u y) (u' y)) ≤ ∑ y ∈ Finset.univ.filter Pr, u' y :=
    Finset.sum_le_sum fun _ _ => min_le_right _ _
  have h2 : (∑ y ∈ Finset.univ.filter (fun y => ¬ Pr y), min (u y) (u' y)) ≤
      ∑ y ∈ Finset.univ.filter (fun y => ¬ Pr y), u y :=
    Finset.sum_le_sum fun _ _ => min_le_left _ _
  linarith
end Formalism.DworkPowerSeriesWeights
