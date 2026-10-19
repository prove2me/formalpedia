-- Prove2me | solution 1 for SoficGroups.KunLiteralSourceSelectedComponents.sourceConjugacyDisagreementBad_density_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/6ce54168-82c4-4dbe-9f13-3eee5157fdbb

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCompressionTransportCrossing_tendsto_action_conjugate

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunLiteralSourceSelectedComponents
open Filter Topology
open scoped BigOperators Pointwise
namespace SoficGroups.KunLiteralSourceSelectedComponents
theorem _root_.solution
    {G : Type*} [Group G]
    (A : SoficGroups.SoficApproximation G)
    (u g : G) :
    Tendsto
      (fun n =>
        ((sourceConjugacyDisagreementBad A u g n).card : ℝ) /
          (A.model n).size)
      atTop (nhds 0) := by
  classical
  simpa [sourceConjugacyDisagreementBad,
    SoficGroups.normalizedHamming, hammingDist] using
    SoficGroups.SourceCompressionTransportCrossing.tendsto_action_conjugate
      A u g
end SoficGroups.KunLiteralSourceSelectedComponents
