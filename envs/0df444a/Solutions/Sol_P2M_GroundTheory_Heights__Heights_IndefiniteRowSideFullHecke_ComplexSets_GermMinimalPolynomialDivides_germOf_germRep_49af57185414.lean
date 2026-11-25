-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermMinimalPolynomialDivides_germOf_germRep_49af57185414
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:57.365485+00:00
-- url     : https://prove2.me/submissions/94acec55-619b-4549-a6d6-bb92ed5e3edf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermMinimalPolynomialDivides
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteFibreGermIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolGermsIntegrallyClosed
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermMinimalPolynomialDivides

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Polynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermMinimalPolynomialDivides
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermMinimalPolynomialDivides
theorem _root_.solution {ι : Type} [Fintype ι] (w : ι → ℂ) (φ : holGerms w) : germOf w (germRep w φ) = φ :=
  Function.surjInv_eq (germOf_surjective w) φ
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.GermMinimalPolynomialDivides
