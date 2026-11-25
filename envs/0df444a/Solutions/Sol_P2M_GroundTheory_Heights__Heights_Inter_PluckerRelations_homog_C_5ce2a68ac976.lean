-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_homog_C_5ce2a68ac976
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:46.508634+00:00
-- url     : https://prove2.me/submissions/646211bd-645b-4fe5-a0a5-e30f005302ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {K : Type*} [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.PluckerRelations
theorem _root_.solution (r : ℤ) (b : K) : IsMultiHomog (C r : MRing ι) (Pi.single b 0) := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    by_contra h
    exact (mem_support_iff.1 hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst hm0
  simp
end GroundTheory.Heights₂.Heights.Inter.PluckerRelations
