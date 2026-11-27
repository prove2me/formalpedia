-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.hilbertLemmas
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:45.819434+00:00
-- url     : https://prove2.me/submissions/c2c4f854-28b3-4214-af2d-f4da02df8996

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_CvxOfConvex
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HormanderLemma
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_OntoWithBoundTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_cvx
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_hormanderLemma
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_minimalSolution
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ontoWithBound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_rieszOnRange
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_split


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution (E H₁ H₂ : Type*) [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂] :
    CVXStatement H₁ ∧ RieszOnRangeStatement E H₁ ∧ MinimalSolutionStatement E H₁ ∧
      SplitStatement E H₁ H₂ ∧ HormanderLemmaStatement E H₁ H₂ ∧
      OntoWithBoundStatement E H₁ H₂ :=
  ⟨cvx H₁, rieszOnRange E H₁, minimalSolution E H₁, split E H₁ H₂, hormanderLemma E H₁ H₂,
    ontoWithBound E H₁ H₂⟩
end ReciprocityTheory.L2DbarEstimates
