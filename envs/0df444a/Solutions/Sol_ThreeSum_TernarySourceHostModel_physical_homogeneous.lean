-- Prove2me | solution 1 for ThreeSum.TernarySourceHostModel.physical_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:25:37.640995+00:00
-- url     : https://prove2.me/submissions/de872f7d-83f9-4b55-ba9f-7b0dea52d74f

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_TernaryWeightedPhysicalSources
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_histogram_homogeneous
import Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_histogram_homogeneous


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySourceHostModel
open Finset Light TernaryJointType
open scoped BigOperators
variable {N : ℕ}
namespace ThreeSum.TernarySourceHostModel
theorem _root_.solution (S : Finset (ℕ × ℕ)) (enumeration : ℕ → TritWord N)
    (key group : ℕ → ℕ) (weight : ℕ → ℤ) (h : ℕ)
    (hrank : ∀ pair∈S, TernaryBank.rank (enumeration (key pair.2))=h) (g : ℕ) :
    ∀ R, physical S enumeration key group weight g R≠0 → TernaryBank.rank R=h := by
  apply TernaryWeightedPhysicalSources.histogram_homogeneous
  intro pair hp
  exact hrank pair (Finset.mem_filter.mp hp).1
end ThreeSum.TernarySourceHostModel
