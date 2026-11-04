-- Prove2me | solution 1 for ThreeSum.LightWeightedSourceCountHost.physical_count_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:28:45.404504+00:00
-- url     : https://prove2.me/submissions/e308a2cd-69d7-43cf-9aa3-36844eb09754

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_ThreeSum_LightWeightedCountFrontend_weighted_count_spec
import Theorems.Thm_ThreeSum_LightWeightedWantedQuery_weighted_count_spec
import Theorems.Thm_ThreeSum_TernaryPhysicalSources_convolution_histograms
import Theorems.Thm_ThreeSum_TernarySourceHostModel_physical_homogeneous
import Theorems.Thm_ThreeSum_TernaryWeightedPhysicalSources_convolution_histograms


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedSourceCountHost
theorem _root_.solution {lim : Limits} {P : Program}
    {N a b p d t count dst keep : ℕ} (argv : List ℤ) (μ : ℕ → ℤ)
    (S T : Finset (ℕ × ℕ))
    (enumeration : ℕ → TernaryJointType.TritWord N)
    (leftKey leftGroup rightKey rightGroup : ℕ → ℕ)
    (leftWeight rightWeight : ℕ → ℤ)
    (group : ℕ → ℕ) (Q : ℕ → TernaryJointType.TritWord N)
    (hleft : ∀ pair∈S, TernaryBank.rank (enumeration (leftKey pair.2))=a)
    (hright : ∀ pair∈T, TernaryBank.rank (enumeration (rightKey pair.2))=b)
    (hQ : ∀ j<count, TernaryBank.rank (Q j)=a+b)
    (h : Meets lim P p d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=LightWeightedWantedRows.score
        (fun g A => TernaryConvolution.factorial A*
          TernarySourceHostModel.physical S enumeration leftKey leftGroup leftWeight g A)
        (fun g B => TernaryConvolution.factorial B*
          TernarySourceHostModel.physical T enumeration rightKey rightGroup rightWeight g B)
        group Q j)) :
    Meets lim P p d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=TernaryConvolution.factorial (Q j)*
        TernaryWeightedPhysicalSources.pairWeight
          (TernarySourceHostModel.channel S leftGroup (group j))
          (TernarySourceHostModel.channel T rightGroup (group j))
          (fun pair => enumeration (leftKey pair.2))
          (fun pair => enumeration (rightKey pair.2))
          (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (Q j)) := by
  have hc := LightWeightedCountFrontend.weighted_count_spec argv μ
    (TernarySourceHostModel.physical S enumeration leftKey leftGroup leftWeight)
    (TernarySourceHostModel.physical T enumeration rightKey rightGroup rightWeight) group Q
    (fun _ _ => TernarySourceHostModel.physical_homogeneous S enumeration leftKey leftGroup leftWeight a hleft _)
    (fun _ _ => TernarySourceHostModel.physical_homogeneous T enumeration rightKey rightGroup rightWeight b hright _)
    hQ h
  apply hc.mono le_rfl
  intro r ν hv
  refine ⟨hv.1,?_⟩
  intro j hj
  rw [hv.2 j hj]
  unfold TernarySourceHostModel.physical
  rw [TernaryWeightedPhysicalSources.convolution_histograms]
end ThreeSum.LightWeightedSourceCountHost
