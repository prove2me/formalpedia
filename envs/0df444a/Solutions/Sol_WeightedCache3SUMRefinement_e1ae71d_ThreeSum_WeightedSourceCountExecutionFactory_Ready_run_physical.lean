-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory.Ready.run_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:25:16.043245+00:00
-- url     : https://prove2.me/submissions/ab31dbbb-916d-4aef-b1dc-f625b89a009e

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_CountExecutionFactory
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_SourceCountExecutionFactory
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_LightTernarySourceCountHost_physical_count_spec
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedSourceCountHost_physical_count_spec
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedCountExecutionFactory_Ready_run


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory
namespace Ready
theorem _root_.solution {N a b : ℕ} {S : Setup N} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {leftWeight rightWeight : ℕ→ℤ} (H : Ready S lim d μ leftWeight rightWeight)
    (hleft : ∀ pair∈S.left.records, TernaryBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, TernaryBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, TernaryBank.rank (S.front.Q j)=a+b) :
    Meets lim S.program 134 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.left.base0 ∧ ∀ j<S.front.count,
        ν (S.front.dst+j)=TernaryConvolution.factorial (S.front.Q j)*
          TernaryWeightedPhysicalSources.pairWeight
            (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group j))
            (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group j))
            (fun pair => S.front.E.word (S.left.key pair.2))
            (fun pair => S.front.E.word (S.right.key pair.2))
            (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (S.front.Q j)) := by
  exact LightWeightedSourceCountHost.physical_count_spec S.argv μ S.left.records S.right.records
    S.front.E.word S.left.key S.left.group S.right.key S.right.group leftWeight rightWeight
    S.front.group S.front.Q hleft hright hQ H.run
end Ready
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSourceCountExecutionFactory
