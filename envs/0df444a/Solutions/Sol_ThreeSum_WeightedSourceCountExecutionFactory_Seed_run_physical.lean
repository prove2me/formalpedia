-- Prove2me | solution 1 for ThreeSum.WeightedSourceCountExecutionFactory.Seed.run_physical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:03:20.593226+00:00
-- url     : https://prove2.me/submissions/87d5b323-c81b-4c7e-85ae-eaff6a8cdf0e

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_SourceCountExecutionFactory
import Definitions.Def_Submission_ThreeSum_TernarySourceWeightSeed
import Definitions.Def_Submission_Weighted_Global_TernarySourceCountWeightSeed
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Seed_finish
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Seed_finish
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run_physical


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedSourceCountExecutionFactory
open Light TernaryJointType
namespace ThreeSum.WeightedSourceCountExecutionFactory
namespace Seed
theorem _root_.solution {N a b : ℕ} {S : Setup N} {lim : Limits} {d boundary : ℕ}
    {μ ν : ℕ→ℤ} {leftWeight rightWeight : ℕ→ℤ}
    (H : Seed S lim d boundary μ leftWeight rightWeight) (hkeep : Kept μ ν boundary)
    (hleftRead : ∀ i<S.left.NL, ν (S.left.weightBase+i)=leftWeight i)
    (hrightRead : ∀ i<S.right.NL, ν (S.right.weightBase+i)=rightWeight i)
    (hleft : ∀ pair∈S.left.records, WeightedGlobalBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, WeightedGlobalBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, WeightedGlobalBank.rank (S.front.Q j)=a+b) :
    Meets lim S.program 134 d S.argv ν S.runtime
      (fun _ ξ => Kept ν ξ boundary ∧ ∀ j<S.front.count,
        ξ (S.front.dst+j)=TernaryConvolution.factorial (S.front.Q j)*
          TernaryWeightedPhysicalSources.pairWeight
            (TernarySourceHostModel.channel S.left.records S.left.group (S.front.group j))
            (TernarySourceHostModel.channel S.right.records S.right.group (S.front.group j))
            (fun pair => S.front.E.word (S.left.key pair.2))
            (fun pair => S.front.E.word (S.right.key pair.2))
            (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (S.front.Q j)) := by
  apply ((H.finish hkeep hleftRead hrightRead).run_physical hleft hright hQ).mono le_rfl
  rintro r ξ ⟨hprefix,hvalue⟩
  exact ⟨fun x hx => hprefix x (lt_of_lt_of_le hx H.boundaryBefore),hvalue⟩
end Seed
end ThreeSum.WeightedSourceCountExecutionFactory
