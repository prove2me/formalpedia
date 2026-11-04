-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalTensorFactory.Ready.run_scaled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:18:18.480197+00:00
-- url     : https://prove2.me/submissions/04e61c14-8ab0-4eeb-92f0-b9aa1105a67f

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensorScaled
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryScaled
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_tensorIndex_lt
import Theorems.Thm_ThreeSum_LightWeightedGlobalTensorFactory_Ready_run
import Theorems.Thm_ThreeSum_TernaryPairedTensorScaled_scaled_total
import Theorems.Thm_ThreeSum_TernarySourceExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedCountExecutionFactory_Ready_run
import Theorems.Thm_ThreeSum_WeightedSourceCountExecutionFactory_Ready_run


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedGlobalTensorFactory
open Light TernaryJointType TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightWeightedGlobalTensorFactory
namespace Ready
theorem _root_.solution {N a b d K J config ls rs tensorBase quad powers cols potPowers U : ℕ}
    {S : WeightedSourceCountExecutionFactory.Setup N} {lim : Limits} {μ : ℕ→ℤ}
    {L R : ℕ→ℕ→ℤ} {V : ℤ}
    (H : Ready S lim d K J config ls rs tensorBase quad powers cols potPowers μ L R U V)
    (hleft : ∀ pair∈S.left.records, WeightedGlobalBank.rank (S.front.E.word (S.left.key pair.2))=a)
    (hright : ∀ pair∈S.right.records, WeightedGlobalBank.rank (S.front.E.word (S.right.key pair.2))=b)
    (hQ : ∀ j<S.front.count, WeightedGlobalBank.rank (S.front.Q j)=a+b)
    (P : Fin S.front.count→Type*) [∀ i, Fintype (P i)]
    (A B : ∀ i, P i→Fin (J+2)→ℤ) (s : ℤ)
    (hModel : ∀ (i : Fin S.front.count) (a b c e : Fin (J+2)),
      score S J L R i.val (LightTernaryPairedPolynomial.tensorIndex (J+2) a.val b.val c.val e.val)=
        s*tensor (A i) (B i) a b c e) :
    Meets lim (program S K) 150 d
      [config,ls,S.left.NL,rs,S.right.NL,J,S.left.weightBase,S.right.weightBase,
        tensorBase,S.front.count,S.front.dst,quad,powers,cols,potPowers] μ
      (LightWeightedGlobalTensorDriver.time K J S.left.NL S.right.NL S.front.count S.runtime)
      (fun r ν => r=s^K*((∑ i : Fin S.front.count, ∑ e : Fin K→P i,
          TernaryPairedPotential.rowWeight
            (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ) ∧
        LightWeightedGlobalTensorDriver.InputKept μ ν quad tensorBase S.front.count ((J+2)^4)) := by
  apply (H.run hleft hright hQ).mono le_rfl
  rintro r ν ⟨hr,hT,hkeep⟩
  refine ⟨hr.trans (TernaryPairedTensorScaled.scaled_total K tensorBase (J+2) ν A B s ?_),hkeep⟩
  intro i a b c e
  rw [hT i.val i.isLt _ (LightTernaryPairedPolynomial.tensorIndex_lt a.isLt b.isLt c.isLt e.isLt)]
  exact hModel i a b c e
end Ready
end ThreeSum.LightWeightedGlobalTensorFactory
