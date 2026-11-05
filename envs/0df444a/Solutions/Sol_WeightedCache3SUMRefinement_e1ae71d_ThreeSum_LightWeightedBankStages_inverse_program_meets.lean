-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages.inverse_program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:19:33.575715+00:00
-- url     : https://prove2.me/submissions/12d7c90d-0bff-4e1d-bf18-a8dead3f657b

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankSweep
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankStages_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryCell_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_inverse_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankCoordinate_inverse_meets


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightWeightedBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages
theorem _root_.solution {N T n a powers L keyBase base d V : ℕ}
    (E : Enumeration N T n) (H : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=H (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hH : ∀ R, |H R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim (program true) 0 d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => stageValue s H) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by
  exact inverse_meets (pMain := 0) (pCoord := 1) (pMeta := 2) (pZero := 3)
    (pDigit := 4) (pErase := 5) (pPass := 6) (pCell := 7) (pSearch := 8) (pValue := 9)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    E H μ hw ha hmeta hpows hspace hword hNword hcodes hsource hpowers hsorted
    hH hvalword hL hn hd
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.LightWeightedBankStages
