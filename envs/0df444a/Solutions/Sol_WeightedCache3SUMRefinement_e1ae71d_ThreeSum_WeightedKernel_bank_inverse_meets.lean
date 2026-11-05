-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel.bank_inverse_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:30:58.953138+00:00
-- url     : https://prove2.me/submissions/56ea3bb3-7963-4e37-b266-712782c48dde

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSourceWords
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStages
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_LightNearEnumerationMain
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenPhysical
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearSetup
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_KernelProgram
import Theorems.Thm_ThreeSum_LightTernaryCell_inverse_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_inverse_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankCoordinate_inverse_meets
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_LightWeightedBankStages_inverse_meets


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.WeightedBankEnumeration (cacheCost)
open ThreeSum.TernaryCodeSemantics ThreeSum.WeightedPhysicalEuler
open ThreeSum.WeightedBankStageModel ThreeSum.TernaryFrozenQueryStages
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
variable {lim : Limits}
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel
theorem _root_.solution {N T n
    a powers L keyBase base d V : ℕ}
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
    Meets lim program 24 d [N,a,n,powers,L,keyBase,base] μ (LightWeightedBankSweep.time N L n)
      (fun _ μ' => LightWeightedBankSweep.Stages E (fun s => stageValue s H) base N μ' ∧
        LightWeightedBankSweep.Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by
  exact LightWeightedBankStages.inverse_meets (P := program) (pMain := 24) (pCoord := 25) (pMeta := 20) (pZero := 11) (pDigit := 7) (pErase := 10) (pPass := 26) (pCell := 27) (pSearch := 13) (pValue := 28)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    E H μ hw ha hmeta hpows hspace hword hNword hcodes hsource hpowers hsorted
    hH hvalword hL hn hd
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedKernel
