-- Prove2me | solution 1 for ThreeSum.LightTernaryBankStages.zeta_program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:00.874278+00:00
-- url     : https://prove2.me/submissions/da5da23a-11e6-421a-8970-ba4f004029fc

import Definitions.Def_Submission_ThreeSum_LightTernaryBankSweep
import Definitions.Def_Submission_ThreeSum_LightTernaryBankStages
import Theorems.Thm_ThreeSum_LightTernaryBankStages_zeta_meets
import Theorems.Thm_ThreeSum_LightTernaryBankCoordinate_zeta_meets
import Theorems.Thm_ThreeSum_LightTernaryCell_zeta_meets
import Theorems.Thm_ThreeSum_LightTernaryLookup_zeta_meets


set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryBankStages
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightTernaryBankStages
theorem _root_.solution {N T n a powers L keyBase base d V : ℕ}
    (E : Enumeration N T n) (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤base) (hspace : base+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (base+j)=F (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ R, |F R|≤(V : ℤ)) (hvalword : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+5≤lim.depth) :
    Meets lim (program false) 0 d [N,a,n,powers,L,keyBase,base] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) base N μ' ∧
        Preserved μ μ' keyBase n base N ∧ Powers μ' powers (2*N)) := by
  exact zeta_meets (pMain := 0) (pCoord := 1) (pMeta := 2) (pZero := 3)
    (pDigit := 4) (pErase := 5) (pPass := 6) (pCell := 7) (pSearch := 8) (pValue := 9)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    E F μ hw ha hmeta hpows hspace hword hNword hcodes hsource hpowers hsorted
    hF hvalword hL hn hd
end ThreeSum.LightTernaryBankStages
