-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitC_indicator_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:16:27.06585+00:00
-- url     : https://prove2.me/submissions/eb5af690-8d55-4a54-b141-32e599c823be

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitC
import Theorems.Thm_ReciprocityTheory_Cheb_splitC_nrm_ge_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] (S : Set (Prm E)) (hS : S.Finite) (s : ℝ)
    (hs : 0 ≤ s) : ∑' q, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q ≤ hS.toFinset.card := by
  rw [tsum_eq_sum (s := hS.toFinset)]
  · calc ∑ q ∈ hS.toFinset, S.indicator (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s)) q
        ≤ ∑ _q ∈ hS.toFinset, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Set.indicator_of_mem (hS.mem_toFinset.mp hq)]
          exact Real.rpow_le_one_of_one_le_of_nonpos (splitC_nrm_ge_one q) (by linarith)
      _ = hS.toFinset.card := by simp
  · intro q hq
    rw [Set.indicator_of_notMem]
    intro h'
    exact hq (hS.mem_toFinset.mpr h')
end ReciprocityTheory.Cheb
