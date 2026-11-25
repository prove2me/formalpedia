-- Prove2me | solution 1 for P2M_Formalism_GM_DimensionMonotonicity_glAct_wh__8320259c7632
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:38:02.481093+00:00
-- url     : https://prove2.me/submissions/fce4ae04-7d7f-4f7c-a29f-e910ddbb348a

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_M_FB_evVal_castSucc
import Theorems.Thm_Formalism_GM_M_FB_evVal_last
import Theorems.Thm_Formalism_GM_M_FB_ext_castSucc
import Theorems.Thm_Formalism_GM_M_FB_ext_last
import Theorems.Thm_Formalism_GM_M_FB_res_apply
import Theorems.Thm_Formalism_GM_M_FB_res_ext
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_deg_last
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_castSucc
import Theorems.Thm_Formalism_GM_M_FB_snoc_vec_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.M.FB.evVal_castSucc
attribute [local simp] Formalism.GM.M.FB.evVal_last
attribute [local simp] Formalism.GM.M.FB.ext_castSucc
attribute [local simp] Formalism.GM.M.FB.ext_last
attribute [local simp] Formalism.GM.M.FB.res_apply
attribute [local simp] Formalism.GM.M.FB.res_ext
attribute [local simp] Formalism.GM.M.FB.snoc_deg_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_deg_last
attribute [local simp] Formalism.GM.M.FB.snoc_vec_castSucc
attribute [local simp] Formalism.GM.M.FB.snoc_vec_last



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution (LL : Letters N) {j J : ℕ} (hjJ : j ≤ J) (a b : Fin r) {ν : Fin r → ℤ}
    {x : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) ν) :
    glAct p LL j a b x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv LL J) (ν + dl a b) := by
  rw [mem_weightedHomogeneousSubmodule] at hx
  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hwd : Finsupp.weight (wv LL J) d = ν := hx (mem_support_iff.mp hd)
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  split_ifs with h1' h2
  · have h1 : (i : ℕ) < J := by omega
    have h3 := wh_XD (K := ℚ_[p]) (wv LL J) (i, b) (i, a) d (coeff d x)
    have e : ν + dl a b = Finsupp.weight (wv LL J) d - wv LL J (i, b) + wv LL J (i, a) := by
      rw [hwd]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, wv, h1, h2, if_true, if_false, ite_true, ite_false,
        Bool.false_eq_true, dl_apply, Pi.single_apply]
      split_ifs <;> omega
    rw [e]
    exact h3
  · have h1 : (i : ℕ) < J := by omega
    have h3 := wh_XD (K := ℚ_[p]) (wv LL J) (i, a) (i, b) d (coeff d x)
    have e : ν + dl a b = Finsupp.weight (wv LL J) d - wv LL J (i, a) + wv LL J (i, b) := by
      rw [hwd]
      funext c
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, wv, h1, h2, if_true, if_false, ite_true, ite_false,
        Bool.false_eq_true, dl_apply, Pi.single_apply]
      split_ifs <;> omega
    rw [LinearMap.neg_apply, e]
    exact Submodule.neg_mem _ h3
  · rw [LinearMap.zero_apply]
    exact Submodule.zero_mem _
end Formalism.GM.DimensionMonotonicity
