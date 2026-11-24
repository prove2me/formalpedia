-- Prove2me | solution 1 for P2M_Formalism_GM_leadingTermLemmas_biHom_sq__c19e50466e6a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:59:33.570921+00:00
-- url     : https://prove2.me/submissions/1dc7956b-da19-46f4-84ee-5d5000756628

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead
import Theorems.Thm_Formalism_GM_leadingTermLemmas_sum_update
import Theorems.Thm_Formalism_GM_leadingTermLemmas_biHom_sq
import Theorems.Thm_Formalism_GM_leadingTermLemmas_multiDeg_total
import Theorems.Thm_Formalism_GM_leadingTermLemmas_multidegree_last_weight_sum
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
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K : Type} [Field K] {N r : ℕ} (LL : M.Letters (N + 1)) (ρ : Fin r)
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (m : Fin (N + 1) × Fin r →₀ ℕ) (hm : M.MultiDeg LL m) :
    BiHom (wW (N := N)) eη (LL.deg (Fin.last N) - m (Fin.last N, ρ)) (LL.total - m (Fin.last N, ρ))
      (sq (K := K) LL ρ m) := by
  have h1 := sum_update m (Fin.last N, ρ) (fun x => if x.1 = Fin.last N then 1 else 0)
  have h2 := sum_update m (Fin.last N, ρ) (fun _ => 1)
  rw [multidegree_last_weight_sum LL m hm] at h1
  rw [multiDeg_total LL m hm] at h2
  simp only [if_true, mul_one] at h1 h2
  have := biHom_sq (K := K) LL ρ m
  simp only [mul_one] at this
  rwa [show ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x * (if x.1 = Fin.last N then 1 else 0) =
      LL.deg (Fin.last N) - m (Fin.last N, ρ) by omega,
    show ∑ x, (Finsupp.update m (Fin.last N, ρ) 0) x = LL.total - m (Fin.last N, ρ) by omega] at this
end Formalism.GM.leadingTermLemmas
