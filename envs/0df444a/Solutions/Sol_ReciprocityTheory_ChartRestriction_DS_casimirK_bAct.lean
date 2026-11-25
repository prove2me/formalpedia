-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.casimirK_bAct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:24.550235+00:00
-- url     : https://prove2.me/submissions/f7db1344-0846-4874-b24b-2ed4a01a009a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mAct_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (k : ℕ) :
    casimirK ε (bAct E k) = factorCasimir ε k + casimirK ε (mAct E k) + 2 • ∑ i, crossOp ε E k i := by
  have hc : ∀ (a b c d : Fin n) (i : Fin k),
      mAct E k a b * factorAd (M := M) k i c d = factorAd k i c d * mAct E k a b := by
    intro a b c d i
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    simp only [Module.End.mul_apply, mAct_apply, factorAd_apply]
    split_ifs <;> simp
  have hswap : ∀ g : Fin n → Fin n → Module.End ℂ (Big n k M),
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g b a =
        ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g a b := by
    intro g
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rcases eq_or_ne (ε a) (ε b) with h | h
    · simp [h]
    · simp [h, h.symm]
  have hX : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        mAct E k a b * ∑ i, factorAd (M := M) k i b a =
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        (∑ i, factorAd (M := M) k i a b) * mAct E k b a := by
    have h1 := hswap (fun a b => (∑ i, factorAd (M := M) k i a b) * mAct E k b a)
    rw [← h1]
    simp only [Finset.mul_sum, Finset.sum_mul, hc]
  have hY : ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a),
        (∑ i, factorAd (M := M) k i a b) * mAct E k b a =
      ∑ i, ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), factorAd k i a b * mAct E k b a := by
    simp only [Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  unfold factorCasimir crossOp bAct casimirK
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  rw [hX, hY, two_smul]
  abel
end ReciprocityTheory.ChartRestriction.DS
