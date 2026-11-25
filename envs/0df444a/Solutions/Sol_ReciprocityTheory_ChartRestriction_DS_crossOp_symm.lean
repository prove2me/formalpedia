-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.crossOp_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:07.765652+00:00
-- url     : https://prove2.me/submissions/cea549da-804f-4bda-a412-80faaf4ae64f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCasA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_BigCas
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_adjoint
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_factorAd_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_BigCasimir_mAct_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_factorAd_adjoint
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
theorem _root_.solution (hU : IsInfUnitary ε E) (k : ℕ) (i : Fin k) (F G : Big n k M) :
    inner ℂ (crossOp ε E k i F) G = inner ℂ F (crossOp ε E k i G) := by
  have hU' : ∀ (a b : Fin n) (x y : M),
      inner ℂ (E a b x) y = adjSign ε a b * inner ℂ x (E b a y) := hU
  have hm : ∀ (a b : Fin n) (X Y : Big n k M),
      inner ℂ (mAct E k a b X) Y = adjSign ε a b * inner ℂ X (mAct E k b a Y) := by
    intro a b X Y
    simp only [PiLp.inner_apply, mAct_apply, hU', Finset.mul_sum]
  have hc : ∀ (a b c d : Fin n),
      mAct E k a b * factorAd (M := M) k i c d = factorAd k i c d * mAct E k a b := by
    intro a b c d
    refine LinearMap.ext fun F => PiLp.ext fun κ => ?_
    simp only [Module.End.mul_apply, mAct_apply, factorAd_apply]
    split_ifs <;> simp
  have hswap : ∀ g : Fin n → Fin n → ℂ,
      ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g b a =
        ∑ a, ∑ b ∈ univ.filter (fun b => ε b = ε a), g a b := by
    intro g
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rcases eq_or_ne (ε a) (ε b) with h | h
    · simp [h]
    · simp [h, h.symm]
  unfold crossOp
  simp only [LinearMap.sum_apply, sum_inner, inner_sum, Module.End.mul_apply]
  have h1 := hswap (fun a b => inner ℂ F (factorAd k i a b (mAct E k b a G)))
  rw [← h1]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.1 hb).2
  rw [factorAd_adjoint, hm, show adjSign ε b a = 1 by simp [adjSign, hab], one_mul]
  congr 1
  exact LinearMap.congr_fun (hc a b b a) G
end ReciprocityTheory.ChartRestriction.DS
