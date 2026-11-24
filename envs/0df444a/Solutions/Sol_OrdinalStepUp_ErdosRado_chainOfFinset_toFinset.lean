-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.chainOfFinset_toFinset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:15.780158+00:00
-- url     : https://prove2.me/submissions/1a19de04-276c-441f-b0f3-63364df7ea78

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_FinChain_mem_toFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
attribute [local simp] OrdinalStepUp.ErdosRado.toFinset_chainOfFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (u : FinChain n) :
    chainOfFinset u.toFinset u.card_toFinset = u := by
  have hlist : u.toFinset.sort WOle = List.ofFn u := by
    refine List.Perm.eq_of_pairwise' (Finset.pairwise_sort _ _)
      (List.pairwise_ofFn.2 fun i j hij => Or.inr (u.map_rel_iff.2 hij)) ?_
    rw [List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) (List.nodup_ofFn.2 u.injective)]
    intro a
    rw [Finset.mem_sort, List.mem_ofFn, FinChain.mem_toFinset]
  refine DFunLike.coe_injective (funext fun i => ?_)
  change (u.toFinset.sort WOle).get _ = _
  simp [hlist]
end OrdinalStepUp.ErdosRado
