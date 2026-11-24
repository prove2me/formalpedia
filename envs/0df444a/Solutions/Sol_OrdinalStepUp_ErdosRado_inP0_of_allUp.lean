-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.inP0_of_allUp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:51:33.98199+00:00
-- url     : https://prove2.me/submissions/b14f2696-c1bd-467a-bfbd-69574ba6186b

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_inK_of_homog
attribute [local simp] OrdinalStepUp.ErdosRado.toFinset_chainOfFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hom : HomAgree 𝒞)
    (hup : ∀ a ∈ 𝒞, ∀ b ∈ 𝒞, ∀ c ∈ 𝒞, a ≺w b → b ≺w c → disc a b < disc b c)
    {u : FinChain (n + 4)} (hu : ∀ j, u j ∈ 𝒞) : InP0 u := by
  refine ⟨inK_of_homog hom hu, fun j ↦ ?_⟩
  rw [discSeq, discSeq, show (Fin.castSucc j).succ = (Fin.succ j).castSucc from
    (Fin.succ_castSucc j).symm]
  exact hup _ (hu _) _ (hu _) _ (hu _)
    (u.map_rel_iff.2 (by simp [Fin.lt_def])) (u.map_rel_iff.2 (by simp [Fin.lt_def]))
end OrdinalStepUp.ErdosRado
