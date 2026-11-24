-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_chain_discSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:17.984714+00:00
-- url     : https://prove2.me/submissions/97e2e20a-1f7f-46dc-b7d4-832f6fcb2230

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_wo_gt
import Theorems.Thm_OrdinalStepUp_ErdosRado_nextIn_mem
import Theorems.Thm_OrdinalStepUp_ErdosRado_wo_nextIn
import Theorems.Thm_OrdinalStepUp_ErdosRado_discNext_eq
import Theorems.Thm_OrdinalStepUp_ErdosRado_wo_of_discNext_lt

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hD : IsIndec (otp 𝒟))
    (hup : ∀ a ∈ 𝒟, ∀ b ∈ 𝒟, ∀ c ∈ 𝒟, a ≺w b → b ≺w c → disc a b < disc b c)
    (w : Fin (n + 1) → Ordinal) (hmono : StrictMono w)
    (hw : ∀ i, w i ∈ discNext 𝒟 '' 𝒟) :
    ∃ u : FinChain (n + 2), (∀ i, u i ∈ 𝒟) ∧ ∀ j, discSeq u j = w j := by
  choose x hxD hxw using fun i => hw i
  -- The pulled-back points inherit the order, because `discNext` reflects it.
  have hxmono : ∀ i j : Fin (n + 1), i < j → x i ≺w x j := fun i j hij =>
    wo_of_discNext_lt hD hup (hxD i) (hxD j) (by rw [hxw i, hxw j]; exact hmono hij)
  set t : SetOrd := nextIn 𝒟 (x (Fin.last n)) with ht
  have hex : ∃ y, y ∈ 𝒟 ∧ x (Fin.last n) ≺w y := exists_wo_gt hD (hxD _)
  have htD : t ∈ 𝒟 := nextIn_mem hex
  have hlt : ∀ i : Fin (n + 1), x i ≺w t := by
    intro i
    rcases eq_or_lt_of_le (Fin.le_last i) with h | h
    · exact h ▸ wo_nextIn hex
    · exact _root_.trans (hxmono i _ h) (wo_nextIn hex)
  refine ⟨FinChain.mk (Fin.snoc x t) ?_, ?_, ?_⟩
  · -- the extended family is still increasing
    intro i j
    refine Fin.lastCases ?_ ?_ j
    · intro hij
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (n + 1), i = i'.castSucc :=
        ⟨i.castPred (Fin.ne_last_of_lt hij), (Fin.castSucc_castPred _ _).symm⟩
      simpa using hlt i'
    · intro j' hij
      obtain ⟨i', rfl⟩ : ∃ i' : Fin (n + 1), i = i'.castSucc :=
        ⟨i.castPred (Fin.ne_last_of_lt (hij.trans (Fin.castSucc_lt_last j'))),
          (Fin.castSucc_castPred _ _).symm⟩
      simpa using hxmono i' j' (by simpa using hij)
  · -- every point is in `𝒟`
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa using htD
    · intro i'; simpa using hxD i'
  · -- and the discrepancies are the values we started from
    intro j
    change disc (Fin.snoc (α := fun _ => SetOrd) x t j.castSucc)
      (Fin.snoc (α := fun _ => SetOrd) x t j.succ) = w j
    rw [Fin.snoc_castSucc]
    refine Fin.lastCases ?_ ?_ j
    · rw [Fin.succ_last, Fin.snoc_last]
      exact hxw _
    · intro j'
      rw [Fin.succ_castSucc, Fin.snoc_castSucc,
        ← discNext_eq hup (hxD _) (hxD _) (hxmono _ _ (Fin.castSucc_lt_succ (i := j')))]
      exact hxw _
end OrdinalStepUp.ErdosRado
