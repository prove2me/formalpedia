-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.exists_chain_of_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:53:56.456721+00:00
-- url     : https://prove2.me/submissions/b3af04d1-9f40-417d-a7a9-ac314094716c

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_toFinset_chainOfFinset
import Theorems.Thm_OrdinalStepUp_ErdosRado_exists_chain_head
attribute [local simp] OrdinalStepUp.ErdosRado.toFinset_chainOfFinset

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : IsIndec (otp 𝒜))
    {a b c e : SetOrd} (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜) (he : e ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) (hce : c ≺w e) :
    ∃ u : FinChain (n + 4), (∀ i, u i ∈ 𝒜) ∧
      u 0 = a ∧ u 1 = b ∧ u 2 = c ∧ u 3 = e := by
  have hvmem : ∀ i, (![a, b, c, e] : Fin 4 → SetOrd) i ∈ 𝒜 := by
    intro i; fin_cases i <;> simpa
  have hvmono : ∀ i i' : Fin 4, i < i' →
      (![a, b, c, e] : Fin 4 → SetOrd) i ≺w ![a, b, c, e] i' := by
    -- the three composites, so every case is a hypothesis lookup
    have hac := _root_.trans hab hbc
    have hbe := _root_.trans hbc hce
    have hae := _root_.trans hac hce
    intro i i'
    fin_cases i <;> fin_cases i' <;> simp_all
  obtain ⟨u, hu, heq⟩ :=
    exists_chain_head (j := 3) (L := n + 4) hA (by omega) ![a, b, c, e] hvmem hvmono
  refine ⟨u, hu, ?_, ?_, ?_, ?_⟩
  · simpa using heq 0
  · simpa using heq 1
  · rw [show (2 : Fin (n + 4)) = ⟨2, by omega⟩ from Fin.ext (by simp)]; simpa using heq 2
  · rw [show (3 : Fin (n + 4)) = ⟨3, by omega⟩ from Fin.ext (by simp)]; simpa using heq 3
end OrdinalStepUp.ErdosRado
