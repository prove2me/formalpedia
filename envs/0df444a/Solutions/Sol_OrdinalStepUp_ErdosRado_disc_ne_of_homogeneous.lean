-- Prove2me | solution 1 for OrdinalStepUp.ErdosRado.disc_ne_of_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:49:59.932635+00:00
-- url     : https://prove2.me/submissions/9f9cf42c-1cda-444f-9a9b-41a3d0d03f2b

import Mathlib.SetTheory.Cardinal.EventuallyConst
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.FinCases
import Definitions.Def_OrdinalStepUp_Solution
import Theorems.Thm_OrdinalStepUp_ErdosRado_disc_ne_disc_of_lexLT
import Theorems.Thm_OrdinalStepUp_ErdosRado_agree_iff_lexLT
import Theorems.Thm_OrdinalStepUp_ErdosRado_lexLT_of_not_lexLT

set_option autoImplicit true
open OrdinalStepUp OrdinalStepUp.ErdosRado
open Ordinal
universe u
variable {n r : ℕ} {α β κ μ θ : Ordinal} {a b c : SetOrd} {𝒜 ℬ 𝒞 : Set SetOrd}
  {V : Type u} {wo wo' : WellOrder} {x : wo.α}
namespace OrdinalStepUp.ErdosRado
theorem _root_.solution (hA : HomAgree 𝒜)
    (ha : a ∈ 𝒜) (hb : b ∈ 𝒜) (hc : c ∈ 𝒜)
    (hab : a ≺w b) (hbc : b ≺w c) : disc a b ≠ disc b c := by
  have ne₁ : a ≠ b := fun e => irrefl _ (e ▸ hab)
  have ne₂ : b ≠ c := fun e => irrefl _ (e ▸ hbc)
  rcases hA with h | h
  · exact disc_ne_disc_of_lexLT ((agree_iff_lexLT hab).1 (h ha hb ne₁))
      ((agree_iff_lexLT hbc).1 (h hb hc ne₂))
  · -- Disagreement reverses the lexicographic order, so the triple runs backwards.
    have rev : ∀ {x y}, x ∈ 𝒜 → y ∈ 𝒜 → x ≠ y → x ≺w y → y ≺ x := fun hx hy hne hxy =>
      lexLT_of_not_lexLT hxy (mt (agree_iff_lexLT hxy).2 (h hx hy hne))
    exact fun heq => disc_ne_disc_of_lexLT (rev hb hc ne₂ hbc) (rev ha hb ne₁ hab)
      (by rw [disc_comm c b, disc_comm b a]; exact heq.symm)
end OrdinalStepUp.ErdosRado
