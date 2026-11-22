-- Prove2me | solution 1 for PES.indep_iff_concurrent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:49:19.265667+00:00
-- url     : https://prove2.me/submissions/ad15b0ff-16c3-4bf1-b2ba-4ef7195cf844

import Definitions.Def_EventStructures_Prime_Basic
import Definitions.Def_EventStructures_Family_Basic
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Definitions.Def_EventStructures_Prime_Configuration
import Theorems.Thm_PES_enables_iff
import Theorems.Thm_ConfFamily_Indep_symm
import Theorems.Thm_PES_concurrent_irrefl

attribute [local simp] PES.enables_iff

set_option autoImplicit true
variable {L : Type*} (es : PES L)
open PES
variable {L : Type*} (P : PES L)
namespace PES
theorem _root_.solution {c : Set P.Event} {e₁ e₂ : P.Event}
    (h₁ : Configuration.enables P c e₁) (h₂ : Configuration.enables P c e₂)
    (hf₁ : e₁ ∉ c) (hf₂ : e₂ ∉ c) :
    P.toFamily.Indep c e₁ e₂ ↔ P.concurrent e₁ e₂ := by
  constructor
  · rintro ⟨hne, -, -, hst⟩
    refine ⟨hst.1 (Or.inl (Or.inr rfl)) (Or.inr rfl), ?_, ?_⟩
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | rfl
      · exact hf₁ (h₂.2.2 hlt)
      · exact hne rfl
    · intro hle
      rcases lt_or_eq_of_le hle with hlt | rfl
      · exact hf₂ (h₁.2.2 hlt)
      · exact hne rfl
  · intro hconc
    have hne : e₁ ≠ e₂ := by rintro rfl; exact P.concurrent_irrefl _ hconc
    have hc1 : isConf P (c ∪ {e₁}) := ((PES.enables_iff P).mpr h₁).2
    refine ⟨hne, (PES.enables_iff P).mpr h₁, (PES.enables_iff P).mpr h₂, ?_, ?_⟩
    · rintro x y (hx | rfl) (hy | rfl)
      · exact hc1.1 hx hy
      · rcases hx with hx | rfl
        · exact fun hcf => h₂.2.1 x hx (P.conflict_symm.symm _ _ hcf)
        · exact hconc.1
      · rcases hy with hy | rfl
        · exact h₂.2.1 y hy
        · exact fun hcf => hconc.1 (P.conflict_symm.symm _ _ hcf)
      · exact P.conflict_irrefl _
    · rintro x y (hx | rfl) hle
      · exact Or.inl (hc1.2 hx hle)
      · rcases lt_or_eq_of_le hle with hlt | rfl
        · exact Or.inl (Or.inl (h₂.2.2 hlt))
        · exact Or.inr rfl
end PES
