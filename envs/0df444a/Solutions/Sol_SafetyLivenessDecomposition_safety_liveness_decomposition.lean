-- Prove2me | solution 1 for SafetyLivenessDecomposition.safety_liveness_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T22:46:40.761709+00:00
-- url     : https://prove2.me/submissions/ea6f6754-0543-40ee-b210-293b41c6a666

module
public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Finiteness.Attr
public import Definitions.Def_LeanPool_LeanModelChecking_SafetyLivenessDecomposition
public import Theorems.Thm_SafetyLivenessDecomposition_slice_length
public import Theorems.Thm_SafetyLivenessDecomposition_slice_get
public import Theorems.Thm_SafetyLivenessDecomposition_slice_append
public import Theorems.Thm_SafetyLivenessDecomposition_append_slice_eq_self
attribute [local simp] SafetyLivenessDecomposition.slice_length
attribute [local simp] SafetyLivenessDecomposition.slice_get

set_option autoImplicit true
@[expose] public section
public section
open SafetyLivenessDecomposition
namespace SafetyLivenessDecomposition
theorem _root_.solution
  {T}
  [t_nonempty : Nonempty T]
  (P : Property T)
  : ∃ (A B : Property T), SafetyProp A ∧ LivenessProp B ∧ (A ∩ B = P)
  := by
  let A : Property T := {σ : InfWord T | ∀ n, ∃ β : InfWord T, (σ.slice n).append β ∈ P}
  let B : Property T := P ∪ Aᶜ
  refine ⟨A, B, ?_, ?_, ?_⟩
  · -- `A` is a safety property
    intro σ hσ
    have hnot : ¬∀ n, ∃ β : InfWord T, (σ.slice n).append β ∈ P := by
      simpa [A] using hσ
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hforall : ∀ β : InfWord T, (σ.slice i).append β ∉ P := not_exists.mp hi
    refine ⟨i, fun β hAβ => ?_⟩
    have hslice : ((σ.slice i).append β).slice i = σ.slice i := by
      simpa [slice_length] using slice_append (σ.slice i) β
    obtain ⟨γ, hγ⟩ := hAβ i
    exact hforall γ (by convert hγ using 1; simp [hslice])
  · -- `B` is a liveness property
    intro α
    by_cases h : ∃ β : InfWord T, α.append β ∈ P
    · rcases h with ⟨β, hβ⟩
      exact ⟨β, Or.inl hβ⟩
    · have hforall : ∀ β : InfWord T, α.append β ∉ P := not_exists.mp h
      obtain ⟨t⟩ := t_nonempty
      refine ⟨fun _ => t, Or.inr fun hA => ?_⟩
      have hslice : (α.append (fun _ => t)).slice α.length = α := slice_append α _
      obtain ⟨γ, hγ⟩ := hA α.length
      exact hforall γ (by convert hγ using 1; simp [hslice])
  · -- intersection equals `P`
    ext σ; constructor
    · intro hσ
      exact hσ.2.resolve_right (fun h => h hσ.1)
    · intro hσ
      refine ⟨fun n => ⟨fun k => σ (k + n), ?_⟩, Or.inl hσ⟩
      convert hσ using 1
      simp [append_slice_eq_self]
end SafetyLivenessDecomposition
