-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_erase_eq_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:26:02.351849+00:00
-- url     : https://prove2.me/submissions/38948b03-d2d6-4c53-ae18-80891e5869a8

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_erase_val
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_erase_mk
public import Theorems.Thm_SizeRamsey_Plan_tau4_le_of_restrict
public import Theorems.Thm_SizeRamsey_Plan_tau4_le_of_embed

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} {W : Type*}
namespace SizeRamsey.Plan
theorem _root_.solution [Fintype V] (G H : SimpleGraph V) (D : Finset V)
    (havoid : ∀ f, IsC4Map H f → ∀ i, f i ∉ D)
    (hadj : ∀ a b, a ∉ D → b ∉ D → (H.Adj a b ↔ G.Adj a b)) :
    tau4 (erase G D) = tau4 H := by
  apply le_antisymm
  · refine tau4_le_of_restrict Subtype.val Subtype.val_injective fun f hf => ?_
    obtain ⟨hinj, h01, h12, h23, h30⟩ := IsC4Map.erase_val hf
    have := (f 0).2; have := (f 1).2; have := (f 2).2; have := (f 3).2
    refine ⟨hinj, ?_, ?_, ?_, ?_⟩ <;> simp only [Function.comp] <;> rw [hadj] <;> assumption
  · refine tau4_le_of_embed Subtype.val fun f hf => ?_
    have hD := havoid f hf
    obtain ⟨hinj, h01, h12, h23, h30⟩ := hf
    refine ⟨fun i => ⟨f i, hD i⟩, IsC4Map.erase_mk ⟨hinj, ?_, ?_, ?_, ?_⟩ hD, rfl⟩ <;>
      rw [← hadj _ _ (hD _) (hD _)] <;> assumption
end SizeRamsey.Plan
