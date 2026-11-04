-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupport.exists_joint_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:44:31.712626+00:00
-- url     : https://prove2.me/submissions/dda14273-3a7d-4e8b-8b54-38f8ec4b101b

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Theorems.Thm_ThreeSum_TernaryPairedSupport_forbidden_card_le

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedSupport
open Finset
attribute [local instance] Classical.propDecidable
variable {K E V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
  [AddCommGroup W] [Module K W] [Fintype W]
  [Fintype E]
namespace ThreeSum.TernaryPairedSupport
theorem _root_.solution (f : E → V) (g : E → W)
    (hf : Function.Injective f) (hg : Function.Injective g) (m : ℕ)
    (hcard : 2 * Fintype.card K ^ m < Fintype.card E) :
    ∃ e : Fin m → E, LinearIndependent K (fun i => f (e i)) ∧
      LinearIndependent K (fun i => g (e i)) := by
  classical
  have haux : ∀ j ≤ m, ∃ e : Fin j → E,
      LinearIndependent K (fun i => f (e i)) ∧
      LinearIndependent K (fun i => g (e i)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine ⟨Fin.elim0, ?_, ?_⟩ <;> exact linearIndependent_empty_type
    | succ j ih =>
      intro hj
      obtain ⟨e,hef,heg⟩ := ih (by omega)
      let A := univ.filter fun x => f x ∈ Submodule.span K (Set.range (fun i => f (e i)))
      let B := univ.filter fun x => g x ∈ Submodule.span K (Set.range (fun i => g (e i)))
      have hA : A.card ≤ Fintype.card K ^ j := forbidden_card_le f hf _ hef
      have hB : B.card ≤ Fintype.card K ^ j := forbidden_card_le g hg _ heg
      have hpow : Fintype.card K ^ j ≤ Fintype.card K ^ m :=
        Nat.pow_le_pow_right Fintype.card_pos (by omega)
      have hAB : (A ∪ B).card < (univ : Finset E).card := by
        have hu := card_union_le A B
        simp only [card_univ]
        omega
      obtain ⟨x,hx,hout⟩ := exists_mem_notMem_of_card_lt_card hAB
      have hfa : f x ∉ Submodule.span K (Set.range (fun i => f (e i))) := by
        intro h
        exact hout (mem_union_left B (mem_filter.mpr ⟨mem_univ _,h⟩))
      have hgb : g x ∉ Submodule.span K (Set.range (fun i => g (e i))) := by
        intro h
        exact hout (mem_union_right A (mem_filter.mpr ⟨mem_univ _,h⟩))
      refine ⟨Fin.cons x e, ?_, ?_⟩
      · change LinearIndependent K (f ∘ Fin.cons x e)
        rw [Fin.comp_cons]
        exact hef.finCons hfa
      · change LinearIndependent K (g ∘ Fin.cons x e)
        rw [Fin.comp_cons]
        exact heg.finCons hgb
  exact haux m le_rfl
end ThreeSum.TernaryPairedSupport
