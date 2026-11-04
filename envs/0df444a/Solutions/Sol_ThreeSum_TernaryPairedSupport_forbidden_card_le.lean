-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupport.forbidden_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:43:27.920784+00:00
-- url     : https://prove2.me/submissions/d2265d7f-d3fe-441f-afa0-48eb7b8dc1a2

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport
import Theorems.Thm_ThreeSum_TernaryPairedSupport_span_card_eq

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
theorem _root_.solution {j : ℕ} (f : E → V) (hf : Function.Injective f)
    (v : Fin j → V) (hv : LinearIndependent K v) :
    (univ.filter fun e => f e ∈ Submodule.span K (Set.range v)).card ≤
      Fintype.card K ^ j := by
  classical
  letI := Fintype.ofFinite (Submodule.span K (Set.range v))
  let S := univ.filter fun e => f e ∈ Submodule.span K (Set.range v)
  let g : S → Submodule.span K (Set.range v) := fun e =>
    ⟨f e.val, (mem_filter.mp e.property).2⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective g hg
  have hc' : Nat.card S ≤ Nat.card (Submodule.span K (Set.range v)) := by
    simpa only [Nat.card_eq_fintype_card] using hc
  rw [span_card_eq v hv] at hc'
  change S.card ≤ _
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hc'
end ThreeSum.TernaryPairedSupport
