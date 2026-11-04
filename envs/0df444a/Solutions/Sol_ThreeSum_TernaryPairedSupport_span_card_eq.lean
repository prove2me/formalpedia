-- Prove2me | solution 1 for ThreeSum.TernaryPairedSupport.span_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:25.554393+00:00
-- url     : https://prove2.me/submissions/8b84f065-4169-4918-b5b4-bfd0f72065b6

import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryPairedSupport

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
theorem _root_.solution {j : ℕ} (v : Fin j → V) (hv : LinearIndependent K v) :
    Nat.card (Submodule.span K (Set.range v)) = Fintype.card K ^ j := by
  classical
  rw [Module.natCard_eq_pow_finrank (K := K)]
  rw [Nat.card_eq_fintype_card]
  rw [finrank_span_eq_card hv]
  simp
end ThreeSum.TernaryPairedSupport
