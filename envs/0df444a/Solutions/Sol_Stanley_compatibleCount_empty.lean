-- Prove2me | solution 1 for Stanley.compatibleCount_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:02:31.259432+00:00
-- url     : https://prove2.me/submissions/bb0c956f-a3df-4973-b94b-e5236b0a9931

module
public import Definitions.Def_Stanley_Compatible
public import Mathlib.Tactic.Ring
public import Definitions.Def_Stanley_Reciprocity
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
public import Theorems.Thm_Stanley_orientationCount_induce_univ
attribute [local simp] Stanley.chromaticPolynomial_induce_univ
attribute [local simp] Stanley.orientationCount_induce_univ



set_option autoImplicit true
@[expose] public section
public section
open Stanley
open SimpleGraph Finset Polynomial
universe u
variable {V : Type u} [Fintype V] (G : SimpleGraph V)
namespace Stanley
theorem _root_.solution [IsEmpty V] (k : ℕ) : compatibleCount G k = 1 := by
  let d : AcyclicOrientation G := ⟨fun _ _ => False,
    (fun _ _ h => h.elim), (fun u => isEmptyElim u), ⟨fun u => isEmptyElim u⟩⟩
  let p : CompatiblePair G k := ⟨d, (fun u => isEmptyElim u), (fun u => isEmptyElim u)⟩
  have : Subsingleton (CompatiblePair G k) := ⟨fun A B => by
    apply CompatiblePair.ext
    · apply Subtype.ext
      funext v
      exact isEmptyElim v
    · funext v
      exact isEmptyElim v⟩
  let : Unique (CompatiblePair G k) :=
    { default := p, uniq := fun _ => Subsingleton.elim _ _ }
  simp [compatibleCount, Nat.card_eq_fintype_card]
end Stanley
