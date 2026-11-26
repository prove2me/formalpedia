-- Prove2me | solution 1 for Stanley.orientationCount_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:55.523986+00:00
-- url     : https://prove2.me/submissions/852a4565-6198-4a9a-ad52-055d4b84cbd9

module
public import Definitions.Def_Stanley_Convolution
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Stanley_NegOne
public import Theorems.Thm_Stanley_orientationCount_induce_univ
public import Theorems.Thm_Stanley_chromaticPolynomial_induce_univ
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
theorem _root_.solution [IsEmpty V] : orientationCount G = 1 := by
  let d : AcyclicOrientation G := ⟨fun _ _ => False,
    (fun _ _ h => h.elim), (fun u => isEmptyElim u),
    ⟨fun u => isEmptyElim u⟩⟩
  have : Subsingleton (AcyclicOrientation G) := ⟨fun A B => by
    apply Subtype.ext
    funext u
    exact isEmptyElim u⟩
  let : Unique (AcyclicOrientation G) :=
    { default := d, uniq := fun _ => Subsingleton.elim _ _ }
  simp [orientationCount, Nat.card_eq_fintype_card]
end Stanley
