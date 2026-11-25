-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.exists_primRoot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:39:01.902035+00:00
-- url     : https://prove2.me/submissions/9581c334-a03e-4f61-a19f-42ba72e716ab

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution [IsAlgClosed C] [CharZero C] : ∃ ζ : C, IsPrimitiveRoot ζ p := by
  haveI : NeZero (p : C) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p C) (by
    rw [Polynomial.degree_cyclotomic, Nat.totient_prime hp.out]
    have := hp.out.two_le
    norm_cast
    omega)
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩
end ReciprocityTheory.PGsh.Up.U3
