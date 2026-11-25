-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.monX_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:39:10.132863+00:00
-- url     : https://prove2.me/submissions/cee7a7c1-e9ae-49f1-83a5-8636eeb2b244

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj
import Theorems.Thm_ReciprocityTheory_PGsh_Up_monX_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up
open ReciprocityTheory.PGsh.L2
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (D : Lifts H U X) (k : Ix g) : monX D (Pi.single k 1) = xL D k := by
  rw [monX_eq, Finset.prod_eq_single k]
  · simp [ZMod.val_one]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ k) h
end ReciprocityTheory.PGsh.Up
