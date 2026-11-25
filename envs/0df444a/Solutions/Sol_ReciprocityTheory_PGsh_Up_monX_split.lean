-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.monX_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:39:14.367557+00:00
-- url     : https://prove2.me/submissions/c47eb996-538c-491c-a4d0-01cbf4bf1481

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
theorem _root_.solution (D : Lifts H U X) {α : Nb p g} {j : Ix g} (hj : α j ≠ 0) :
    monX D α = xL D j * monX D (Function.update α j (α j - 1)) := by
  rw [monX_eq, monX_eq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j, xL D i ^ (Function.update α j (α j - 1) i).val =
      ∏ i ∈ Finset.univ.erase j, xL D i ^ (α i).val :=
    Finset.prod_congr rfl fun i hi => by simp [Function.update_apply, Finset.ne_of_mem_erase hi]
  have hself : (Function.update α j (α j - 1) j) = α j - 1 := by simp [Function.update_apply]
  rw [hrest, hself]
  have hv1 : 1 ≤ (α j).val := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, ZMod.val_eq_zero])
  have hsub : (α j - 1).val = (α j).val - 1 := by
    rw [ZMod.val_sub (by rw [ZMod.val_one]; exact hv1), ZMod.val_one]
  rw [hsub, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hv1]
end ReciprocityTheory.PGsh.Up
