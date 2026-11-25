-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.monX_zero_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:35:53.431541+00:00
-- url     : https://prove2.me/submissions/6c2c22e7-f8fd-436d-b458-0df88bdec1a7

import Definitions.Def_ReciprocityTheory_DualLattices_LiftMonomialDeterminantStatement
import Definitions.Def_ReciprocityTheory_DualLattices_PowMemCarrier
import Definitions.Def_ReciprocityTheory_DualLattices_IsLocalOfIntegers
import Definitions.Def_ReciprocityTheory_DualLattices_MemOfSumSingleEqZero
import Definitions.Def_ReciprocityTheory_DualLattices_EigenLiftsFrobenius
import Definitions.Def_ReciprocityTheory_DualLattices_HasLenLeOfSurj

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
theorem _root_.solution (D : Lifts H U X) {α : Nb p g} (hα : α ≠ 0) : monX D α 0 = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
  have hj' : α j ≠ 0 := hj
  have h0 : xL D j 0 = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp (D.x_mem j)).2
  have hv : (α j).val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  simp only [monX]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [h0, zero_pow hv])
end ReciprocityTheory.PGsh.Up
