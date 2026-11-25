-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.red_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:38:17.122009+00:00
-- url     : https://prove2.me/submissions/379140d2-1a3b-4575-b30e-7fad6b6f367d

import Definitions.Def_ReciprocityTheory_DualLattices_EmbeddingSeparatingGroupStatement
import Definitions.Def_ReciprocityTheory_DualLattices_UnramifiedCokernelLengthOfLengthEigenLengthProduct
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination

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
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution (y : Nb p g) : ∃ t : TT p g, red p g t = y := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ⟨fun i => ((y i).val : ℤ_[p]), funext fun i => by
    show PadicInt.toZMod (((y i).val : ℕ) : ℤ_[p]) = y i
    rw [map_natCast, ZMod.natCast_zmod_val]⟩
end ReciprocityTheory.PGsh.Up
