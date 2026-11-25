-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.nbAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:41:07.202703+00:00
-- url     : https://prove2.me/submissions/60b4aa59-142f-4547-9ac9-e88da5597c86

import Definitions.Def_ReciprocityTheory_DualLattices_ExistsReductionOfCoordinateCombination
import Definitions.Def_ReciprocityTheory_DualLattices_AvgFZero

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
variable {G : Type} [CommGroup G] [Fintype G] (β : G → O)
namespace ReciprocityTheory.PGsh.Up
theorem _root_.solution {H : HodgeTateDatum p g v R O σ cp}
    (hmul : ∀ γ γ', H.ρ (β (γ * γ')) = H.ρ (β γ) * H.ρ (β γ')) (γ δ : G) (y : Nb p g) :
    nbAct H (β (γ * δ)) y = nbAct H (β γ) (nbAct H (β δ) y) := by
  rw [nbAct, nbAct, nbAct, hmul, Matrix.map_mul, Matrix.mulVec_mulVec]
end ReciprocityTheory.PGsh.Up
