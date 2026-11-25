-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_whole_ringKrullDim_b53d304dea6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:40.456335+00:00
-- url     : https://prove2.me/submissions/43b0a174-9d50-44ed-848a-56132dffeb5e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Examples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (n : ι → ℕ) (k₀ : ι)
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (N : ℕ) :
    ringKrullDim (ArithVariety.whole (fun _ : Unit ↦ N)).CoordRing =
      ((N + 1 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq
      (show (ArithVariety.whole (fun _ : Unit ↦ N)).ideal = ⊥ from rfl)).trans (RingEquiv.quotientBot _)),
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have hc : Nat.card (Coord (fun _ : Unit ↦ N)) = N + 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
    simp
  rw [hc, Fintype.card_unit]
  norm_cast
  omega
end GroundTheory.Heights₂.Heights
