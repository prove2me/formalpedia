-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.exists_nat_of_two_le_dim_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:26:01.782317+00:00
-- url     : https://prove2.me/submissions/f95e0679-2c65-4c61-a9a3-0e957e00d3b9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CardPieceIrrelevantIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_TwoLeKrullDimOfRelevantPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : WithBot ℕ∞} {D : ℕ} (h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ x)
    (hD : x ≤ ((D + 2 : ℕ) : WithBot ℕ∞)) : ∃ d ≤ D, x = ((d + 2 : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h2 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have := WithBot.coe_le_coe.1 hD
      exact absurd (top_le_iff.1 this) (ENat.natCast_ne_top _)
    | coe n =>
      have h2' : 2 ≤ n := Nat.cast_le.1 (WithBot.coe_le_coe.1 h2)
      have hD' : n ≤ D + 2 := Nat.cast_le.1 (WithBot.coe_le_coe.1 hD)
      refine ⟨n - 2, by omega, ?_⟩
      rw [show n - 2 + 2 = n by omega]
      rfl
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
