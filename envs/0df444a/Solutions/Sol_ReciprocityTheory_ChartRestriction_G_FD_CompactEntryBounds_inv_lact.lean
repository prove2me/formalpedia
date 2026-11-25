-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.inv_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:04.488891+00:00
-- url     : https://prove2.me/submissions/f44d3c0b-1273-47db-94dc-97193a102f68

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
theorem _root_.solution (γ : GL (Fin r) E) (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ * Y)⁻¹ *ᵥ Data.emb τ v =
      Y⁻¹ *ᵥ Data.emb τ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  have hinv : ((γ : Matrix (Fin r) (Fin r) E).map τ)⁻¹ =
      ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero τ) (map_one τ)]
  rw [Matrix.mul_inv_rev, hinv, ← Matrix.mulVec_mulVec]
  congr 1
  funext a
  exact (RingHom.map_mulVec τ _ v a).symm
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
