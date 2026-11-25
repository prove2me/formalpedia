-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.itD_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:12:41.5148+00:00
-- url     : https://prove2.me/submissions/ead81d1e-3698-4bdd-b238-58ce640c5e59

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PolyDerivMonomialOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {s : (Fin 1 → W) → ℂ} (hs : ContDiff ℂ (⊤ : ℕ∞) s) (l : List W) :
    itD (fun z : W => s (fun _ => z)) l 0 = iteratedFDeriv ℂ l.length s 0 (fun j _ => l.get j) := by
  unfold itD
  have hi : ((l.length : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    first
      | exact_mod_cast le_top
      | exact WithTop.coe_le_coe.2 le_top
  have h := (ContinuousLinearMap.pi fun _ : Fin 1 => ContinuousLinearMap.id ℂ W).iteratedFDeriv_comp_right
    hs (0 : W) hi
  exact congrArg (fun T => T (fun j => l.get j)) h
end ReciprocityTheory.ChartRestriction.G.I2
