-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.iteratedDeriv_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:43.775894+00:00
-- url     : https://prove2.me/submissions/ad031a8c-1bcb-44fc-93b7-3d03b8badf10

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_IteratedDerivOrbit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_hasDerivAt_orbit

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (v : D) (m : ℕ) :
    iteratedDeriv m (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) (v : H)) =
      fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) ((((actM E X) ^ m) v : D) : H) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    rw [(hasDerivAt_orbit hσ hD hX ((actM E X ^ m) v) t).deriv, pow_succ', Module.End.mul_apply]
end ReciprocityTheory.ChartRestriction.DS
