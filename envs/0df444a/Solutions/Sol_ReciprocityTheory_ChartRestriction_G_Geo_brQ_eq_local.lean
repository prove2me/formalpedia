-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.brQ_eq_local
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:34.46068+00:00
-- url     : https://prove2.me/submissions/dbf19e64-d923-49d8-81e2-8aebf318e4f1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {x z : R.X} (hz : z ∈ R.U x) :
    brQ R Ψ z = fun i => Ψ (segre (R.lift x z)) i.succ / Ψ (segre (R.lift x z)) 0 := by
  obtain ⟨c, hc0, hc⟩ := R.compat x z z ⟨hz, R.mem_U z⟩
  have hseg : segre (R.lift x z) = (∏ k, c k) • segre (R.lift z z) := by
    funext i
    simp only [segre, Pi.smul_apply, smul_eq_mul, hc, Finset.prod_mul_distrib]
  have hC : (∏ k, c k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc0 k
  funext i
  simp only [brQ, hseg, map_smul, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hC]
end ReciprocityTheory.ChartRestriction.G.Geo
