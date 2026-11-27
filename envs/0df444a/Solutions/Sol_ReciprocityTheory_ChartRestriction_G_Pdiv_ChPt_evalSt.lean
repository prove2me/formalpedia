-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt.evalSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:33:37.321052+00:00
-- url     : https://prove2.me/submissions/b25c721a-5a2e-4c15-bfa3-001abde02309

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_InChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ChartPointCongruence_EqOfMod
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsLocalRing MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open ReciprocityTheory.ChartRestriction.G.Chart (jetLift jetLift_zR jet_ext)
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
namespace ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
theorem _root_.solution : EvalSt := by
  intro T O _ _ _ I m d k χ c hχ f
  have htr : MvPowerSeries.trunc O (Finsupp.equivFunOnFinite.symm fun _ => k + 1)
      (MvPowerSeries.map (algebraMap T O) f) = MvPolynomial.map (algebraMap T O)
        (MvPowerSeries.trunc T (Finsupp.equivFunOnFinite.symm fun _ => k + 1) f) := by
    ext e
    simp only [MvPolynomial.coeff_map, MvPowerSeries.coeff_trunc]
    split_ifs <;> simp
  have hcomp : χ.comp (Ideal.Quotient.mkₐ T _) =
      (Ideal.Quotient.mkₐ T I).comp (MvPolynomial.aeval (fun q : Fin m × Fin d => c q.1 q.2)) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, MvPolynomial.aeval_X]
    exact hχ q
  rw [htr, MvPolynomial.eval_map, ← MvPolynomial.aeval_def]
  exact AlgHom.congr_fun hcomp _
end ReciprocityTheory.ChartRestriction.G.Pdiv.ChPt
