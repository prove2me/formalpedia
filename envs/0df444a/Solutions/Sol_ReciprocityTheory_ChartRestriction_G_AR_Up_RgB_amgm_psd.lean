-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.RgB.amgm_psd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:37.762003+00:00
-- url     : https://prove2.me/submissions/c9d95ce3-f3fe-45ad-baa9-e6bdc9df8235

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustStatementPfA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
open Matrix
open scoped ComplexOrder Matrix
open ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
theorem _root_.solution {m : ℕ} (hm : 0 < m) {P : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosSemidef) :
    P.det.re ^ ((m : ℝ)⁻¹) ≤ P.trace.re / m := by
  have hH := hP.1
  have hd : P.det.re = ∏ i, hH.eigenvalues i := by
    rw [hH.det_eq_prod_eigenvalues]
    simp [← Complex.ofReal_prod]
  have ht : P.trace.re = ∑ i, hH.eigenvalues i := by
    rw [hH.trace_eq_sum_eigenvalues]
    simp [← Complex.ofReal_sum]
  have hnn : ∀ i, 0 ≤ hH.eigenvalues i := fun i => hP.eigenvalues_nonneg i
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin m))
    (fun _ => (m : ℝ)⁻¹) (fun i => hH.eigenvalues i) (fun _ _ => by positivity)
    (by simp [Finset.card_univ]; field_simp) (fun i _ => hnn i)
  rw [hd, ht, ← Real.finsetProd_rpow _ _ (fun i _ => hnn i)]
  calc ∏ i, hH.eigenvalues i ^ ((m : ℝ)⁻¹) ≤ ∑ i, (m : ℝ)⁻¹ * hH.eigenvalues i := h
    _ = (∑ i, hH.eigenvalues i) / m := by rw [← Finset.mul_sum]; field_simp
end ReciprocityTheory.ChartRestriction.G.AR.Up.RgB
