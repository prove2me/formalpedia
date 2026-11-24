-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_trans_fac
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:50.732238+00:00
-- url     : https://prove2.me/submissions/833b15ad-4de4-46a8-b194-e1dfcc9f5045

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsAlg
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStA

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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology
variable {J : Type} [Fintype J] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {P : Ideal (MvPolynomial J ℤ)} {U U' : Set (Fin D → ℂ)}
    {γ γ' : (Fin D → ℂ) → J → ℂ} (hpts : ∀ y ∈ U, γ y ∈ pts P) {O' : Set (J → ℂ)}
    {q' : (J → ℂ) → Fin D → ℂ} (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {w : Fin D → ℂ} (hw : w ∈ U) (hwO : γ w ∈ O') :
    q' (γ w) ∈ U' ∧ ∃ c : ℂ, c ≠ 0 ∧ γ w = c • γ' (q' (γ w)) := by
  have hmem : γ w ∈ O' ∩ pts P := ⟨hwO, hpts w hw⟩
  rw [hOP'] at hmem
  obtain ⟨y', hy', c, hc, hcw⟩ := hmem
  have hinv : c⁻¹ • γ w = γ' y' := by rw [hcw, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hq : q' (γ w) = y' := by
    rw [← (hsc' (γ w) hwO c⁻¹ (inv_ne_zero hc)).2, hinv, hqγ' y' hy']
  refine ⟨by rw [hq]; exact hy', c, hc, ?_⟩
  rw [hq]
  exact hcw
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
