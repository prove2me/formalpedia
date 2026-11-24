-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_of_mem_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:21:35.406031+00:00
-- url     : https://prove2.me/submissions/b7e20853-5fb6-4dd7-b391-a228a82deabb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_mcPts_of_sameOrbit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_smul


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
open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
variable (R : AnLogRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, hzw, hΨw⟩ := hw
  have hzJ : z ∉ mcPts J := by
    intro hzJ
    refine hy ⟨z, hz, hzJ, ?_⟩
    rw [hzw]
    exact hΨw
  obtain ⟨x, hx⟩ := R.surj z hz hzJ
  obtain ⟨cc, hcc, hlift⟩ := hx
  have hμ : ∏ k, cc k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hcc k
  have hseg : segre (R.lift x x) = (∏ k, cc k) • w := by
    rw [hlift, segre_smul, hzw]
  have hΨl : Ψ (segre (R.lift x x)) = (∏ k, cc k) • Fin.cons 1 y := by
    rw [hseg, map_smul, hΨw]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, cc k := by
    rw [hΨl]
    simp
  refine ⟨x, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hzJ
    refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (cc k)⁻¹, fun k => inv_ne_zero (hcc k), ?_⟩ h
    funext p
    rw [hlift]
    exact (inv_mul_cancel_left₀ (hcc p.1) (z p)).symm
  · rw [h0]
    exact hμ
  · funext i
    simp only [brQ, hΨl]
    simp [hμ]
  · show (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x) = w
    rw [h0, hseg, smul_smul, inv_mul_cancel₀ hμ, one_smul]
end ReciprocityTheory.ChartRestriction.G.Geo
