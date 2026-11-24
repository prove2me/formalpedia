-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.brW_mem_fibre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:50.688816+00:00
-- url     : https://prove2.me/submissions/90c98bf3-34c1-411b-b9b3-aa62b3dca965

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
theorem _root_.solution (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  classical
  have hz0 : R.lift x x ∈ mcPts P := R.mem x x (R.mem_U x)
  let k0 : K := hK.some
  let cc : K → ℂ := fun k => if k = k0 then (Ψ (segre (R.lift x x)) 0)⁻¹ else 1
  have hcc : ∀ k, cc k ≠ 0 := by
    intro k
    simp only [cc]
    split_ifs
    · exact inv_ne_zero h0
    · exact one_ne_zero
  have horb : SameOrbit (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) (R.lift x x) := ⟨cc, hcc, rfl⟩
  have hprod : ∏ k, cc k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by simp [cc]
  have hseg : segre (fun p : (Σ k, ι k) => cc p.1 * R.lift x x p) = brW R Ψ x := by
    rw [segre_smul, hprod]
    rfl
  refine ⟨fun p => cc p.1 * R.lift x x p, mem_mcPts_of_sameOrbit hPh horb hz0, hseg, ?_⟩
  show Ψ ((Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)) = Fin.cons 1 (brQ R Ψ x)
  rw [map_smul]
  funext i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · simp [inv_mul_cancel₀ h0]
  · simp [brQ, div_eq_inv_mul]
end ReciprocityTheory.ChartRestriction.G.Geo
