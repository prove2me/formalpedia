-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_segre_lift_eq_2e320d5521fd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:33.058153+00:00
-- url     : https://prove2.me/submissions/29f24510-3047-4a4d-96ef-c6e0e978bce6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.Targets.ProjRegular
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {n : ℕ} {R : AnLogRes P J (n + 1)} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))
namespace GroundTheory.Heights₂.Heights.Targets.ProjRegular
theorem _root_.solution {x y : R.X} (hy : y ∈ R.U x) :
    ∃ c : ℂ, c ≠ 0 ∧ Ψ (segre (R.lift y y)) = c • Ψ (segre (R.lift x y)) := by
  obtain ⟨c, hc, hz⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  refine ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr (fun k _ => hc k), ?_⟩
  rw [← map_smul]
  congr 1
  funext i
  simp only [segre, Pi.smul_apply, smul_eq_mul, hz, Finset.prod_mul_distrib]
end GroundTheory.Heights₂.Heights.Targets.ProjRegular
