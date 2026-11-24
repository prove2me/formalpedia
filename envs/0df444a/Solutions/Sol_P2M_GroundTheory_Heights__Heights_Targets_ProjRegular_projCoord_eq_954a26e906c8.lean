-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_projCoord_eq_954a26e906c8
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:08.412085+00:00
-- url     : https://prove2.me/submissions/c80d5120-55b6-405a-b984-879e0d77ff42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsProjRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PProjRegular
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_segre_lift_eq_2e320d5521fd

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
    projCoord R Ψ y = fun i => Ψ (segre (R.lift x y)) i.succ / Ψ (segre (R.lift x y)) 0 := by
  obtain ⟨c, hc, h⟩ := proj_segre_lift_eq Ψ hy
  funext i
  simp only [projCoord, h, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hc
end GroundTheory.Heights₂.Heights.Targets.ProjRegular
