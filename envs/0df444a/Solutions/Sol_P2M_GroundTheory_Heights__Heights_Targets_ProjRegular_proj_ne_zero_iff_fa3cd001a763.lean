-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_ProjRegular_proj_ne_zero_iff_fa3cd001a763
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:04.814522+00:00
-- url     : https://prove2.me/submissions/b58f29b9-68a5-4e55-ae83-bc19de14392a

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
    Ψ (segre (R.lift y y)) 0 ≠ 0 ↔ Ψ (segre (R.lift x y)) 0 ≠ 0 := by
  obtain ⟨c, hc, h⟩ := proj_segre_lift_eq Ψ hy
  simp [h, hc]
end GroundTheory.Heights₂.Heights.Targets.ProjRegular
