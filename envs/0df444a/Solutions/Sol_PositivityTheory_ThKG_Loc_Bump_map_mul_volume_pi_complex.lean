-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Bump.map_mul_volume_pi_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:27.383205+00:00
-- url     : https://prove2.me/submissions/adeeffea-97ad-4d2c-ae2f-8cd8da7c0f63

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_ExistsDensity
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplexFourier
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ArchimedeanBumps_IntegrableConjPowGaussian
import Theorems.Thm_PositivityTheory_ThKG_Loc_Bump_nm_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Bump
open MeasureTheory Filter Topology Set
open scoped ComplexConjugate
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.ThKG.Loc.Bump
theorem _root_.solution {y : ι → ℂ} (hy : ∀ w, y w ≠ 0) :
    Measure.map (fun x : ι → ℂ => y * x) volume = ENNReal.ofReal (nm y)⁻¹ • volume := by
  classical
  let L : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun w => (Algebra.lmul ℝ ℂ (y w)).comp (LinearMap.proj w)
  have hd : LinearMap.det L = nm y := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) (f := L) (by rw [hd]; exact (nm_pos hy).ne')
  rw [hd, abs_of_pos (inv_pos.2 (nm_pos hy))] at this
  exact this
end PositivityTheory.ThKG.Loc.Bump
