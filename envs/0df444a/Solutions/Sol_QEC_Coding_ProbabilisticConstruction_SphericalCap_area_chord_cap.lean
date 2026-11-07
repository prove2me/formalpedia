-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.area_chord_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:54:34.490389+00:00
-- url     : https://prove2.me/submissions/17fab751-b5e4-468c-801c-1b3498a67094

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Slab
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_SmallCap
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_area_cap_all
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Set Metric
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (hεR : ε ≤ 2*R) (v : Sphere) :
    area (cap v (1-ε^2/(2*R^2))) = ENNReal.ofReal (Real.pi*ε^2/R^2) := by
  have hR2 : 0 < 2*R^2 := by positivity
  have hquot : 0 ≤ ε^2/(2*R^2) := div_nonneg (sq_nonneg _) hR2.le
  have hquot2 : ε^2/(2*R^2) ≤ 2 := by
    apply (div_le_iff₀ hR2).mpr
    have hs := (sq_le_sq₀ hε (by positivity : 0 ≤ 2*R)).mpr hεR
    nlinarith
  rw [area_cap_all]
  have he : capHeight (1-ε^2/(2*R^2)) = ε^2/(2*R^2) := by
    simp only [capHeight, max_eq_right (by linarith : (-1:ℝ) ≤ 1-ε^2/(2*R^2))]
    rw [show 1-(1-ε^2/(2*R^2)) = ε^2/(2*R^2) by ring, max_eq_right hquot]
  rw [he]
  congr 1
  ring
end QEC.Coding.ProbabilisticConstruction.SphericalCap
