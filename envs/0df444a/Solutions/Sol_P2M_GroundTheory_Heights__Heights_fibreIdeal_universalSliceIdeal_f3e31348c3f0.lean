-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_fibreIdeal_universalSliceIdeal_f3e31348c3f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:21.466989+00:00
-- url     : https://prove2.me/submissions/50be0df5-aa0e-4daa-9c46-7059c924be79

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBundleRadicalAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreIdeal_map_C_e0f3e21e5aef


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (L : Matrix (Fin d) (Fin n) ℂ) :
    fibreIdeal (universalSliceIdeal J d q) (fun ij => L ij.1 ij.2) = sliceIdeal J L q := by
  rw [fibreIdeal, universalSliceIdeal, Ideal.map_sup, ← fibreIdeal, fibreIdeal_map_C, Ideal.map_span,
    sliceIdeal, ← Set.range_comp]
  have h : (MvPolynomial.map (eval fun ij : Fin d × Fin n => L ij.1 ij.2)) ∘
      (fun i : Fin d => ∑ j, C (X (i, j)) * (X j - C (C (q j)))) =
      fun i => ComplexSets.linPoly L i - C ((L *ᵥ q) i) := by
    funext i
    simp [ComplexSets.linPoly, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib, map_sum]
  rw [h]
end GroundTheory.Heights₂.Heights
