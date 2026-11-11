-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.supported_pair_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T21:56:57.757955+00:00
-- url     : https://prove2.me/submissions/a8065c84-87cd-4949-92ae-bd2b189cbe31

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_normalizedDisplacement_smul
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_normalizedDisplacement_mem
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_cap_pair_inner_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_coordinateAxis_orthogonal


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (p q : Space) {R θ : ℝ} (hR : 0 < R)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/24) {i j : Fin 3} (hij : i ≠ j)
    (hp : p ∈ displacementCap R (coordinateAxis i) (Real.cos θ))
    (hq : q ∈ displacementCap R (coordinateAxis j) (Real.cos θ)) :
    ⟪p,q⟫_ℝ ≤ R^2 / 4 := by
  have h := cap_pair_inner_le (coordinateAxis i) (coordinateAxis j)
    (normalizedDisplacement p hR hp.1) (normalizedDisplacement q hR hq.1)
    (coordinateAxis_orthogonal hij) hθ0 hθ1
    (normalizedDisplacement_mem p hR _ hp) (normalizedDisplacement_mem q hR _ hq)
  have hm := mul_le_mul_of_nonneg_left h (sq_nonneg R)
  rw [← normalizedDisplacement_smul p hR hp.1, ← normalizedDisplacement_smul q hR hq.1,
    real_inner_smul_left, real_inner_smul_right]
  nlinarith
end QEC.Coding.BDL26RandomPerturbation
