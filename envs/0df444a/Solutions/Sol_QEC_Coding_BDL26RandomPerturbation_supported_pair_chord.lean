-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.supported_pair_chord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:02:50.95637+00:00
-- url     : https://prove2.me/submissions/9adf85e5-f1ed-4915-b345-b835e81dd90b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Geometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SupportGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_supported_pair_inner

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (p q : Space) {R θ : ℝ} (hR : 0 < R)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1/24) {i j : Fin 3} (hij : i ≠ j)
    (hp : p ∈ displacementCap R (coordinateAxis i) (Real.cos θ))
    (hq : q ∈ displacementCap R (coordinateAxis j) (Real.cos θ)) : R ≤ ‖p-q‖ := by
  have hi := supported_pair_inner p q hR hθ0 hθ1 hij hp hq
  have hn := norm_sub_sq_real p q
  rw [hp.1, hq.1] at hn
  have hnorm := norm_nonneg (p-q)
  nlinarith
end QEC.Coding.BDL26RandomPerturbation
