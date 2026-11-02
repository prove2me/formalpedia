-- Prove2me | solution 1 for TensorNP.Eigen.theorem_1_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:51:52.264199+00:00
-- url     : https://prove2.me/submissions/cb6ac4b3-c776-4a01-9fe5-a7e24d531e03
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_TensorNP_Eigen_colorable_iff_colorTensor_eigen
import Theorems.Thm_TensorNP_Eigen_colorTensor_encoding_transfer
import Definitions.Def_TensorNP_Eigen_Construction

open CookPvsNP TensorNP.Eigen ProjSchedTW.Complexity

/-- The mathematical color/eigenvalue equivalence and an explicit total
    polynomial-time encoding transfer imply the paper's many-one reduction.

    The second transfer clause rules out false positives for malformed input
    and for any ambiguity in tensor encodings. -/
theorem tensor_reduction_from_encoding
    (hsem : ∀ (v : ℕ) (G : SimpleGraph (Fin v)),
      G.Colorable 3 ↔ IsEigenvalue (castTensor ℝ (colorTensor G)) 0)
    (hencoding : ∃ f : List BSym → List BSym, PolyTimeComputable f ∧
      (∀ (v : ℕ) (G : SimpleGraph (Fin v)), f (graphCode G) = tensorCode (colorTensor G)) ∧
      (∀ w, f w ∈ tensorZeroEigLangR →
        ∃ (v : ℕ) (G : SimpleGraph (Fin v)), w = graphCode G ∧
          IsEigenvalue (castTensor ℝ (colorTensor G)) 0)) :
    PolyReducible threeColLang tensorZeroEigLangR := by
  obtain ⟨f, hf, hmap, hback⟩ := hencoding
  refine ⟨f, hf, ?_⟩
  intro w
  constructor
  · intro hin
    obtain ⟨v, G, hcol, rfl⟩ := hin
    rw [hmap v G]
    exact ⟨_, colorTensor G, by simpa using (hsem v G).mp hcol, rfl⟩
  · intro hout
    obtain ⟨v, G, hw, heig⟩ := hback w hout
    exact ⟨v, G, (hsem v G).mpr heig, hw⟩

/-- Hillar–Lim Theorem 1.3 reduced to the explicit encoding and machine transfer. -/
theorem solution : PolyReducible threeColLang tensorZeroEigLangR := by
  apply tensor_reduction_from_encoding
  · intro v G
    exact TensorNP.Eigen.colorable_iff_colorTensor_eigen G
  · exact TensorNP.Eigen.colorTensor_encoding_transfer
