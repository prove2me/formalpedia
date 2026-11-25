-- Prove2me | solution 1 for PI.UConjT.transferStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:42:04.418686+00:00
-- url     : https://prove2.me/submissions/a7272c35-1250-4750-a590-7d11ccfec48d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_TransferStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryConjugation_Transfer
import Theorems.Thm_PI_UConjT_inner_toEuclideanLin_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UConjT
open Matrix
namespace PI.UConjT
theorem _root_.solution : TransferStep := by
  intro hO n g hg
  have hg2 : gᴴ * g = 1 := by
    rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.mp hg
  obtain ⟨b, hbo, hbe, hbr⟩ := hO (n + 1) (EuclideanSpace ℂ (Fin (n + 1)))
    finrank_euclideanSpace_fin (Matrix.toEuclideanLin g) (inner_toEuclideanLin_unitary g hg2)
    (EuclideanSpace.single (Fin.last n) 1)
  choose d hd using hbe
  refine ⟨Matrix.of fun i j => b j i, ?_, d, ?_, ?_⟩
  · rw [mem_unitaryGroup_iff']
    ext i j
    have h1 := orthonormal_iff_ite.mp hbo i j
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h1
    simp only [star_eq_conjTranspose, mul_apply, conjTranspose_apply, of_apply, one_apply]
    rw [← h1]
    simp [dotProduct, mul_comm]
  · ext i j
    have h1 := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) => v i) (hd j)
    simp only [Matrix.toLpLin_apply, PiLp.smul_apply, smul_eq_mul] at h1
    rw [mul_diagonal, mul_apply]
    simp only [of_apply]
    simpa [mulVec, dotProduct, mul_comm] using h1
  · intro i
    have h1 := hbr i
    rw [EuclideanSpace.inner_single_right] at h1
    simpa using h1
end PI.UConjT
