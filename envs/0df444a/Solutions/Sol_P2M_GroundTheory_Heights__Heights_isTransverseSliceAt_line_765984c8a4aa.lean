-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isTransverseSliceAt_line_765984c8a4aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:12:39.794259+00:00
-- url     : https://prove2.me/submissions/802aeb38-01af-439b-bad0-153e8be7e66d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseObjects

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
open MvPolynomial Matrix ComplexSets IsLocalRing
noncomputable section
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    IsTransverseSliceAt (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 := by
  intro g hg
  refine ⟨1, by simp, ?_⟩
  rw [one_mul]
  refine Ideal.mem_sup_right ?_
  have hX : linPoly (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 - C (((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ 0) 0) = X 0 := by
    simp [linPoly]
  have hspan : Ideal.span (X '' (Set.univ : Set (Fin 1))) ≤
      Ideal.span (Set.range fun i : Fin 1 =>
        linPoly (1 : Matrix (Fin 1) (Fin 1) ℂ) i - C (((1 : Matrix (Fin 1) (Fin 1) ℂ) *ᵥ 0) i)) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, -, rfl⟩
    refine Ideal.subset_span ⟨i, ?_⟩
    dsimp only
    rw [Subsingleton.elim i 0, hX]
  refine hspan (MvPolynomial.mem_ideal_span_X_image.mpr fun m hm => ?_)
  refine ⟨0, Set.mem_univ _, fun h0 => ?_⟩
  have hm0 : m = 0 := Finsupp.ext fun i => by rw [Subsingleton.elim i 0, h0]; rfl
  subst hm0
  rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq, ← MvPolynomial.eval_zero] at hm
  exact hm hg
end GroundTheory.Heights₂.Heights
