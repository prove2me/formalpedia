-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_isSymmetric_d4be3b011480
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:52:15.088908+00:00
-- url     : https://prove2.me/submissions/9c24f06e-6987-4e30-81d5-14932c32e8a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums

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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    (powerSumHom N S).IsSymmetric := by
  have : powerSumHom N S ∈ symmetricSubalgebra (Fin N) ℚ := by
    have hsub : (powerSumHom N).range ≤ symmetricSubalgebra (Fin N) ℚ := by
      rintro _ ⟨T, rfl⟩
      simp only [powerSumHom]
      have : Algebra.adjoin ℚ (Set.range fun i : Fin N => psum (Fin N) ℚ (i.val + 1)) ≤
          symmetricSubalgebra (Fin N) ℚ := by
        rw [Algebra.adjoin_le_iff]
        rintro _ ⟨i, rfl⟩
        exact psum_isSymmetric (Fin N) ℚ _
      exact this (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨T, rfl⟩)
    exact hsub ⟨S, rfl⟩
  exact this
end GroundTheory.Heights₂.Heights.RestTerms.Flag
