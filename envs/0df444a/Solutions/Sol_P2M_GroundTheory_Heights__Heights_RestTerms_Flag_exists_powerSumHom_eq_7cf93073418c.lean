-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:23.926223+00:00
-- url     : https://prove2.me/submissions/6c346138-4bbd-44c4-82c3-5083c679a287

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_esymm_mem_range_4f4cf4a0cb66

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
theorem _root_.solution {N : ℕ} {P : MvPolynomial (Fin N) ℚ} (hP : P.IsSymmetric) :
    ∃ S, powerSumHom N S = P := by
  obtain ⟨Q, hQ⟩ := esymmAlgHom_fin_surjective ℚ (le_refl N) ⟨P, hP⟩
  have h1 : P = aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q := by
    rw [← esymmAlgHom_apply, hQ]
  have h2 : aeval (fun i : Fin N => esymm (Fin N) ℚ (i + 1)) Q ∈ (powerSumHom N).range := by
    have hsub : Algebra.adjoin ℚ (Set.range fun i : Fin N => esymm (Fin N) ℚ (i + 1)) ≤
        (powerSumHom N).range := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact esymm_mem_range N _ (by omega)
    exact hsub (by rw [Algebra.adjoin_range_eq_range_aeval]; exact ⟨Q, rfl⟩)
  rw [h1]
  exact h2
end GroundTheory.Heights₂.Heights.RestTerms.Flag
