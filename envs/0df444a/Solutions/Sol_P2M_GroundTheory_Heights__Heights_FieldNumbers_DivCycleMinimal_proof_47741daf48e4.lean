-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DivCycleMinimal_proof_47741daf48e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:43.938845+00:00
-- url     : https://prove2.me/submissions/73fd69ff-4444-46f9-b027-4ca403fc6774

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivCycleMinimal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDivCycleMinimal
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DivCycleMinimal_ringKrullDim_eq_eff9f06a084e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedQuot_ne_top_a831a4f25617


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace DivCycleMinimal
theorem _root_.solution : DivCycleMinimal.Statement.{u} := by
  intro F _ K _ _ ι _ P hP n hPn a ha W hW hWn hle
  have hmin : W ∈ (P ⊔ Ideal.span {a}).minimalPrimes := by
    refine ⟨⟨hW, hle⟩, fun Q hQ hQW => ?_⟩
    obtain ⟨hQp, hJQ⟩ := hQ
    by_contra hWQ
    obtain ⟨f, hfW, hfQ⟩ := Set.not_subset.mp hWQ
    have h1 := PFContracted.ringKrullDim_add_one_le (P := Q) (Q := W) hQW hfQ hfW
    have h2 := PFContracted.ringKrullDim_add_one_le (P := P) (Q := Q) (le_sup_left.trans hJQ) ha
      (hJQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
    have h3 := (add_le_add h1 (le_refl 1)).trans h2
    rw [DivCycleMinimal.ringKrullDim_eq W n hWn, DivCycleMinimal.ringKrullDim_eq P (n + 1) hPn] at h3
    have h4 : (((n + Fintype.card K + 1 + 1 : ℕ)) : WithBot ℕ∞) ≤ ((n + 1 + Fintype.card K : ℕ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using h3
    have h5 := WithBot.coe_le_coe.mp h4
    have h6 := ENat.natCast_le_natCast.mp h5
    omega
  exact ⟨hmin, length_localizedQuot_ne_top _ _ hmin⟩
end DivCycleMinimal
end GroundTheory.Heights₂.Heights.FieldNumbers
