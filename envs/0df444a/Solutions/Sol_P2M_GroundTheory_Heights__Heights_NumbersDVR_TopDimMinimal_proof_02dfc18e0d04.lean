-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_TopDimMinimal_proof_02dfc18e0d04
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:57.354898+00:00
-- url     : https://prove2.me/submissions/9d60cbde-3eb7-49c1-81fc-5f7acc4f84fa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTopDimMinimal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace TopDimMinimal
theorem _root_.solution (h1 : DimStrictDrop.Statement.{u}) : TopDimMinimal.Statement.{u} := by
  intro A _ J Q _ N hJQ hJ hQ
  by_contra hmin
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hWne : W ≠ Q := fun h => hmin (h ▸ hW)
  have hWlt : W < Q := lt_of_le_of_ne hWQ hWne
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := hW.1.2
  have h2 : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ W) := h1 A W Q hWlt
  have h3 : ringKrullDim (A ⧸ W) ≤ ringKrullDim (A ⧸ J) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJW) (Ideal.Quotient.factor_surjective hJW)
  have h4 : ((N : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Q) + 1 :=
    add_le_add (not_lt.mp hQ) le_rfl
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) = ((N : ℕ) : WithBot ℕ∞) + 1 := Nat.cast_succ N
  exact lt_irrefl _ (lt_of_le_of_lt (h5 ▸ h4.trans (h2.trans h3)) hJ)
end TopDimMinimal
end GroundTheory.Heights₂.Heights.NumbersDVR
