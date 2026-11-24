-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Numbers_ringKrullDim_eq_of_relDim_b46a94ec49e5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:35.886687+00:00
-- url     : https://prove2.me/submissions/cc3e4148-da7e-4765-8ce8-313b8d75934f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumIsFieldIntersection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumRatSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabMultiHomogIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PVocabDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumUnique
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
omit [DecidableEq K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
theorem _root_.solution (V : Ideal (MRing ι F)) (n : ℕ)
    (h : FieldNumbers.relDim V = (n : WithBot (WithTop ℤ))) :
    ringKrullDim (MRing ι F ⧸ V) = ((n + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  unfold FieldNumbers.relDim at h
  generalize ringKrullDim (MRing ι F ⧸ V) = d at h ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h₁ : ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) = (n : WithBot (WithTop ℤ)) := h
      have h' : (⊤ : WithTop ℤ) = (n : WithTop ℤ) := by exact_mod_cast h₁
      exact absurd h' (WithTop.top_ne_coe)
    | coe m =>
      have h₁ : ((((m : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) =
          (n : WithBot (WithTop ℤ)) := h
      have h' : (m : ℤ) - Fintype.card K = n := by exact_mod_cast h₁
      have hm : m = n + Fintype.card K := by omega
      rw [hm]
      rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.Numbers
