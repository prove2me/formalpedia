-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_relDim_lt_of_lt_7832e8c64fa7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:08:19.456128+00:00
-- url     : https://prove2.me/submissions/a01a0e86-7d7a-47ed-b095-89369017d8bc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalIntegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsValuativeCentre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PExistsForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalIntegral
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalIntegral_exists_ringKrullDim_eq_nat_98f2ffb13dfc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_krullDim_quot_add_one_le_e3d9e5ecaaa0


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
open GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
theorem _root_.solution {Q Q₂ : Ideal (MRing ι F)} [Q.IsPrime] [Q₂.IsPrime] (h : Q < Q₂) :
    relDim Q₂ < relDim Q := by
  obtain ⟨x, hx, hxQ⟩ := SetLike.exists_of_lt h
  have hle := Inter.krullDim_quot_add_one_le h.le hx hxQ
  obtain ⟨D, hD⟩ := exists_ringKrullDim_eq_nat Q
  obtain ⟨D₂, hD₂⟩ := exists_ringKrullDim_eq_nat Q₂
  rw [hD, hD₂] at hle
  have : D₂ + 1 ≤ D := by exact_mod_cast hle
  rw [PFContracted.relDim_eq_int hD, PFContracted.relDim_eq_int hD₂]
  exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))
end GroundTheory.Heights₂.Heights.FieldNumbers.SemilocalIntegral
