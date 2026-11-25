-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_of_equiv_0fa1882a45e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:59:49.50053+00:00
-- url     : https://prove2.me/submissions/78202ea5-0b4a-4442-bbb1-0d5d740706bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_isIntegralElem_comp_ringEquiv_6375cdd6f877
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_norm_le_one_iff_isIntegralElem_padicInt_f628f916acb3
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open IsDedekindDomain NumberField Polynomial Rat.HeightOneSpectrum
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
theorem _root_.solution (p : ℕ) [Fact p.Prime] {E O K : Type*} [Field E]
    [CommRing O] [NormedField K] [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
    [Algebra E K] (ι : O →+* E) (e : ℚ_[p] →+* E) (ψ : ℤ_[p] ≃+* O)
    (hψ : ∀ z, ι (ψ z) = e (algebraMap ℤ_[p] ℚ_[p] z))
    (he : algebraMap ℚ_[p] K = (algebraMap E K).comp e) (x : K) :
    ‖x‖ ≤ 1 ↔ ((algebraMap E K).comp ι).IsIntegralElem x := by
  rw [norm_le_one_iff_isIntegralElem_padicInt p, ← isIntegralElem_comp_ringEquiv ψ]
  have : (algebraMap ℚ_[p] K).comp (algebraMap ℤ_[p] ℚ_[p]) =
      ((algebraMap E K).comp ι).comp (ψ : ℤ_[p] →+* O) :=
    RingHom.ext fun z => by simp [he, hψ]
  rw [this]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
