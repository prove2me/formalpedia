-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeIntegralMass_proof_0af09eb068df
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:40:55.649298+00:00
-- url     : https://prove2.me/submissions/d60afc77-0428-44e3-9ea6-5f2b55c3cece

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Characterised
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_coordBall_mass_6af667653fce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ae_fibreCount_eq_zero_40bf10712179

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
open MvPolynomial MeasureTheory Module
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeIntegralMass
theorem _root_.solution (hF : ConeFibreDegree.Statement) (hM : ConeMassOfFibre.Statement) :
    ConeIntegralMass.Statement := by
  intro n e δ h W f hW hf hδ
  have hfib := hF n e δ h W f hW hf hδ
  have hmass := hM n (e + 1) δ h W hW hfib
  unfold coneIntegral
  simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [hmass]
  by_cases hn : e + 1 ≤ n
  · obtain ⟨hpos, hfin⟩ := coordBall_mass hn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_assoc,
      div_self (ENNReal.toReal_pos hpos.ne' hfin.ne).ne', mul_one]
  · have hδ0 : δ = 0 := by
      have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
        Measure.pi.isAddHaarMeasure _
      have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
      have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
        ae_neBot.2 (NeZero.ne _)
      obtain ⟨π, hπ⟩ := hfib.exists
      obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) h W π)).exists
      rw [hw1] at hw2
      exact_mod_cast hw2
    simp [hδ0]
end ConeIntegralMass
end GroundTheory.Heights₂.Heights
