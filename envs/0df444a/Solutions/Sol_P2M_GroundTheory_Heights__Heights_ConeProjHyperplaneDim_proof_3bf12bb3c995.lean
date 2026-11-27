-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_proof_3bf12bb3c995
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:57.96183+00:00
-- url     : https://prove2.me/submissions/2f8636f4-df13-469e-ab1d-f63d9de55e1f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeProjHyperplaneDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetParam
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeProjHyperplaneDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_coneForm_zero_799732297cbd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_cone_rel_fa3848bfc4a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeProjHyperplaneDim_krullDim_le_of_rel_5aa08ca6aebb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj segre mcPts psiPoly)
open GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
namespace GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
theorem _root_.solution : ConeProjHyperplaneDim.Statement := by
  intro n e P Ψ hP hΨ
  classical
  set J := complexFibreIdeal P ⊔ Ideal.span {coneFirstForm Ψ} with hJ
  have hrad : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) =
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J.radical) := by
    rw [ringKrullDim_quotient, ringKrullDim_quotient, PrimeSpectrum.zeroLocus_radical]
  rw [hrad]
  choose r hr H hH hrelP using fun i => cone_rel hP hΨ i
  have h0 : coneForm Ψ 0 ∈ J.radical := by
    rw [coneForm_zero]
    exact Ideal.le_radical (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  refine krullDim_le_of_rel J.radical (fun j : Fin e => coneForm Ψ j.succ) r hr
    (fun i j => H i j.succ) (fun i j => hH i j.succ) (fun i => ?_)
  have h1 : X i ^ r i - ∑ j, coneForm Ψ j * H i j ∈ J.radical :=
    Ideal.radical_mono le_sup_left (hrelP i)
  rw [Fin.sum_univ_succ] at h1
  have heq : X i ^ r i - ∑ j : Fin e, coneForm Ψ j.succ * H i j.succ =
      (X i ^ r i - (coneForm Ψ 0 * H i 0 + ∑ j : Fin e, coneForm Ψ j.succ * H i j.succ)) +
        coneForm Ψ 0 * H i 0 := by ring
  rw [heq]
  exact add_mem h1 (Ideal.mul_mem_right _ _ h0)
end GroundTheory.Heights₂.Heights.ConeProjHyperplaneDim
