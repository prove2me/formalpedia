-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChowSecDegree_proof_68e50720dc8e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:17:33.893452+00:00
-- url     : https://prove2.me/submissions/6847e68e-717d-40f4-8bef-bffcb1bbb4e7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowSecDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_specRest_bcd4be807f6e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_det_linear_9fa9fdfd32bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_normForm_eq_det_0ca3f0e920b9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace ChowSecDegree
theorem _root_.solution (h1 : ChowNormForm.Statement) (h2 : ChowFormHomog.Statement)
    (h3 : NormFormEval.Statement) : ChowSecDegree.Statement := by
  intro k E _ _ _ _ n e Q g y hy hQ hg
  classical
  obtain ⟨hfin, c, hc, heq⟩ := h1 k E n e Q g y hy hQ hg
  set QE := Q.map (MvPolynomial.map (algebraMap k E))
  have : Module.Finite E (SecAlg QE y) := hfin
  have : Module.Free E (SecAlg QE y) := Module.Free.of_divisionRing E (SecAlg QE y)
  let b : Module.Basis (Module.Free.ChooseBasisIndex E (SecAlg QE y)) E (SecAlg QE y) :=
    Module.Free.chooseBasis E (SecAlg QE y)
  have hN : (normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    rw [normForm_eq_det b, Module.finrank_eq_card_chooseBasisIndex]
    refine isHomogeneous_det_linear _ fun i k' => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    exact IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_X E j).mul (isHomogeneous_C (Fin n) _)
  have hone : (∑ j, algebraMap E (SecAlg QE y) (y (.inr j)) * secCoord QE y j) = 1 := by
    have hmem : chartForm y - 1 ∈ secIdeal QE y := Ideal.mem_sup_right (Ideal.subset_span rfl)
    have h := Ideal.Quotient.eq.mpr hmem
    rw [map_one] at h
    rw [← h]
    simp [chartForm, linForm, secCoord, map_sum, map_mul]
    rfl
  have hN0 : normForm (R := E) (SecAlg QE y) (secCoord QE y) ≠ 0 := by
    intro h0
    have hv := h3 E (SecAlg QE y) n (secCoord QE y) (fun j => y (.inr j))
    rw [h0, map_zero, hone, map_one] at hv
    exact zero_ne_one hv
  have hG : (specRest (algebraMap k E) g y).IsHomogeneous (chowDegree Q (e + 1)) :=
    isHomogeneous_specRest _ (h2 k n (e + 1) Q g hg) y
  rw [heq] at hG
  have hCN : (C c * normForm (R := E) (SecAlg QE y) (secCoord QE y)).IsHomogeneous
      (Module.finrank E (SecAlg QE y)) := by
    simpa using hN.C_mul c
  exact hCN.inj_right hG (mul_ne_zero (C_ne_zero.mpr hc) hN0)
end ChowSecDegree
end GroundTheory.Heights₂.Heights.Vertical
