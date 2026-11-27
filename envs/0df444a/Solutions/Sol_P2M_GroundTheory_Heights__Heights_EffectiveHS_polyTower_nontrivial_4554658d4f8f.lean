-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_EffectiveHS_polyTower_nontrivial_4554658d4f8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:55:05.981864+00:00
-- url     : https://prove2.me/submissions/365e7ea2-5b48-40e1-b02e-951677240841

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_MulTower_gen_mem_Vpp_c93286f36977

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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset
namespace GroundTheory.Heights₂.Heights.EffectiveHS
theorem _root_.solution :
    MvPolynomial.X 0 ∈ polyTower.W ∧ (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧
      mono (fun i => MvPolynomial.X i) (fun _ => 1) * (∏ i : Fin 0, Fin.elim0 i) * 1 ∈
        polyTower.Vpp 2 2 2 (fun i => MvPolynomial.X i) := by
  refine ⟨?_, MvPolynomial.X_ne_zero 0, ?_⟩
  · show _ ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 1
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_X ℚ 0
  · refine polyTower.gen_mem_Vpp (fun _ => 1) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) ?_
      (by simp) (by simp)
    show (1 : MvPolynomial (Fin 2) ℚ) ∈ MvPolynomial.homogeneousSubmodule (Fin 2) ℚ 0
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact MvPolynomial.isHomogeneous_one (Fin 2) ℚ
end GroundTheory.Heights₂.Heights.EffectiveHS
