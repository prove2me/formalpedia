-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceReducedAway_proof_6d8d1ec040f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:30.471674+00:00
-- url     : https://prove2.me/submissions/96a926aa-199a-4642-8a60-aedb3770d9db

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceReducedAwayZariski
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceReducedAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_eval_ne_zero_of_isOpen_pi_53a6727c2b58

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
open MvPolynomial Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace SliceReducedAway
theorem _root_.solution (hZ : SliceReducedAwayZariski.Statement) :
    SliceReducedAway.Statement := by
  intro n d J q hJ
  obtain ⟨F, hF, hgood⟩ := hZ n d J q hJ
  let e : Matrix (Fin d) (Fin n) ℂ → (Fin d × Fin n → ℂ) := fun L ij => L ij.1 ij.2
  let φ : (Fin d × Fin n → ℂ) → Matrix (Fin d) (Fin n) ℂ := fun y => Matrix.of fun i j => y (i, j)
  have he : Continuous e := continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2
  have hφ : Continuous φ :=
    continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
  refine ⟨{L | eval (e L) F ≠ 0}, ?_, ?_, fun L hL => hgood L hL⟩
  · exact isOpen_ne_fun ((MvPolynomial.continuous_eval F).comp he) continuous_const
  · rw [dense_iff_inter_open]
    rintro U hU ⟨L₀, hL₀⟩
    obtain ⟨y, hyU, hyF⟩ :=
      exists_eval_ne_zero_of_isOpen_pi hF (hU.preimage hφ) ⟨e L₀, hL₀⟩
    exact ⟨φ y, hyU, hyF⟩
end SliceReducedAway
end GroundTheory.Heights₂.Heights
