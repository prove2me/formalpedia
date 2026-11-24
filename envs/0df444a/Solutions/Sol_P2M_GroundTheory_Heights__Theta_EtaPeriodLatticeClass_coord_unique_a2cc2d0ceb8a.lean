-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:52.68394+00:00
-- url     : https://prove2.me/submissions/ef9ed14e-d303-48ac-b1d2-9018205ab61b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups
open GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
namespace GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
theorem _root_.solution {τ : ℍ} {m n m' n' : ℤ}
    (h : (m : ℂ) + n * (τ : ℂ) = m' + n' * (τ : ℂ)) : m = m' ∧ n = n' := by
  have him := congr_arg Complex.im h
  have hre := congr_arg Complex.re h
  simp at him hre
  have hn : n = n' := by
    rcases him with h | h
    · exact_mod_cast h
    · exact absurd h τ.im_pos.ne'
  subst hn
  refine ⟨?_, rfl⟩
  exact_mod_cast (by linarith : (m : ℝ) = m')
end GroundTheory.Heights₂.Theta.EtaPeriodLatticeClass
