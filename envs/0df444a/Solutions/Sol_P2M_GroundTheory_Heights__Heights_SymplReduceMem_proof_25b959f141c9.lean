-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplReduceMem_proof_25b959f141c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:20.954656+00:00
-- url     : https://prove2.me/submissions/ef274984-3b8d-4743-aabd-ad3971d7ac29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplReduceMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_sub_smul_c8100a0683da
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_omega_tail_a426f24c6159
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_2a53475047d0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_succ_e_dec9e46caacf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_J_e_succ_ad8be0cda494
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplReduceMem_reduce_row_8b4c0b15e8b8

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
open Matrix
open PSymplReduceMem
namespace GroundTheory.Heights₂.Heights
namespace SymplReduceMem
theorem _root_.solution (h1 : SymplOmegaMem.Statement) (h2 : SymplCons.Statement) :
    SymplReduceMem.Statement := by
  intro n H hH he
  have hω := (h1 ℝ (Fin (n + 1)) H).1 hH
  rw [h1 ℝ (Fin n) (symplReduce H)]
  intro a b
  rw [reduce_row, reduce_row, omega_sub_smul, omega_tail h2, omega_tail h2, omega_tail h2,
    omega_tail h2, hω, hω, hω, hω, J_succ, J_succ_e, J_e_succ]
  simp only [J, fromBlocks_apply₁₁, Matrix.zero_apply]
  field_simp
  ring
end SymplReduceMem
end GroundTheory.Heights₂.Heights
