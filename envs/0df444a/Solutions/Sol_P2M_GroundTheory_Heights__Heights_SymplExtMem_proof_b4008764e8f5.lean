-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SymplExtMem_proof_b4008764e8f5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:06.987173+00:00
-- url     : https://prove2.me/submissions/31f197b0-40be-4ee4-8ca5-13d20e6fb0ff

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsSympl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PSymplExtMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_left_00cf8a2eada3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_omega_zero_right_3ac668c7eb0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_e_6d67875bd178
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_f_4ca89db14d4d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inl_0db009739d4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PSymplExtMem_row_inr_f2f09600dc08

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
open PSymplExtMem
namespace GroundTheory.Heights₂.Heights
namespace SymplExtMem
theorem _root_.solution (h1 : SymplOmegaMem.Statement) (h2 : SymplCons.Statement) :
    SymplExtMem.Statement := by
  intro R _ n α β γ δ Q hdet hQ
  rw [h1 R (Fin (n + 1))]
  have hQ' := (h1 R (Fin n) Q).1 hQ
  have hc := (h2 R n).2
  rintro (x | x) (y | y) <;> cases x using Fin.cases <;> cases y using Fin.cases <;>
    simp only [row_e, row_f, row_inl, row_inr, hc, hQ', omega_zero_left, omega_zero_right] <;>
    simp [Matrix.J, Matrix.one_apply, Fin.succ_ne_zero, Fin.succ_inj] <;>
    first
      | ring1
      | linear_combination hdet
      | linear_combination (-1 : R) * hdet
      | exact fun h => absurd (Eq.symm h) (Fin.succ_ne_zero _)
end SymplExtMem
end GroundTheory.Heights₂.Heights
