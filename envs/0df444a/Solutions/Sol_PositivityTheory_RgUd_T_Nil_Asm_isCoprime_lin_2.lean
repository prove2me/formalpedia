-- Prove2me | solution 2 for PositivityTheory.RgUd.T.Nil.Asm.isCoprime_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:33.253072+00:00
-- url     : https://prove2.me/submissions/34d08f3e-44b1-4991-a63c-a996d13ac178

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_CompactOrbits_NilpotentOrbits_NilpotentHypotheses_AevalProdLinearFactors
import Theorems.Thm_PositivityTheory_RgUd_T_Nil_Asm_lin_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Asm
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace PositivityTheory.RgUd.T.Nil.Asm
theorem _root_.solution (α β γ : ℂ) (h : β - γ * α ≠ 0) : IsCoprime (X - C α) (C β - C γ * X) := by
  refine ⟨C (γ / (β - γ * α)), C (1 / (β - γ * α)), ?_⟩
  rw [lin_comb]
  have e1 : γ / (β - γ * α) - 1 / (β - γ * α) * γ = 0 := by ring
  rw [e1, map_zero, zero_mul, add_zero]
  have e2 : (γ / (β - γ * α)) * (-α) + (1 / (β - γ * α)) * β = 1 := by
    field_simp
    ring
  rw [e2, map_one]
end PositivityTheory.RgUd.T.Nil.Asm
