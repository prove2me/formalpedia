-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_C_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:46:14.690858+00:00
-- url     : https://prove2.me/submissions/3475f7d6-8c34-41bb-8ff1-559ac6e1cd34

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (c : ℂ) (Q : MvPolynomial (Fin ν × ι) ℂ) :
    fischer (C c) Q = c * starRingEnd ℂ (coeff 0 Q) := by
  have hsub : (C c : MvPolynomial (Fin ν × ι) ℂ).support ⊆ {0} := by
    intro A hA
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hA
    rw [Finset.mem_singleton]
    by_contra h
    exact hA (if_neg (fun e => h e.symm))
  rw [fischer_eq_sum (C c) Q {0} hsub, Finset.sum_singleton, MvPolynomial.coeff_C, if_pos rfl]
  simp [fw]
end ReciprocityTheory.PGsh
