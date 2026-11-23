-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.nu_eq_zero_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:03:42.106044+00:00
-- url     : https://prove2.me/submissions/f10b993e-14f8-492c-b358-34d3e879aa6a

import Definitions.Def_ReciprocityTheory_ReducedBases_GsInnerBOfLt
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsBoundedBasis
import Definitions.Def_ReciprocityTheory_ReducedBases_LatticeReduction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution (b : Fin d → E) (c : Fin d → ℝ) (j : Fin d) (h : ∀ l, j ≤ l → c l = 0) :
    nu b c j = 0 := by
  unfold nu
  apply Finset.sum_eq_zero
  intro l _
  rcases lt_or_ge l j with hlj | hjl
  · have h0 : ⟪gs b j, b l⟫_ℝ = 0 := by
      first
      | exact gramSchmidt_inv_triangular ℝ b hlj
      | exact gramSchmidt_inv_triangular b hlj
    simp [mu, h0]
  · simp [h l hjl]
end ReciprocityTheory.ReducedBases.T2
