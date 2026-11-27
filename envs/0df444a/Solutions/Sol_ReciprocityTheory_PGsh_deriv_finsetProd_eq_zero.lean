-- Prove2me | solution 1 for ReciprocityTheory.PGsh.deriv_finsetProd_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:32:54.957815+00:00
-- url     : https://prove2.me/submissions/f217fbae-0f9d-4305-8532-f4faaed7da90

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_deriv_finsetProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
namespace ReciprocityTheory.PGsh
theorem _root_.solution {ι : Type*} [DecidableEq ι] (D : Derivation R A A) (t : Finset ι)
    (P : ι → A) (h : ∀ k ∈ t, D (P k) = 0) : D (∏ k ∈ t, P k) = 0 := by
  rw [deriv_finsetProd]
  exact Finset.sum_eq_zero fun k₀ hk₀ => Finset.prod_eq_zero hk₀ (by simp [h k₀ hk₀])
end ReciprocityTheory.PGsh
