-- Prove2me | solution 1 for ReciprocityTheory.PGsh.deriv_finsetProd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:21.827037+00:00
-- url     : https://prove2.me/submissions/05e087e7-717d-4bd3-ab47-223dc5bd683f

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

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
    (P : ι → A) :
    D (∏ k ∈ t, P k) = ∑ k₀ ∈ t, ∏ k ∈ t, (if k = k₀ then D (P k) else P k) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
    have h1 : ∏ k ∈ t, (if k = a then D (P k) else P k) = ∏ k ∈ t, P k :=
      Finset.prod_congr rfl fun k hk => if_neg fun h => ha (by rw [← h]; exact hk)
    have h2 : ∀ k₀ ∈ t, ∏ k ∈ insert a t, (if k = k₀ then D (P k) else P k) =
        P a * ∏ k ∈ t, (if k = k₀ then D (P k) else P k) := fun k₀ hk₀ => by
      rw [Finset.prod_insert ha, if_neg fun h => ha (by rw [h]; exact hk₀)]
    rw [Finset.prod_insert ha, Derivation.leibniz, ih, Finset.sum_insert ha,
      Finset.prod_insert ha, if_pos (rfl : a = a), h1, Finset.sum_congr rfl h2,
      smul_eq_mul, smul_eq_mul, Finset.mul_sum]
    ring
end ReciprocityTheory.PGsh
