-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:21.581633+00:00
-- url     : https://prove2.me/submissions/e4aa8177-a76c-476a-bd11-4f7e412cf509

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight

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
theorem _root_.solution (P Q : MvPolynomial (Fin ν × ι) ℂ) (S : Finset (Fin ν × ι →₀ ℕ))
    (hS : P.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), P.support ⊆ T →
      ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A
        = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : coeff A P = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ P.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_left _ hx)
    _ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm
end ReciprocityTheory.PGsh
