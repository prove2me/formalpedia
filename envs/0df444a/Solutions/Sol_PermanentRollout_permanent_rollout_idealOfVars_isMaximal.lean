-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_idealOfVars_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/00bdc625-c969-49e7-bb7a-b39d0c4631e6

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution (m : ℕ) :
    (MvPolynomial.idealOfVars (Fin m) ℂ).IsMaximal := by
  have hkernel :
      RingHom.ker
        (MvPolynomial.constantCoeff : MvPolynomial (Fin m) ℂ →+* ℂ) =
        MvPolynomial.idealOfVars (Fin m) ℂ := by
    ext f
    change MvPolynomial.coeff 0 f = 0 ↔
      f ∈ MvPolynomial.idealOfVars (Fin m) ℂ
    rw [← pow_one (MvPolynomial.idealOfVars (Fin m) ℂ),
      MvPolynomial.mem_pow_idealOfVars_iff']
    constructor
    · intro hf exponent hexponent
      have hezero : exponent = 0 :=
        (Finsupp.degree_eq_zero_iff exponent).mp
          (Nat.lt_one_iff.mp hexponent)
      simpa [hezero] using hf
    · intro hf
      exact hf 0 (by simp)
  rw [← hkernel]
  apply RingHom.ker_isMaximal_of_surjective
  intro a
  exact ⟨MvPolynomial.C a, MvPolynomial.constantCoeff_C _ a⟩
end PermanentRollout
