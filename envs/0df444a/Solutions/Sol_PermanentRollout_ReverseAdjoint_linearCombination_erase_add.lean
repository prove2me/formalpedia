-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.linearCombination_erase_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/77e5b07c-6548-4253-831e-803d8edb2ebf

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι κ : Type*}
    (adjoints : κ →₀ MvPolynomial ι ℂ)
    (family : κ → MvPolynomial ι ℂ) (index : κ) :
    Finsupp.linearCombination (MvPolynomial ι ℂ) family
          (adjoints.erase index) +
        adjoints index * family index =
      Finsupp.linearCombination (MvPolynomial ι ℂ) family adjoints := by
  classical
  calc
    Finsupp.linearCombination (MvPolynomial ι ℂ) family
          (adjoints.erase index) + adjoints index * family index =
        Finsupp.linearCombination (MvPolynomial ι ℂ) family
          (adjoints.erase index) +
          Finsupp.linearCombination (MvPolynomial ι ℂ) family
            (Finsupp.single index (adjoints index)) := by
              simp [Finsupp.linearCombination_single]
    _ = Finsupp.linearCombination (MvPolynomial ι ℂ) family
          (adjoints.erase index +
            Finsupp.single index (adjoints index)) := by
              rw [map_add]
    _ = Finsupp.linearCombination (MvPolynomial ι ℂ) family adjoints := by
              rw [Finsupp.erase_add_single]
end PermanentRollout.ReverseAdjoint
