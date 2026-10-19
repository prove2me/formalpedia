-- Prove2me | solution 1 for PermanentRollout.homogeneousLinearSliceIdeal_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/4668afeb-1708-4ea2-bd4b-be2189f2a0e1

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped LinearAlgebra.Projectivization
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution {t n : ℕ}
    (I : Ideal (MvPolynomial (Fin t) ℂ))
    (c : Fin n → Fin t → ℂ) (x : Fin t → ℂ) :
    homogeneousLinearSliceIdeal I (Fin.snoc c x) =
      homogeneousLinearSliceIdeal I c ⊔
        Ideal.span
          ({permanentRolloutLinearCoordinateCombination t x} :
            Set (MvPolynomial (Fin t) ℂ)) := by
  unfold homogeneousLinearSliceIdeal
  have hsnoc :
      (fun j : Fin (n + 1) =>
        permanentRolloutLinearCoordinateCombination t
          ((Fin.snoc c x : Fin (n + 1) → Fin t → ℂ) j)) =
      Fin.snoc
        (fun j => permanentRolloutLinearCoordinateCombination t (c j))
        (permanentRolloutLinearCoordinateCombination t x) := by
    funext j
    induction j using Fin.lastCases <;> simp
  rw [hsnoc, Fin.range_snoc, Ideal.span_insert]
  ac_rfl
end PermanentRollout
