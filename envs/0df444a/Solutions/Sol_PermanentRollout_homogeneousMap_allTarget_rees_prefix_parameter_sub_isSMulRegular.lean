-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_prefix_parameter_sub_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/440951a9-5924-48b5-a449-688ae68fb09f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_homogeneous_linear_sub_constant_isSMulRegular
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesCoordinate_isHomogeneous
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_rees_prefix_parameter_isSMulRegular

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators Topology Pointwise
open Filter Asymptotics
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PermanentRollout
theorem _root_.solution
    {k : ℕ} (F : Fin k → MvPolynomial (Fin k) ℂ)
    (target : Fin k → ℂ) (e : ℕ) (he : 0 < e)
    (hF : ∀ i, (F i).IsHomogeneous e)
    (hzero : ∀ point : Fin k → ℂ,
      (∀ i, MvPolynomial.eval point (F i) = 0) ↔ point = 0)
    (j : ℕ) (hj : j ≤ k) (a : ℂ) :
    IsSMulRegular
      (MvPolynomial (Fin (k + 1)) ℂ ⧸
        Ideal.ofList
          ((List.ofFn
            (homogeneousMapAllTargetReesCoordinate F target e)).take j))
      (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1)) -
        MvPolynomial.C a) := by
  apply homogeneousMap_allTarget_homogeneous_linear_sub_constant_isSMulRegular
    (Ideal.ofList
      ((List.ofFn
        (homogeneousMapAllTargetReesCoordinate F target e)).take j))
  · change
      (Ideal.span
        {p : MvPolynomial (Fin (k + 1)) ℂ |
          p ∈ (List.ofFn
            (homogeneousMapAllTargetReesCoordinate F target e)).take j}).IsHomogeneous _
    apply Ideal.homogeneous_span
    intro p hp
    have hpfull : p ∈
        List.ofFn (homogeneousMapAllTargetReesCoordinate F target e) :=
      List.mem_of_mem_take hp
    obtain ⟨i, rfl⟩ := (List.mem_ofFn.mp hpfull)
    exact ⟨e,
      homogeneousMap_allTarget_reesCoordinate_isHomogeneous F target e hF i⟩
  · exact MvPolynomial.isHomogeneous_X ℂ 0
  · exact homogeneousMap_allTarget_rees_prefix_parameter_isSMulRegular
      F target e he hF hzero j hj
end PermanentRollout
