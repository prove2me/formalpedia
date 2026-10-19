-- Prove2me | solution 1 for PermanentRollout.homogeneousMap_allTarget_rees_prefix_parameter_isSMulRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.813979+00:00
-- url     : https://prove2.me/submissions/95dc6840-6896-4836-95b9-adc566bb5b31

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
import Theorems.Thm_PermanentRollout_homogeneousMap_allTarget_reesCoordinate_quotient_isWeaklyRegular

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
    (j : ℕ) (hj : j ≤ k) :
    IsSMulRegular
      (MvPolynomial (Fin (k + 1)) ℂ ⧸
        Ideal.ofList
          ((List.ofFn
            (homogeneousMapAllTargetReesCoordinate F target e)).take j))
      (MvPolynomial.X (R := ℂ) (0 : Fin (k + 1))) := by
  classical
  let R := MvPolynomial (Fin (k + 1)) ℂ
  let z : R := MvPolynomial.X (0 : Fin (k + 1))
  let G : Fin k → R := homogeneousMapAllTargetReesCoordinate F target e
  let gp : Fin j → R :=
    fun i => G ⟨i.val, Nat.lt_of_lt_of_le i.isLt hj⟩
  let J : Ideal R := Ideal.span ({z} : Set R)
  have hmod : RingTheory.Sequence.IsWeaklyRegular (R ⧸ J)
      (List.ofFn fun i : Fin k => Ideal.Quotient.mk J (G i)) :=
    homogeneousMap_allTarget_reesCoordinate_quotient_isWeaklyRegular
      F target e he hF hzero
  have htake :
      List.ofFn (fun i : Fin j => Ideal.Quotient.mk J (gp i)) =
        (List.ofFn fun i : Fin k =>
          Ideal.Quotient.mk J (G i)).take j := by
    apply List.ext_getElem
    · simp [hj]
    · intro i hleft hright
      simp [gp]
  have hprefix : RingTheory.Sequence.IsWeaklyRegular (R ⧸ J)
      (List.ofFn fun i : Fin j => Ideal.Quotient.mk J (gp i)) := by
    rw [htake]
    have hsplit :
        (List.ofFn fun i : Fin k => Ideal.Quotient.mk J (G i)) =
          (List.ofFn fun i : Fin k =>
            Ideal.Quotient.mk J (G i)).take j ++
          (List.ofFn fun i : Fin k =>
            Ideal.Quotient.mk J (G i)).drop j :=
      (List.take_append_drop j _).symm
    exact (RingTheory.Sequence.isWeaklyRegular_append_iff (R ⧸ J)
      ((List.ofFn fun i : Fin k => Ideal.Quotient.mk J (G i)).take j)
      ((List.ofFn fun i : Fin k => Ideal.Quotient.mk J (G i)).drop j)).mp
      (hsplit ▸ hmod) |>.1
  have hspan :
      Ideal.ofList ((List.ofFn G).take j) =
        Ideal.span (Set.range gp) := by
    have hGtake : List.ofFn gp = (List.ofFn G).take j := by
      apply List.ext_getElem
      · simp [hj]
      · intro i hleft hright
        simp [gp]
    rw [← hGtake]
    change Ideal.span {x : R | x ∈ List.ofFn gp} =
      Ideal.span (Set.range gp)
    congr 1
    ext x
    simp
  rw [hspan]
  exact homogeneousMap_allRank_fin_hyperplane_isSMulRegular_of_quotient_weaklyRegular
    gp z (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin (k + 1))) hprefix
end PermanentRollout
