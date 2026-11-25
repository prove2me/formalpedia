-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_finite_mapExpand_723755a99971
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:50.523611+00:00
-- url     : https://prove2.me/submissions/5bcf399b-7c9f-4a4f-b94d-368d09ba1dbd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_NoetherCharPLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open Polynomial
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (k k' : Type*) [Field k] [Field k'] [Algebra k k']
    [FiniteDimensional k k'] (σ : Type*) [Finite σ] (q : ℕ) (hq : 0 < q) :
    ((MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k k')).comp
      (MvPolynomial.expand q)).toRingHom.Finite := by
  set θ := (MvPolynomial.mapAlgHom (σ := σ) (Algebra.ofId k k')).comp (MvPolynomial.expand q)
  let : Algebra (MvPolynomial σ k) (MvPolynomial σ k') := θ.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial σ k) (MvPolynomial σ k') :=
    IsScalarTower.of_algebraMap_eq fun x => (θ.commutes x).symm
  have hX : ∀ i, IsIntegral (MvPolynomial σ k) (MvPolynomial.X i : MvPolynomial σ k') := by
    intro i
    refine IsIntegral.of_pow hq ?_
    have : (MvPolynomial.X i : MvPolynomial σ k') ^ q =
        algebraMap (MvPolynomial σ k) (MvPolynomial σ k') (MvPolynomial.X i) := by
      change _ = θ (MvPolynomial.X i)
      simp [θ]
    rw [this]
    exact isIntegral_algebraMap
  have : Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ k') := by
    constructor
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
      have h1 : IsIntegral k (algebraMap k' (MvPolynomial σ k') a) :=
        (Algebra.IsIntegral.isIntegral (R := k) a).map (IsScalarTower.toAlgHom k k' _)
      rw [MvPolynomial.algebraMap_eq] at h1
      exact h1.tower_top
    | add f g hf hg => exact hf.add hg
    | mul_X f i hf => exact hf.mul (hX i)
  have : Algebra.FiniteType k (MvPolynomial σ k') :=
    Algebra.FiniteType.trans (S := k') inferInstance inferInstance
  have : Algebra.FiniteType (MvPolynomial σ k) (MvPolynomial σ k') :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  exact Algebra.IsIntegral.finite
end GroundTheory.Heights₂.Heights.FieldNumbers
