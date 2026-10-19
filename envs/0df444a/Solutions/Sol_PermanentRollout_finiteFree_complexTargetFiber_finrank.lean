-- Prove2me | solution 1 for PermanentRollout.finiteFree_complexTargetFiber_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/abf1aaa1-092a-456c-b01d-8743072c34d4

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_finiteFree_maximalFiber_finrank

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution
    {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [Algebra ℂ R] [Algebra ℂ S] [Algebra R S]
    [IsScalarTower ℂ R S] [Module.Free R S]
    (φ : R →ₐ[ℂ] ℂ) (hφ : Function.Surjective φ) :
    Module.finrank ℂ
      (S ⧸ (RingHom.ker φ.toRingHom).map (algebraMap R S)) =
        Module.finrank R S := by
  let p : Ideal R := RingHom.ker φ.toRingHom
  letI : p.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective φ.toRingHom hφ
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : IsScalarTower ℂ (R ⧸ p)
      (S ⧸ p.map (algebraMap R S)) :=
    IsScalarTower.of_algebraMap_eq (by
      intro c
      change Ideal.Quotient.mk (p.map (algebraMap R S))
          (algebraMap ℂ S c) =
        Ideal.Quotient.mk (p.map (algebraMap R S))
          (algebraMap R S (algebraMap ℂ R c))
      rw [IsScalarTower.algebraMap_apply ℂ R S c])
  have hres : Module.finrank ℂ (R ⧸ p) = 1 := by
    calc
      Module.finrank ℂ (R ⧸ p) = Module.finrank ℂ ℂ :=
        (Ideal.quotientKerAlgEquivOfSurjective hφ).toLinearEquiv.finrank_eq
      _ = 1 := Module.finrank_self ℂ
  have htower := Module.finrank_mul_finrank ℂ (R ⧸ p)
    (S ⧸ p.map (algebraMap R S))
  change Module.finrank ℂ
    (S ⧸ p.map (algebraMap R S)) = Module.finrank R S
  rw [hres, one_mul] at htower
  exact htower.symm.trans (finiteFree_maximalFiber_finrank p)
end PermanentRollout
