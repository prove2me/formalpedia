-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.differentIdeal_multiplicity_map_algEquiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:04.829464+00:00
-- url     : https://prove2.me/submissions/f79b8487-a437-439f-89ec-f603f0a38373

import Mathlib.RingTheory.DedekindDomain.Different
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differents_Transport
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_differentIdeal_map_algEquiv_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
attribute [local instance] FractionRing.liftAlgebra
namespace QEC.Coding.AlgebraicGeometry
theorem _root_.solution
    (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsIntegrallyClosed A]
    [IsDedekindDomain B] [IsDedekindDomain C]
    [Algebra A B] [Algebra A C]
    [Module.IsTorsionFree A B] [Module.IsTorsionFree A C]
    (sigma : B ≃ₐ[A] C) (P : Ideal B) :
    multiplicity (Ideal.map sigma P) (differentIdeal A C) =
      multiplicity P (differentIdeal A B) := by
  calc
    multiplicity (Ideal.map sigma P) (differentIdeal A C) =
        multiplicity (Ideal.map sigma P)
          (Ideal.map sigma (differentIdeal A B)) := by
      rw [differentIdeal_map_algEquiv_eq A B C sigma]
    _ = multiplicity P (differentIdeal A B) := by
      exact multiplicity_map_eq
        (idealMapRingEquiv B C sigma.toRingEquiv)
end QEC.Coding.AlgebraicGeometry
