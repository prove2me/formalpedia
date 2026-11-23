-- Prove2me | solution 1 for ReciprocityTheory.CA.isIntegral_quotient_of_isMaximal_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:55.266253+00:00
-- url     : https://prove2.me/submissions/6c12a2e7-9b87-4647-8a6b-0b0e84322150

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyMax

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open Polynomial IsLocalRing
variable {P : Type*} [CommRing P] [IsLocalRing P]
namespace ReciprocityTheory.CA
theorem _root_.solution {S : Type*} [CommRing S] [Algebra P S]
    [Algebra.FiniteType P S] (𝔑 : Ideal S) [𝔑.IsMaximal]
    (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) : Algebra.IsIntegral P (S ⧸ 𝔑) := by
  classical
  letI : Field (P ⧸ maximalIdeal P) := Ideal.Quotient.field _
  letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _
  letI : Algebra (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    (Ideal.quotientMap 𝔑 (algebraMap P S) h.ge).toAlgebra
  haveI : IsScalarTower P (P ⧸ maximalIdeal P) (S ⧸ 𝔑) := by
    first
    | exact IsScalarTower.of_algebraMap_eq (fun p => rfl)
    | exact IsScalarTower.of_algebraMap_eq (fun p => by simp [Ideal.quotientMap_mk])
  haveI : Algebra.FiniteType P (S ⧸ 𝔑) := by
    first
    | infer_instance
    | exact Algebra.FiniteType.of_surjective inferInstance (Ideal.Quotient.mkₐ P 𝔑)
        (Ideal.Quotient.mkₐ_surjective P 𝔑)
  haveI : Algebra.FiniteType (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    Algebra.FiniteType.of_restrictScalars_finiteType P _ _
  haveI : Module.Finite (P ⧸ maximalIdeal P) (S ⧸ 𝔑) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  haveI : Algebra.IsIntegral P (P ⧸ maximalIdeal P) := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_surjective (Ideal.Quotient.mkₐ P (maximalIdeal P))
        (Ideal.Quotient.mkₐ_surjective P _)
  exact Algebra.IsIntegral.trans (P ⧸ maximalIdeal P)
end ReciprocityTheory.CA
