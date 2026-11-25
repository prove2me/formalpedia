-- Prove2me | solution 1 for ReciprocityTheory.CA.isMaximal_comap_of_isMaximal_of_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:25.535235+00:00
-- url     : https://prove2.me/submissions/dec1c57c-46f2-44e8-aa00-2af399899f71

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyMax
import Theorems.Thm_ReciprocityTheory_CA_isIntegral_quotient_of_isMaximal_of_comap_eq

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
theorem _root_.solution {S' S : Type*} [CommRing S'] [CommRing S]
    [Algebra P S'] [Algebra P S] [Algebra S' S] [IsScalarTower P S' S] [Algebra.FiniteType P S]
    (𝔑 : Ideal S) [𝔑.IsMaximal] (h : 𝔑.comap (algebraMap P S) = maximalIdeal P) :
    (𝔑.comap (algebraMap S' S)).IsMaximal := by
  haveI := isIntegral_quotient_of_isMaximal_of_comap_eq 𝔑 h
  haveI : Algebra.IsIntegral S' (S ⧸ 𝔑) := by
    first
    | exact Algebra.IsIntegral.tower_top P
    | exact Algebra.IsIntegral.tower_top (R := P)
  letI : Field (S ⧸ 𝔑) := Ideal.Quotient.field _
  have hbot := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := S') (⊥ : Ideal (S ⧸ 𝔑))
  have heq : (⊥ : Ideal (S ⧸ 𝔑)).comap (algebraMap S' (S ⧸ 𝔑)) = 𝔑.comap (algebraMap S' S) := by
    ext y
    rw [Ideal.mem_comap, Ideal.mem_bot, Ideal.mem_comap]
    first
    | exact Ideal.Quotient.eq_zero_iff_mem
    | (rw [IsScalarTower.algebraMap_apply S' S (S ⧸ 𝔑), Ideal.Quotient.algebraMap_eq]
       exact Ideal.Quotient.eq_zero_iff_mem)
  rw [← heq]
  exact hbot
end ReciprocityTheory.CA
