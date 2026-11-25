-- Prove2me | solution 1 for ReciprocityTheory.CA.height_add_height_maximal_quotient_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:08:54.588554+00:00
-- url     : https://prove2.me/submissions/27d9e66a-845a-458b-8dab-3d980aef8c0c

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_Integral
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Theorems.Thm_ReciprocityTheory_CA_height_add_height_map_eq_mvPolynomial_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
universe u
namespace ReciprocityTheory.CA
theorem _root_.solution (K : Type*) [Field K] (N : ℕ)
    (𝔔 : Ideal (MvPolynomial (Fin N) K)) [𝔔.IsPrime]
    (𝔪 : Ideal (MvPolynomial (Fin N) K ⧸ 𝔔)) [h𝔪 : 𝔪.IsMaximal] :
    𝔔.height + 𝔪.height = N := by
  haveI : (𝔪.comap (Ideal.Quotient.mk 𝔔)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : 𝔔 ≤ 𝔪.comap (Ideal.Quotient.mk 𝔔) := fun x hx =>
    Ideal.mem_comap.2 (by rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact 𝔪.zero_mem)
  have h := height_add_height_map_eq_mvPolynomial_field K N 𝔔 (𝔪.comap (Ideal.Quotient.mk 𝔔)) hle
  rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
end ReciprocityTheory.CA
