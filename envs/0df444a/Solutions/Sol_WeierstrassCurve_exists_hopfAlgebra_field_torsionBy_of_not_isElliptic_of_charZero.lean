-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/c897265f-f83d-54c2-9e87-96126f50ab00

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero
import Theorems.Thm_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option maxHeartbeats 1600000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (hW : ¬ W.IsElliptic)
    (n : ℕ) [Fact n.Prime] :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by
  by_cases hc4 : W.c₄ = 0
  · exact WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero
      K W hW hc4 n
  · exact WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_ne_zero
      K W hW hc4 n

end S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero (solution)
