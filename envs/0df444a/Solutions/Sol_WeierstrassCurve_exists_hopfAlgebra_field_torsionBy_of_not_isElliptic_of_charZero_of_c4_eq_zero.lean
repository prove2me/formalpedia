-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/f9a01b59-8b1b-5fc9-82b9-c79e1192388b

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero"

set_option maxHeartbeats 3200000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (W : WeierstrassCurve K) (hW : ¬ W.IsElliptic)
    (hc4 : W.c₄ = 0) (n : ℕ) [Fact n.Prime] :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _

  have hTorsTriv :=
    WeierstrassCurve.subsingleton_torsionBy_algClosure_point_of_not_isElliptic_of_charZero_of_c4_eq_zero
      K W hW hc4 n (Nat.Prime.ne_zero Fact.out)

  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨⟨fun _ => 0, fun _ => default, fun _ => Subsingleton.elim _ _,
    fun _ => @Subsingleton.elim _ hTorsTriv _ _⟩, ?_, ?_⟩
  · intro f g; exact @Subsingleton.elim _ hTorsTriv _ _
  · intro σ f g _; exact @Subsingleton.elim _ hTorsTriv _ _

end S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_of_not_isElliptic_of_charZero_of_c4_eq_zero (solution)
