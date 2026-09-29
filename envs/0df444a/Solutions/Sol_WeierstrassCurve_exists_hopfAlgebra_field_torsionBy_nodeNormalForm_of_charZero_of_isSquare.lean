-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/a2097b1a-c99a-56ad-906b-7595ed9b0695

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare
import Theorems.Thm_MonoidAlgebra_exists_equiv_withConv_algHom_rootsOfUnity_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare

set_option maxHeartbeats 6400000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [Fact n.Prime]
    (d : K) (hd : d * d = c) :
    letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
    let W : WeierstrassCurve K := ⟨0, c, 0, 0, 0⟩
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra K A),
      Module.Finite K A ∧ Coalgebra.IsCocomm K A ∧
      ∃ eA : WithConv (A →ₐ[K] AlgebraicClosure K) ≃
            Submodule.torsionBy ℤ (W⁄(AlgebraicClosure K)).Point n,
        (∀ f g, eA (f * g) = eA f + eA g) ∧
        ∀ (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
          (f g : WithConv (A →ₐ[K] AlgebraicClosure K)),
          (∀ a : A, g a = σ (f a)) → eA g = σ • (eA f) := by
  letI : DecidableEq (AlgebraicClosure K) := Classical.decEq _
  haveI : NeZero n := ⟨(Fact.out : n.Prime).pos.ne'⟩
  refine ⟨MonoidAlgebra K (Multiplicative (ZMod n)), inferInstance, inferInstance,
    inferInstance, inferInstance, ?_⟩
  obtain ⟨et, het_add, het_gal⟩ :=
    WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_isSquare
      K c hc n d hd
  obtain ⟨eμ, heμ_mul, heμ_gal⟩ :=
    MonoidAlgebra.exists_equiv_withConv_algHom_rootsOfUnity_zmod K n
  refine ⟨eμ.trans et.symm, ?_, ?_⟩
  ·
    intro f g
    show et.symm (eμ (f * g)) = et.symm (eμ f) + et.symm (eμ g)
    apply et.injective
    rw [Equiv.apply_symm_apply, het_add, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, heμ_mul]
  ·
    intro σ f g hfg
    show et.symm (eμ g) = σ • et.symm (eμ f)
    apply et.injective
    rw [Equiv.apply_symm_apply]

    refine Subtype.ext (Units.ext ?_)
    rw [het_gal σ (et.symm (eμ f)), Equiv.apply_symm_apply]
    exact heμ_gal σ f g hfg

end S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_isSquare (solution)
