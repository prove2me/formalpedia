-- Prove2me | solution 1 for WeierstrassCurve.exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.822295+00:00
-- url     : https://prove2.me/submissions/2584dc35-2b8c-53eb-800b-e4819bd84748

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_WeierstrassCurve_exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare
import Theorems.Thm_HopfAlgebra_exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare

set_option maxHeartbeats 6400000
open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine.Point

theorem solution
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0) (n : ℕ) [Fact n.Prime]
    (hnsq : ¬ IsSquare c) :
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
  obtain ⟨δ, hδ, et, het_add, het_gal⟩ :=
    WeierstrassCurve.exists_equiv_torsionBy_nodeNormalForm_rootsOfUnity_of_not_isSquare
      K c hc n hnsq
  obtain ⟨A, hCR, hHA, hFin, hCocomm, eμ, heμ_mul, heμ_gal⟩ :=
    HopfAlgebra.exists_withConv_algHom_equiv_rootsOfUnity_quadraticTwist
      K c hc hnsq n δ hδ
  letI : CommRing A := hCR
  letI : HopfAlgebra K A := hHA
  refine ⟨A, hCR, hHA, hFin, hCocomm, eμ.trans et.symm, ?_, ?_⟩
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
    obtain ⟨heμ_eq, heμ_neg⟩ := heμ_gal σ f g hfg
    obtain ⟨het_eq, het_neg⟩ := het_gal σ (et.symm (eμ f))

    have hcases : σ δ = δ ∨ σ δ = -δ := by
      have hsq : (σ δ) ^ 2 = δ ^ 2 := by
        rw [← map_pow σ δ 2, sq, hδ, σ.commutes c, ← hδ, ← sq]
      have hprod : (σ δ - δ) * (σ δ + δ) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hprod with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (eq_neg_of_add_eq_zero_left h)
    rcases hcases with hpos | hneg
    ·
      rw [het_eq hpos, Equiv.apply_symm_apply]; exact heμ_eq hpos
    ·
      have h1 := het_neg hneg; rw [Equiv.apply_symm_apply] at h1
      have h2 := heμ_neg hneg
      have hσne : σ (((eμ f : (AlgebraicClosure K)ˣ) : AlgebraicClosure K)) ≠ 0 := by
        simp only [ne_eq, map_eq_zero]; exact Units.ne_zero _
      exact mul_right_cancel₀ hσne (h2.trans h1.symm)

end S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare
end P2MW
export P2MW.S_WeierstrassCurve_exists_hopfAlgebra_field_torsionBy_nodeNormalForm_of_charZero_of_not_isSquare (solution)
