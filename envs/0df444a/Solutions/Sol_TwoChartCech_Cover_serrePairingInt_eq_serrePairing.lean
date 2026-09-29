-- Prove2me | solution 1 for TwoChartCech.Cover.serrePairingInt_eq_serrePairing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/fecb1348-79b0-56b3-90a4-630cfadd15e1

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechSerrePairingInt
import Definitions.Def_AlgebraicCurve_SerrePairing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TwoChartCech_Cover_serrePairingInt_eq_serrePairing

set_option autoImplicit false

universe u w

theorem solution
    {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar k F]
    [∀ v : AlgebraicCurve.Place k F, v.DCoordGenerates] [Nontrivial Ω[F⁄k]]
    [AlgebraicCurve.HasCanonicalDivisor (K := k) (F := F)] [AlgebraicCurve.HasPrincipalDivisors k F]
    (hRT : AlgebraicCurve.ResidueTheorem k F)
    {S₀ S₁ : Set (AlgebraicCurve.Place k F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (𝒰 : TwoChartCech.Cover.{u, u} k) {ι : Type w} [Fintype ι]
    (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ψ : 𝒰.A01 →ₐ[k] F)
    (hψ : ∀ s : 𝒰.A01, ψ s ∈ AlgebraicCurve.lSpaceOn (S₀ ∩ S₁) (0 : AlgebraicCurve.Divisor k F))
    (e1 : 𝒰.structureSheaf.H1 →ₗ[k] AlgebraicCurve.cechH1 S₀ S₁ (0 : AlgebraicCurve.Divisor k F))
    (he1 : ∀ s : 𝒰.A01, e1 (Submodule.Quotient.mk s) = Submodule.Quotient.mk ⟨ψ s, hψ s⟩)
    (eΩ : 𝒰.kaehler.H0 →ₗ[k] ↥(AlgebraicCurve.regularDifferentials k F))
    (p : ι ↪ AlgebraicCurve.Place k F) (hp : Set.range p = S₀ᶜ)
    (hres : ∀ (i : ι) (s : 𝒰.A01) (ω : 𝒰.kaehler.H0),
      (Λ i).residue (s • 𝒰.kaehler.r0 ω.val.1) =
        AlgebraicCurve.kaehlerResidueTerm ((eΩ ω : ↥(AlgebraicCurve.regularDifferentials k F)) : Ω[F⁄k])
          (AlgebraicCurve.diagonalHom k F (ψ s)) (p i))
    (ω : 𝒰.kaehler.H0) (x : 𝒰.structureSheaf.H1) :
    𝒰.serrePairingInt Λ hv ω x = AlgebraicCurve.serrePairing hRT hcover (eΩ ω) (e1 x) := by
  classical
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [TwoChartCech.Cover.serrePairingInt_apply_mk, he1, AlgebraicCurve.serrePairing_apply_mk_eq_finsum_ite,
    finsum_eq_sum_of_support_subset (s := Finset.univ.map p) _ ?_, Finset.sum_map]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : p i ∉ S₀ := by
      have h' : p i ∈ Set.range p := ⟨i, rfl⟩
      rw [hp] at h'
      exact h'
    rw [if_neg hi, hres i s ω]
  · intro v hv
    rw [Finset.coe_map, Finset.coe_univ, Set.image_univ, hp]
    intro hvS
    exact hv (if_pos hvS)

end S_TwoChartCech_Cover_serrePairingInt_eq_serrePairing
end P2MW
export P2MW.S_TwoChartCech_Cover_serrePairingInt_eq_serrePairing (solution)
