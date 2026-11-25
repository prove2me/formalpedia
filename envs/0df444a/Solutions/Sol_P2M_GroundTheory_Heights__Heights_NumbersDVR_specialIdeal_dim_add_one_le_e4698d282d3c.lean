-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_specialIdeal_dim_add_one_le_e4698d282d3c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:21.756361+00:00
-- url     : https://prove2.me/submissions/fccdc4e1-a6c0-4dfe-bcd4-15e608a7e15d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagProjSpecialDimSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagProjSpecialDim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type*} {ι : K → Type*} (P : Ideal (MvPolynomial (Σ k, ι k) O)) [P.IsPrime]
    (hPC : P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) = ⊥) :
    ringKrullDim (MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) ⧸
        P.map (MvPolynomial.map (IsLocalRing.residue O))) + 1 ≤
      ringKrullDim (MvPolynomial (Σ k, ι k) O ⧸ P) := by
  set φ : MvPolynomial (Σ k, ι k) O →+* MvPolynomial (Σ k, ι k) (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  set g := (Ideal.Quotient.mk (P.map φ)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, hker]
  have e1 := (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)
  set r : MvPolynomial (Σ k, ι k) O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 := (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P
    (Ideal.span {(C ϖ : MvPolynomial (Σ k, ι k) O)}))
  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MvPolynomial (Σ k, ι k) O) := h0
    rw [hPC, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rwa [ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle
end GroundTheory.Heights₂.Heights.NumbersDVR
