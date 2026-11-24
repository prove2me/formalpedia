-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpecialDimBound_proof_548075edbce9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:43.725137+00:00
-- url     : https://prove2.me/submissions/d018dac3-d403-439a-9ea0-927b61197030

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialDimBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_withBotENat_lt_of_add_one_le_110602cf25ee

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
open MvPolynomial
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SpecialDimBound
theorem _root_.solution : SpecialDimBound.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  have := hP.multiProj.isPrime
  set φ : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

  set g : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk (specialIdeal P)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, specialIdeal, ← hφdef,
      Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]
  have e1 : MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) ≃+*
      MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)

  set r : MRing ι O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 : (MRing ι O ⧸ P) ⧸ Ideal.span {r} ≃+* MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
    (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P _)

  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h0
    rw [hP.noTorsion, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hr : r ∈ nonZeroDivisors (MRing ι O ⧸ P) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rw [hP.dim, ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle
  exact withBotENat_lt_of_add_one_le hle
end SpecialDimBound
end GroundTheory.Heights₂.Heights.NumbersDVR
