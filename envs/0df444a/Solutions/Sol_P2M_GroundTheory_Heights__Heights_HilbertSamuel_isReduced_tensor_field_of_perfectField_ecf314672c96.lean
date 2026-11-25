-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_field_of_perfectField_ecf314672c96
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:44.008984+00:00
-- url     : https://prove2.me/submissions/ec44def0-975f-4d95-a434-aa2e73e4e410

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeComplexRadical
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_formallyEtale_f3c416b86548

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial TensorProduct
noncomputable section
open scoped IntermediateField.algebraAdjoinAdjoin
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (K L F : Type*) [Field K] [PerfectField K]
    [Field L] [Algebra K L] [Algebra.EssFiniteType K L] [Field F] [Algebra K F] :
    IsReduced (L ⊗[K] F) := by
  classical
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K L
  let R := Algebra.adjoin K (s : Set L)
  let E := IntermediateField.adjoin K (s : Set L)

  have eR : R ≃ₐ[K] MvPolynomial s K :=
    (Subalgebra.equivOfEq R (Algebra.adjoin K (Set.range ((↑) : s → L))) (by simp [R])).trans hs.1.aevalEquiv.symm
  have hRF : IsDomain (R ⊗[K] F) :=
    ((Algebra.TensorProduct.comm K R F).toRingEquiv.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : F ≃ₐ[K] F) eR).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv (σ := s) K F).toRingEquiv)).toMulEquiv.isDomain

  have hT : IsDomain (E ⊗[R] (R ⊗[K] F)) := by
    letI : Algebra (R ⊗[K] F) (E ⊗[R] (R ⊗[K] F)) := Algebra.TensorProduct.rightAlgebra
    have := IsLocalization.tensorRight (R := R) (S := R ⊗[K] F) (A := E) (nonZeroDivisors R)
    refine IsLocalization.isDomain_of_le_nonZeroDivisors (R := R ⊗[K] F)
      (M := Algebra.algebraMapSubmonoid (R ⊗[K] F) (nonZeroDivisors R)) (E ⊗[R] (R ⊗[K] F)) ?_
    rintro _ ⟨r, hr, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero ?_
    intro h0
    have hinj : Function.Injective (algebraMap R (R ⊗[K] F)) :=
      Algebra.TensorProduct.includeLeft_injective (S := R) (RingHom.injective (algebraMap K F))
    exact nonZeroDivisors.ne_zero hr (hinj (by simpa using h0))

  have : IsDomain (E ⊗[K] F) :=
    (Algebra.TensorProduct.cancelBaseChange K R R E F).symm.toMulEquiv.isDomain

  have : Algebra.FormallyEtale E L := Algebra.FormallyEtale.of_isSeparable E L
  have : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp K E L
  have := isReduced_tensor_domain_of_formallyEtale E L (E ⊗[K] F)
  exact isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange K E E L F).symm
    (AlgEquiv.injective _)
end GroundTheory.Heights₂.Heights.HilbertSamuel
