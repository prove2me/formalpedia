-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenericFibreDrop_proof_17e85410d2f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:18.663255+00:00
-- url     : https://prove2.me/submissions/3924ab96-0d38-4afe-a104-898f29b352cd

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsFibreCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenericFibreDrop
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_height_add_ringKrullDim_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace GroundTheory.Heights₂.Heights.Vertical
namespace GenericFibreDrop
theorem _root_.solution : GenericFibreDrop.Statement := by
  intro O _ _ _ F _ _ _ n P P' f hP hP'C hfP hP'
  let A := MvPolynomial (Fin n) O
  let T := MvPolynomial (Fin n) F
  let M : Submonoid A := (nonZeroDivisors O).map (C : O →+* A)
  have hφ : (algebraMap A T) = MvPolynomial.map (algebraMap O F) := rfl
  have : IsLocalization M T := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hP'p : P'.IsPrime := hP'.1.1
  have hPP' : P ≤ P' := le_sup_left.trans hP'.1.2
  have hfP' : f ∈ P' := hP'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hdisj' : Disjoint (M : Set A) (P' : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨o, ho, rfl⟩ hmem
    have h1 : o ∈ P'.comap (C : O →+* A) := hmem
    rw [hP'C, Ideal.mem_bot] at h1
    exact nonZeroDivisors.ne_zero ho h1
  have hdisj : Disjoint (M : Set A) (P : Set A) :=
    Set.disjoint_of_subset_right hPP' hdisj'

  let I : Ideal T := P.map (algebraMap A T)
  let I' : Ideal T := P'.map (algebraMap A T)
  have hI : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P hP hdisj
  have hI' : I'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P' hP'p hdisj'
  have hII' : I ≤ I' := Ideal.map_mono hPP'

  let Q : Ideal (A ⧸ P) := P'.map (Ideal.Quotient.mk P)
  have hQ : Q.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hQne : Q ≠ ⊥ := by
    intro h
    have h1 : Ideal.Quotient.mk P f ∈ Q := Ideal.mem_map_of_mem _ hfP'
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hfP h1
  have hQ1 : Q.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hP') ?_
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQne)
    simpa using this

  let M' : Submonoid (A ⧸ P) := Algebra.algebraMapSubmonoid (A ⧸ P) M
  have hQdisj : Disjoint (M' : Set (A ⧸ P)) (Q : Set (A ⧸ P)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have h1 : Ideal.Quotient.mk P a ∈ Q := hmem
    rw [Ideal.mem_quotient_iff_mem hPP'] at h1
    exact Set.disjoint_left.1 hdisj' ha h1
  have hh := IsLocalization.height_map_of_disjoint (S := T ⧸ I) M' Q hQdisj
  have hmap : Q.map (algebraMap (A ⧸ P) (T ⧸ I)) = I'.map (Ideal.Quotient.mk I) := by
    simp only [Q, I', Ideal.map_map]
    rfl
  rw [hmap, hQ1] at hh
  have _ : (I'.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

  have key := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F
    (I'.map (Ideal.Quotient.mk I))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hII')] at key
  show ringKrullDim (T ⧸ I) = ringKrullDim (T ⧸ I') + 1
  rw [← key, add_comm]
  rfl
end GenericFibreDrop
end GroundTheory.Heights₂.Heights.Vertical
