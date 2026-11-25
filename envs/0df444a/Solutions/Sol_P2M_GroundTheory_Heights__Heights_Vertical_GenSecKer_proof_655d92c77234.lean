-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_proof_655d92c77234
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:53:19.221534+00:00
-- url     : https://prove2.me/submissions/66828600-7898-45d8-b9a8-c51e960ff715

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsGenSecKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PGenSecKer
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_GenSecKer_ker_eq_d460a27c2b3a

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
open MvPolynomial Cardinal
noncomputable section
namespace GroundTheory.Heights₂.Heights.Vertical
namespace GenSecKer
theorem _root_.solution (h₁ : SecAlgField.Statement) (h₂ : ConeDimOfChowForm.Statement) :
    GenSecKer.Statement := by
  intro k _ n e Q g hQ hg
  have : Q.IsPrime := hQ.isPrime
  set I := secIdeal (Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))))
      (genPar k e n) with hI
  have hfield : IsField (MvPolynomial (Fin n) (GenParField k e n) ⧸ I) := h₁ k n e Q g hQ hg
  have hsec : ∀ i, secForm (genPar k e n) i ∈ I := fun i => by
    rw [hI]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  have hchart : chartForm (genPar k e n) - 1 ∈ I := by
    rw [hI]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hQI : Q.map (MvPolynomial.map (algebraMap k (GenParField k e n))) ≤ I := by
    rw [hI]
    exact le_sup_left.trans le_sup_left
  let x : Fin n → MvPolynomial (Fin n) (GenParField k e n) ⧸ I := fun j => Ideal.Quotient.mk I (X j)
  have hmk : (aeval x : MvPolynomial (Fin n) (GenParField k e n) →ₐ[GenParField k e n] _) =
      Ideal.Quotient.mkₐ (GenParField k e n) I :=
    MvPolynomial.algHom_ext fun j => by rw [aeval_X]; rfl
  have hlin : ∀ c : Fin n → GenParField k e n, Ideal.Quotient.mk I (linForm c) =
      ∑ j, algebraMap (GenParField k e n) (MvPolynomial (Fin n) (GenParField k e n) ⧸ I) (c j) * x j := by
    intro c
    show Ideal.Quotient.mkₐ (GenParField k e n) I (linForm c) = _
    rw [← hmk]
    simp [linForm, aeval_X]
  have hR1 : ∀ i : Fin e, ∑ j, algebraMap (GenParField k e n) (MvPolynomial (Fin n) (GenParField k e n) ⧸ I)
      (genPar k e n (.inl (i, j))) * x j = 0 := by
    intro i
    rw [← hlin, Ideal.Quotient.eq_zero_iff_mem]
    exact hsec i
  have hR2 : ∑ j, algebraMap (GenParField k e n) (MvPolynomial (Fin n) (GenParField k e n) ⧸ I)
      (genPar k e n (.inr j)) * x j = 1 := by
    rw [← hlin, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hchart
  have hker : (Ideal.Quotient.mk I).comp (MvPolynomial.map (algebraMap k (GenParField k e n))) =
      ((aeval x : MvPolynomial (Fin n) k →ₐ[k] _) : MvPolynomial (Fin n) k →+* _) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.coe_comp, Function.comp_apply, map_C, RingHom.coe_coe, aeval_C]
      rw [IsScalarTower.algebraMap_apply k (GenParField k e n)
        (MvPolynomial (Fin n) (GenParField k e n) ⧸ I)]
      rfl
    · intro j
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, RingHom.coe_coe, aeval_X]
      rfl
  have hQ0 : ∀ q ∈ Q, (aeval x : MvPolynomial (Fin n) k →ₐ[k] _) q = 0 := by
    intro q hq
    have h1 := RingHom.congr_fun hker q
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h1
    rw [← h1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hQI (Ideal.mem_map_of_mem _ hq))
  have hgen : ∀ z : MvPolynomial (Fin n) (GenParField k e n) ⧸ I,
      ∃ p : MvPolynomial (Fin n) (GenParField k e n), aeval x p = z := fun z => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨p, by rw [hmk]; rfl⟩
  rw [hker]
  exact GenSecKer.ker_eq hfield Q (h₂ k n (e + 1) Q g hQ hg) x hgen hR1 hR2 hQ0
end GenSecKer
end GroundTheory.Heights₂.Heights.Vertical
