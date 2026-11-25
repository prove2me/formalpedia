-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_proof_d2fd3db9293e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:22.22988+00:00
-- url     : https://prove2.me/submissions/e00bf77d-7e3a-4c86-8df8-b4c611ea4e54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PAffineChartTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_179a6d344b31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_aeval_genPt_eq_zero_iff_813a9fa835eb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_transcendental_bb27ef9817ff
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_trdeg_eq_of_isFractionRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
open GroundTheory.Heights₂.Heights.AffineChartTrdeg
variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
namespace GroundTheory.Heights₂.Heights.AffineChartTrdeg
theorem _root_.solution : AffineChartTrdeg.Statement := by
  intro F _ n d P _ j hP hdim hj
  set R := MvPolynomial (Fin n) F ⧸ P
  set K := FractionRing R
  set ξ := genPt P
  set A' := Algebra.adjoin F (Set.range fun m => ξ m * (ξ j)⁻¹)
  have hξ : ξ j ≠ 0 := fun h => hj ((aeval_genPt_eq_zero_iff P (X j)).1 (by simpa using h))

  have hK : Algebra.trdeg F K = ((d + 1 : ℕ) : Cardinal) := by
    have : Algebra.FiniteType F R :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P)
        (Ideal.Quotient.mkₐ_surjective F P)
    rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) K]
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F] at hdim
    have h2 : (Algebra.trdeg F R).toENat = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdim
    exact Cardinal.toENat_eq_natCast.mp h2

  set S := Algebra.adjoin A' (Set.range fun _ : Unit => ξ j)
  have hξS : ∀ m, ξ m ∈ S := by
    intro m
    have hr : ξ m * (ξ j)⁻¹ ∈ A' := Algebra.subset_adjoin ⟨m, rfl⟩
    have : ξ m = ξ m * (ξ j)⁻¹ * ξ j := by field_simp
    rw [this]
    exact S.mul_mem (S.algebraMap_mem (⟨_, hr⟩ : A')) (Algebra.subset_adjoin ⟨(), rfl⟩)
  have hRS : ∀ r : R, algebraMap R K r ∈ S := by
    intro r
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← aeval_genPt]
    induction f using MvPolynomial.induction_on with
    | C c =>
      rw [aeval_C, IsScalarTower.algebraMap_apply F A' K]
      exact S.algebraMap_mem _
    | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
    | mul_X f i hf => rw [map_mul, aeval_X]; exact S.mul_mem hf (hξS i)

  have halg : Algebra.IsAlgebraic S K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : algebraMap R K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨Polynomial.C ⟨_, hRS b⟩ * Polynomial.X - Polynomial.C ⟨_, hRS a⟩, fun h => hb0 ?_, ?_⟩
    · have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte,
        one_ne_zero, Polynomial.coeff_zero] at this
      have h' := congrArg Subtype.val this
      simp only [Subalgebra.coe_sub, Subalgebra.coe_zero, sub_zero] at h'
      exact h'
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      show algebraMap R K b * (algebraMap R K a / algebraMap R K b) - algebraMap R K a = 0
      rw [mul_comm, div_mul_cancel₀ _ hb0, sub_self]

  have h1 : Algebra.trdeg A' K = 1 := by
    have hind : AlgebraicIndependent A' (fun _ : Unit => ξ j) :=
      algebraicIndependent_unique_type_iff.mpr (transcendental P hP.isHomog j hj)
    have hb : IsTranscendenceBasis A' (fun _ : Unit => ξ j) :=
      hind.isTranscendenceBasis_iff_isAlgebraic.mpr halg
    rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_unit, Nat.cast_one]

  have : FaithfulSMul A' K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul F A' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A').injective
  have hadd := trdeg_add_eq F A' (A := K)
  rw [h1, hK] at hadd
  have hfin : Algebra.trdeg F A' < Cardinal.aleph0 :=
    lt_of_le_of_lt le_self_add (by rw [hadd]; exact Cardinal.natCast_lt_aleph0)
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hk] at hadd ⊢
  norm_cast at hadd ⊢
  omega
end GroundTheory.Heights₂.Heights.AffineChartTrdeg
