-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_isAlgebraic_adjoin_8f5520555759
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:34.829338+00:00
-- url     : https://prove2.me/submissions/611c9826-e590-40fb-a0b9-b7110303c524

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PMChartTrdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_MChartTrdeg_map_eq_zero_iff_8a5dd37f9c47

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
variable (P : Ideal (MRing ι F)) [P.IsPrime]
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
theorem _root_.solution (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    Algebra.IsAlgebraic (Algebra.adjoin (chartMap P u).range (Set.range fun k =>
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X ⟨k, u k⟩))))
      (FractionRing (MRing ι F ⧸ P)) := by
  set R := MRing ι F ⧸ P
  set L := FractionRing R
  set A₀ := (chartMap P u).range
  set S' := Algebra.adjoin A₀ (Set.range fun k => algebraMap R L (Ideal.Quotient.mk P (X ⟨k, u k⟩)))
  have hξS : ∀ v, algebraMap R L (Ideal.Quotient.mk P (X v)) ∈ S' := by
    intro v
    have hr : chartMap P u (X v) ∈ A₀ := AlgHom.mem_range_self _ _
    have hne : algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) ≠ 0 :=
      fun h => hu v.1 ((map_eq_zero_iff P _).1 h)
    have e : algebraMap R L (Ideal.Quotient.mk P (X v)) =
        chartMap P u (X v) * algebraMap R L (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩)) := by
      simp only [chartMap, aeval_X]
      exact (div_mul_cancel₀ _ hne).symm
    rw [e]
    exact S'.mul_mem (S'.algebraMap_mem (⟨_, hr⟩ : A₀)) (Algebra.subset_adjoin ⟨v.1, rfl⟩)
  have hRS : ∀ r : R, algebraMap R L r ∈ S' := by
    intro r
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    induction f using MvPolynomial.induction_on with
    | C c =>
      rw [show (Ideal.Quotient.mk P (C c) : R) = algebraMap F R c from rfl,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F A₀ L]
      exact S'.algebraMap_mem _
    | add f g hf hg => rw [map_add, map_add]; exact S'.add_mem hf hg
    | mul_X f i hf => rw [map_mul, map_mul]; exact S'.mul_mem hf (hξS i)
  let _ : CommRing S' := Subalgebra.toCommRing S'
  refine ⟨fun x => ?_⟩
  obtain ⟨a, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hd0 : algebraMap R L d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  refine ⟨Polynomial.C (⟨_, hRS d⟩ : S') * Polynomial.X - Polynomial.C (⟨_, hRS a⟩ : S'),
    fun h => hd0 ?_, ?_⟩
  · have := congrArg (Polynomial.coeff · 1) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte,
      one_ne_zero, Polynomial.coeff_zero] at this
    have h' := congrArg Subtype.val this
    simp only [Subalgebra.coe_zero, sub_zero] at h'
    exact h'
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    show algebraMap R L d * (algebraMap R L a / algebraMap R L d) - algebraMap R L a = 0
    rw [mul_comm, div_mul_cancel₀ _ hd0, sub_self]
end GroundTheory.Heights₂.Heights.FieldNumbers.MChartTrdeg
