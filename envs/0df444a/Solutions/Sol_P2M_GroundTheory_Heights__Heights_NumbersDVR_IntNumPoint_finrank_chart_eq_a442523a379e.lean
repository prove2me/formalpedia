-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_finrank_chart_eq_a442523a379e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:57.632271+00:00
-- url     : https://prove2.me/submissions/aa213254-7e4f-4a14-ad7a-0ce3e379972c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_cls_apply_7066b61ef8ff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_chartProd_ne_zero_728a4ef52d77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_mul_of_isMultiHomog_db1b22d71340
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_dehom_eq_zero_of_mem_chartIdeal_c19722018421
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_mem_chartIdeal_of_dehom_eq_zero_3eb777d45518

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
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
theorem _root_.solution (V : Ideal (MRing ι F)) (hV : IsMultiProjPrime V) (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V)
    (hfin : haveI := hV.isPrime; FiniteDimensional F (FieldNumbers.homFracDegZero V)) :
    haveI := hV.isPrime
    Module.finrank F (MRing ι F ⧸ ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) =
      Module.finrank F (FieldNumbers.homFracDegZero V) := by
  haveI := hV.isPrime
  set H := FieldNumbers.homFracDegZero V
  let ρ := Ideal.Quotient.liftₐ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) (dehom V i)
    (fun a ha => dehom_eq_zero_of_mem_chartIdeal i hi hV.multiHomog ha)
  have hρ : ∀ f, ρ (Ideal.Quotient.mk _ f) = dehom V i f := fun f => rfl
  have hinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).2 fun a ha => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hρ] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (mem_chartIdeal_of_dehom_eq_zero i hi ha)
  have hmemρ : ∀ f, dehom V i f ∈ ρ.range := fun f => ⟨Ideal.Quotient.mk _ f, hρ f⟩
  have hdH : ∀ f, dehom V i f ∈ H := by
    intro f
    have : (dehom V i).range ≤ H.toSubalgebra := by
      rw [dehom, aeval_range]
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin F _
        ⟨blockWeight ι p, X p, X ⟨p.1, i p.1⟩, isWeightedHomogeneous_X (R := F) _ _,
          isWeightedHomogeneous_X (R := F) _ _, hi p.1, rfl⟩
    exact this ⟨f, rfl⟩
  have hle : ρ.range ≤ H.toSubalgebra := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hdH f
  let E : IntermediateField F (FractionRing (MRing ι F ⧸ V)) :=
    ρ.range.toIntermediateField fun x hx =>
      ρ.range.inv_mem_of_algebraic (x := ⟨x, hx⟩)
        ((IntermediateField.isAlgebraic_iff (x := (⟨x, hle hx⟩ : H))).1 (IsAlgebraic.of_finite F _))
  have hHE : H ≤ E := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨b, f, g, hf, hg, hgV, rfl⟩
    have h1 := dehom_mul_of_isMultiHomog i hi hf
    have h2 := dehom_mul_of_isMultiHomog i hi hg
    rw [← cls_apply, ← cls_apply, ← h1, ← h2, mul_div_mul_right _ _ (chartProd_ne_zero i hi b),
      div_eq_mul_inv]
    exact E.mul_mem (hmemρ f) (E.inv_mem (hmemρ g))
  have heq : ρ.range = H.toSubalgebra := le_antisymm hle fun x hx => hHE hx
  rw [(AlgEquiv.ofInjective ρ hinj).toLinearEquiv.finrank_eq, heq,
    IntermediateField.finrank_eq_finrank_subalgebra]
end GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
