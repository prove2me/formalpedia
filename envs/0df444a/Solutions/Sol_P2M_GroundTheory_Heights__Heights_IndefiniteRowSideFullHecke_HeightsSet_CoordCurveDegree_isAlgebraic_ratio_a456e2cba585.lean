-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_isAlgebraic_ratio_a456e2cba585
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:31:22.575585+00:00
-- url     : https://prove2.me/submissions/34ce7ec5-ba58-411c-88d2-32e64fafc192

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_trdeg_range_bf53ac89959e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_algebraicIndependent_C_mul_X_edadd42bd2c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_injective_subst_50c463cf8efa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 Algebra
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
theorem _root_.solution {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (p : Σ k, ι k) : IsAlgebraic ℚ (y p / y ⟨p.1, c p.1⟩) := by
  by_contra hr
  set r := y p / y ⟨p.1, c p.1⟩
  set u : K → MvPolynomial K Ω := fun k ↦ C (y ⟨k, c k⟩) * X k
  have hu := algebraicIndependent_C_mul_X _ hc
  have hr1 : AlgebraicIndependent ℚ (fun _ : Unit ↦ r) := algebraicIndependent_unique_type_iff.mpr hr
  have h1 := AlgebraicIndependent.sumElim_comp hr1 hu

  set v : K ⊕ Unit → MvPolynomial K Ω := Sum.elim u fun _ ↦ C (y p) * X p.1
  have hv : AlgebraicIndependent ℚ v := by
    rw [algebraicIndependent_iff_injective_aeval] at h1 ⊢
    have e : (aeval v : MvPolynomial (K ⊕ Unit) ℚ →ₐ[ℚ] _) =
        (aeval (Sum.elim u (algebraMap Ω (MvPolynomial K Ω) ∘ fun _ : Unit ↦ r))).comp
          (aeval (Sum.elim (fun k ↦ X (Sum.inl k)) fun _ : Unit ↦ X (Sum.inr ()) * X (Sum.inl p.1))) := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      rcases i with k | w
      · simp [v]
      · simp only [v, u, r, AlgHom.comp_apply, aeval_X, Sum.elim_inr, Sum.elim_inl, map_mul,
          Function.comp_apply, MvPolynomial.algebraMap_eq]
        rw [← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc p.1)]
    rw [e, AlgHom.coe_comp]
    exact h1.comp (injective_subst p.1)

  let w : K ⊕ Unit → (coneMapQ y).range := fun i ↦ ⟨v i, by
    rcases i with k | w
    · exact ⟨X ⟨k, c k⟩, by simp [coneMapQ, v, u]⟩
    · exact ⟨X p, by simp [coneMapQ, v]⟩⟩
  have hw : AlgebraicIndependent ℚ w := AlgebraicIndependent.of_comp (coneMapQ y).range.val hv
  have hle : Cardinal.toENat (Cardinal.mk (K ⊕ Unit)) ≤ Cardinal.toENat (trdeg ℚ (coneMapQ y).range) :=
    Cardinal.toENat.monotone' hw.cardinalMk_le_trdeg
  rw [trdeg_range hP] at hle
  simp only [Cardinal.mk_fintype, map_natCast] at hle
  have h' : Fintype.card (K ⊕ Unit) ≤ Fintype.card K := by exact_mod_cast hle
  rw [Fintype.card_sum, Fintype.card_unit] at h'
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
