-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SpanBundleDim_proof_5e9e6e286e45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:05:58.680779+00:00
-- url     : https://prove2.me/submissions/acb75c41-f683-48fc-9e6f-5c7657e40a46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPointIdealMultiProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegGe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSpanBundleTrdegLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PCutRegular
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpanBundleDim
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRegular_relDim_eq_natCast_iff_cb89d927b72d


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
namespace SpanBundleDim
theorem _root_.solution (h : PointIdealMultiProj.Statement) (hge : SpanBundleTrdegGe.Statement)
    (hle : SpanBundleTrdegLe.Statement) : SpanBundleDim.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hy hdim M i G hi hG c a H hc hH hGH Φ _ _ s hs
  have hprime : IsMultiProjPrime (projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) := by
    let : Algebra F Φ := ((algebraMap Ω Φ).comp (algebraMap F Ω)).toAlgebra
    refine h F Φ (Option K) (bundleIdx ι M) _ ?_
    rintro (_ | k)
    · obtain ⟨l, hl⟩ : ∃ l, G l ⟨0, hi⟩ ≠ 0 := by
        by_contra! h0
        exact hG.ne_zero ⟨0, hi⟩ (funext h0)
      refine ⟨l, fun h0 => hl ?_⟩
      have hsum : ∑ j, G l j • s j = 0 := by
        rw [← h0]
        simp only [projCoord]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Algebra.smul_def, mul_comm, Matrix.mulVec, dotProduct, Pi.single_apply]
      exact Fintype.linearIndependent_iff.1 hs.linearIndependent _ hsum ⟨0, hi⟩
    · obtain ⟨j, hj⟩ := hy.relevant k
      refine ⟨j, fun h0 => hj ?_⟩
      have hy0 : y ⟨k, j⟩ = 0 := (FaithfulSMul.algebraMap_injective Ω Φ) (by simpa [projCoord] using h0)
      simp [pointIdeal, RingHom.mem_ker, pointConeMap, hy0]
  refine ⟨hprime, ?_⟩
  have := hprime.isPrime
  have := hy.isPrime
  have hty : Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : Cardinal) := by
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F] at hdim
    exact Cardinal.toENat_eq_natCast.1 (WithBot.coe_injective (by simpa using hdim))
  have htz : Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
      (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) =
      ((e + Fintype.card K + i : ℕ) : Cardinal) := by
    apply le_antisymm
    · simpa [hty] using hle F Ω K ι y M i G c a H hc hH hGH Φ s
    · simpa [hty] using hge F Ω K ι y M i G hG Φ s hs
  apply (FieldNumbers.CutRegular.relDim_eq_natCast_iff _ (e + i - 1)).2
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F, htz, Fintype.card_option,
    show e + i - 1 + (Fintype.card K + 1) = e + Fintype.card K + i by omega]
  simp
end SpanBundleDim
end GroundTheory.Heights₂.Heights.NumbersDVR
