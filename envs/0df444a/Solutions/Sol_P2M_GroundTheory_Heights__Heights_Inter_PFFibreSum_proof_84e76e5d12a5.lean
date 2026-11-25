-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PFFibreSum_proof_84e76e5d12a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:29:06.166667+00:00
-- url     : https://prove2.me/submissions/01d65f01-1fdd-4df8-986f-b45384ed89b4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreBij
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFFibreMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isMultiHomog_iff_weighted_ebc17bcac6a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_aeval_baseSubst_c8867875a98c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_baseSubst_isMultiHomog_30eea56ab449

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
namespace PFFibreSum
theorem _root_.solution (hFD : FibreDimStatement) (hBij : PFFibreBij.Statement) (hMult : PFFibreMult.Statement) :
    PFFibreSum.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G J N s a hv hP' hP hJ hNa hs hsP
  classical
  have hV : IsProjVarF (fibreIdeal κ G) (r + 1) := hFD K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hmem : ∀ g : MRing ι', baseSubst κ G g ∈ fibreIdeal κ G ↔ g ∈ P' := by
    intro g
    rw [fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
  have hsec : IsRatSection (fibreIdeal κ G) (fibreDeg κ (N (Fin.last r)).a) (baseSubst κ G s) 1 := by
    refine ⟨fun k => a k.1, 0, baseSubst_isMultiHomog G hs,
      (isMultiHomog_iff_weighted _ _).mpr (isWeightedHomogeneous_one _ _), fun h => hsP ((hmem s).mp h),
      fun h1 => hV.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun k => ?_⟩
    simp [fibreDeg, hNa]
  have hb' : J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) =
      cycEval (fun W => J W r (fun j => fibreDeg κ (N (Fin.castSucc j)).a))
        (ratDiv (fibreIdeal κ G) (baseSubst κ G s) 1) := by
    rw [← hJ.2 _ r _ _ _ _ hV hsec]
    exact congrArg _ (Fin.snoc_init_self (α := fun _ => FibreBlock κ → ℤ) (fun j => fibreDeg κ (N j).a)).symm
  have hdiv1 : divCycle (fibreIdeal κ G) 1 = 0 := by
    ext W
    simp only [divCycle, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
    rw [if_neg]
    simp [divSupp, Ideal.span_singleton_one, Ideal.minimalPrimes_top]
  set L := fun j : Fin r => fibreDeg κ (N (Fin.castSucc j)).a
  set V := fibreIdeal κ G
  set f := baseSubst κ G s
  have hD : ∀ Q, (divCycle V f Q : ℝ) = if Q ∈ divSupp V f then (multAt (V ⊔ Ideal.span {f}) Q : ℝ) else 0 := by
    intro Q
    simp only [divCycle, Finsupp.ofSupportFinite_coe]
    split_ifs <;> simp

  have hR : ((cycEval (fun W => J W r L) (ratDiv V f 1) : ℤ) : ℝ) =
      ∑ᶠ Q ∈ divSupp V f, (multAt (V ⊔ Ideal.span {f}) Q : ℝ) * (J Q r L : ℝ) := by
    rw [ratDiv, hdiv1, Finsupp.mapRange_zero, sub_zero, cycEval,
      Finsupp.sum_mapRange_index (fun _ => zero_mul _), Finsupp.sum, Int.cast_sum,
      finsum_mem_def]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hsupp : Function.support (fun Q => (divCycle V f Q : ℝ) * (J Q r L : ℝ)) ⊆ ↑(divCycle V f).support := by
      intro Q hQ
      rw [Function.mem_support] at hQ
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hQ (by rw [h0]; simp)
    rw [← finsum_eq_sum_of_support_subset _ hsupp]
    congr 1
    funext Q
    rw [hD]
    by_cases hQ : Q ∈ divSupp V f <;> simp [hQ, Set.indicator]

  have hL : ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then (J (fibreOf κ G W) r L : ℝ) else 0) =
      ∑ᶠ W ∈ {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'},
        (multAt (P' ⊔ Ideal.span {s}) W : ℝ) * (J (fibreOf κ G W) r L : ℝ) := by
    rw [finsum_mem_def, finsum_mem_def]
    congr 1
    funext W
    by_cases hW : W ∈ divSupp P' s <;> by_cases hH : IsHorizontal W ∧ imageZ v W = imageZ v P' <;>
      simp [Set.indicator, hW, hH]
  rw [hb', hR, hL]
  refine finsum_mem_eq_of_bijOn (fibreOf κ G) (hBij K ι K' ι' κ v P' d (d + r + 1) G s hv hP' hP) ?_
  rintro W ⟨hW, hH, hI⟩
  rw [hMult K ι K' ι' κ v P' d (d + r + 1) G s W hv hP' hP hW hH hI]
end PFFibreSum
end GroundTheory.Heights₂.Heights.Inter
