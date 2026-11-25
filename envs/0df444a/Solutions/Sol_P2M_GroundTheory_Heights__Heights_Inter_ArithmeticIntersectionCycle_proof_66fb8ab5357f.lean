-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_proof_66fb8ab5357f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:48.620642+00:00
-- url     : https://prove2.me/submissions/330170cc-8b95-4bc4-80d0-eaa4bd3142bb

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsPrimeSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalSpanTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IdDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_isHorizontal_imageZ_iff_1028b5244437
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionCycle_charOf_imageZ_79e92b4a2bdd

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights.Inter
namespace ArithmeticIntersectionCycle
theorem _root_.solution (hHor : ArithmeticIntersectionHorizontal.Statement) (hVert : ArithmeticIntersectionVertical.Statement) (hPush : ArithmeticIntersectionDivisorPushforward.Statement)
    (hGP : GenericPointExists.Statement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    ArithmeticIntersectionCycle.Statement := by
  intro I hI n hn K _ ι _ K' _ ι' _ κ v P' G J L L' s α hv hP' hP hJ hL hLL' hs hsP
  classical

  have hex : ∀ W' : Ideal (MRing ι'), W'.IsPrime →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' := by
    intro W' hW'
    obtain ⟨G'⟩ := hGP K ι K' ι' v W' hW'
    obtain ⟨J', hJ', -⟩ := hEU G'.Φ (FibreBlock κ) (fibreIdx ι' κ)
    exact ⟨G', J', hJ'⟩
  let E : Ideal (MRing ι') → ℤ := fun W' =>
    if h : ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' then
      h.choose_spec.choose (fibreIdeal κ h.choose) 0 Fin.elim0 else 0
  have hE : ∀ W' : Ideal (MRing ι'), W'.IsPrime →
      ∃ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)),
        IsFieldIntersection J' ∧ E W' = J' (fibreIdeal κ G') 0 Fin.elim0 := by
    intro W' hW'
    have h := hex W' hW'
    exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec, by simp only [E, dif_pos h]⟩

  let T : Ideal (MRing ι) → ℝ := fun W =>
    if IsHorizontal W then I K ι W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)
  let T' : Ideal (MRing ι') → ℝ := fun W' =>
    if IsHorizontal W' then I K' ι' W' n L' else (geoNum n W' (fun j => (L' j).a) : ℝ) * Real.log (charOf W')
  have hterm : ∀ W' ∈ divSupp P' (rename v s), T' W' = if imageZ v W' ∈ divSupp (imageZ v P') s then (E W' : ℝ) * T (imageZ v W') else 0 := by
    intro W' hW'
    obtain ⟨G', J', hJ', hEW⟩ := hE W' hW'.1.isPrime
    by_cases hh : IsHorizontal W'
    · have hh' : IsHorizontal (imageZ v W') := (ArithmeticIntersectionCycle.isHorizontal_imageZ_iff v W').2 hh
      rcases hHor I hI n hn K ι K' ι' κ v P' L L' s α W' hv hP' hP hL hLL' hs hsP hW' hh with
        ⟨hm, he⟩ | ⟨hm, h0⟩
      · simp only [T', T, if_pos hh, if_pos hm, if_pos hh', he G' J' hJ', hEW]
      · simp only [T', if_pos hh, if_neg hm, h0]
    · have hh' : ¬ IsHorizontal (imageZ v W') := fun h => hh ((ArithmeticIntersectionCycle.isHorizontal_imageZ_iff v W').1 h)
      have ha : (fun j => (L' j).a) = fun j => pullDeg κ (L j).a := funext fun j => (hLL' j).1
      rcases hVert K ι K' ι' κ v P' n (fun j => (L j).a) s α W' hv hP' hP hs hsP hW' hh with
        ⟨hm, he⟩ | ⟨hm, h0⟩
      · simp only [T', T, if_neg hh, if_pos hm, if_neg hh', ArithmeticIntersectionCycle.charOf_imageZ]
        rw [ha, he G' J' hJ', hEW]
        push_cast
        ring
      · simp only [T', if_neg hh, if_neg hm]
        rw [ha, h0]
        simp

  have hfin' : (divSupp P' (rename v s)).Finite := divSupp_finite _ _
  have hfin : (divSupp (imageZ v P') s).Finite := divSupp_finite _ _
  have key : ∀ W ∈ hfin.toFinset,
      ∑ W' ∈ hfin'.toFinset.filter (fun W' => imageZ v W' = W),
        (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' =
        J (fibreIdeal κ G) 0 Fin.elim0 * multAt (imageZ v P' ⊔ Ideal.span {s}) W := by
    intro W hW
    have h := hPush K ι K' ι' κ v P' n G J s α W E hv hP' hP hJ hs hsP (hfin.mem_toFinset.1 hW)
      (fun W' hW' _ => hE W' hW'.1.isPrime)
    rw [finsum_mem_eq_finite_toFinset_sum _ (hfin'.subset fun x hx => hx.1)] at h
    rw [← h]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext W'
    simp [Set.Finite.mem_toFinset]

  show (∑ᶠ W' ∈ divSupp P' (rename v s), (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * T' W') =
    (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ∑ᶠ W ∈ divSupp (imageZ v P') s, (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℝ) * T W
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin', finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ∑ W' ∈ hfin'.toFinset, (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * T' W'
      = ∑ W' ∈ hfin'.toFinset, if imageZ v W' ∈ hfin.toFinset then
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') else 0 := by
        refine Finset.sum_congr rfl fun W' hW' => ?_
        rw [hterm W' (hfin'.mem_toFinset.1 hW')]
        simp only [Set.Finite.mem_toFinset]
        split_ifs <;> ring
    _ = ∑ W' ∈ hfin'.toFinset with imageZ v W' ∈ hfin.toFinset,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') := by
        rw [Finset.sum_filter]
    _ = ∑ W ∈ hfin.toFinset, ∑ W' ∈ hfin'.toFinset with imageZ v W' = W,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℝ) * E W' * T (imageZ v W') := by
        rw [Finset.sum_fiberwise_eq_sum_filter]
    _ = ∑ W ∈ hfin.toFinset, ((∑ W' ∈ hfin'.toFinset with imageZ v W' = W,
          (multAt (P' ⊔ Ideal.span {rename v s}) W' : ℤ) * E W' : ℤ) : ℝ) * T W := by
        refine Finset.sum_congr rfl fun W _ => ?_
        push_cast
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun W' hW' => ?_
        rw [(Finset.mem_filter.1 hW').2]
    _ = (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) *
          ∑ W ∈ hfin.toFinset, (multAt (imageZ v P' ⊔ Ideal.span {s}) W : ℝ) * T W := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun W hW => ?_
        rw [key W hW]
        push_cast
        ring
end ArithmeticIntersectionCycle
end GroundTheory.Heights₂.Heights.Inter
