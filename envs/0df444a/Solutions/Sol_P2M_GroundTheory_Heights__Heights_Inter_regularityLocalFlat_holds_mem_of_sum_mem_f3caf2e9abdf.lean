-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_regularityLocalFlat_holds_mem_of_sum_mem_f3caf2e9abdf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:58:58.572864+00:00
-- url     : https://prove2.me/submissions/9eab28ac-3343-42ad-a26b-be47cd140277

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PrimeComplMapLeNonZeroDivisorsQuot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_blockComponent
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isHomogeneous_of_isMultiHomogIdeal


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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
theorem _root_.solution {I : Ideal (MRing ι)} (hI : IsMultiHomogIdeal I) {β : Type*} (s : Finset β)
    (h : β → MRing ι) (d : β → K → ℕ) (hd : Set.InjOn d s) (hh : ∀ b ∈ s, IsMultiHomog (h b) (d b))
    (hsum : ∑ b ∈ s, h b ∈ I) : ∀ b ∈ s, h b ∈ I := by
  classical
  intro b hb
  obtain ⟨g, hgI, hg⟩ :=
    exists_blockComponent (isHomogeneous_of_isMultiHomogIdeal hI) (d b) Finset.univ hsum
  convert hgI using 1
  ext m
  rw [hg, coeff_sum]
  by_cases hm : coeff m (h b) = 0
  · rw [hm]
    split_ifs with hdeg
    · refine (Finset.sum_eq_zero fun b' hb' => ?_).symm
      by_contra hne
      have h1 := hh b' hb' m (mem_support_iff.mpr hne)
      have hbb : b' = b := hd hb' hb (funext fun k => (h1 k).symm.trans (hdeg k (Finset.mem_univ k)))
      exact hne (hbb ▸ hm)
    · rfl
  · have hdeg := hh b hb m (mem_support_iff.mpr hm)
    rw [if_pos (fun k _ => hdeg k), Finset.sum_eq_single b]
    · intro b' hb' hne
      by_contra h'
      exact hne (hd hb' hb (funext fun k => (hh b' hb' m (mem_support_iff.mpr h') k).symm.trans (hdeg k)))
    · intro h'
      exact absurd hb h'
end GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds
