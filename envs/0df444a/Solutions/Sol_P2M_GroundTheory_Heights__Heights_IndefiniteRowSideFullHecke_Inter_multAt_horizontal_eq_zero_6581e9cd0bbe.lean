-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_multAt_horizontal_eq_zero_6581e9cd0bbe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:27.304741+00:00
-- url     : https://prove2.me/submissions/6dbe42fe-e44a-4834-9584-62130de77cb1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedG
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isMultiHomog_secOf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_secOf_not_mem


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
open Classical
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι}
    (hs : IsSectionOn P A s)
    (hind : ∀ (I : Family ι) (t : MRing ι), IsSectionOn P A t →
      recR I P (Fin.elim0 : Fin 0 → HermLine ι) A s = recR I P Fin.elim0 A t)
    {W₀ : Ideal (MRing ι)} (hW₀ : W₀ ∈ divSupp P s) (hh : IsHorizontal W₀) :
    (multAt (P ⊔ Ideal.span {s}) W₀ : ℝ) = 0 := by
  obtain ⟨a, hdeg, -, -⟩ := hs
  have hprime : W₀.IsPrime := hW₀.1.1.1
  have hle : P ⊔ Ideal.span {s} ≤ W₀ := hW₀.1.1.2
  choose i hi using hW₀.2
  have ht0 : secOf i a ∉ W₀ := secOf_not_mem hprime hi a
  have ht : IsSectionOn P A (secOf i a) :=
    ⟨a, hdeg, isMultiHomog_secOf i a, fun h => ht0 (le_sup_left.trans hle h)⟩
  have hnot : W₀ ∉ divSupp P (secOf i a) := fun h =>
    ht0 (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  let F : ℝ → Family ι := fun c W _ _ => if W = W₀ then c else 0
  have hFt : recR (F 1) P (Fin.elim0 : Fin 0 → HermLine ι) A (secOf i a) =
      recR (F 0) P Fin.elim0 A (secOf i a) := by
    unfold recR
    congr 1
    refine finsum_mem_congr rfl fun W hW => ?_
    have hne : W ≠ W₀ := fun h => hnot (h ▸ hW)
    simp [F, hne]
  have key := (hind (F 1) _ ht).trans (hFt.trans (hind (F 0) _ ht).symm)
  unfold recR at key
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s)] at key
  have hmem : W₀ ∈ (divSupp_finite P s).toFinset := (Set.Finite.mem_toFinset _).mpr hW₀
  have hsum := sub_left_inj.mp key
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single W₀ (fun W _ hne => by simp [F, hne]) (fun h => absurd hmem h)] at hsum
  simpa [F, hh] using hsum
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
