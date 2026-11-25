-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_compact_reps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:58.665095+00:00
-- url     : https://prove2.me/submissions/44910c7a-f2a4-4a51-971f-96a80da65819

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ValAtLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnFrameA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
variable {N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {La : Type} [AddCommGroup La] (P : La →+ (Fin N → ℂ))
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    ∃ K : Set (Fin N → ℂ), IsCompact K ∧ ∀ z, ∃ w ∈ K, z - w ∈ P.range := by
  classical
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℝ (Set.range P)
  rw [hspan] at hbspan
  haveI : Finite b := hbli.finite
  haveI : Fintype b := Fintype.ofFinite b
  have hpre : ∀ j : b, ∃ x, P x = (j : Fin N → ℂ) := fun j => hbsub j.prop
  choose a ha using hpre
  refine ⟨(fun c : b → ℝ => ∑ j, c j • (j : Fin N → ℂ)) '' Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1),
    ?_, ?_⟩
  · exact (isCompact_univ_pi fun _ => isCompact_Icc).image
      (continuous_finset_sum _ fun j _ => (continuous_apply j).smul continuous_const)
  · intro z
    let B := Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
    have hBj : ∀ j, B j = (j : Fin N → ℂ) := fun j => by simp [B]
    have hz : ∑ j, B.repr z j • (j : Fin N → ℂ) = z := by
      simp_rw [← hBj]
      exact B.sum_repr z
    generalize B.repr z = r at hz ⊢
    refine ⟨∑ j, Int.fract (r j) • (j : Fin N → ℂ),
      ⟨fun j => Int.fract (r j), fun j _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩, rfl⟩, ?_⟩
    refine ⟨∑ j, ⌊r j⌋ • a j, ?_⟩
    rw [map_sum]
    conv_rhs => rw [← hz]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, ha j, ← sub_smul, Int.self_sub_fract, Int.cast_smul_eq_zsmul]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
