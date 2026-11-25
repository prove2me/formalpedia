-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_colon_isPrime_e41b03fc9ee7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:06:51.854883+00:00
-- url     : https://prove2.me/submissions/b7261f9f-b887-45bc-8142-ab97acb3f8f5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_isHomogeneous_of_multiHomog_9ab68c09e1f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_exists_multiHomog_of_mem_88b7c3ef52b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_mem_colon_iff_a8700efb8128
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_multiHomog_colon_ca90d2ed2e72

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution [∀ k, Fintype (ι k)] {J : Ideal (MRing ι F)}
    (hJ : IsMultiHomogIdeal J) (hJt : J ≠ ⊤) :
    ∃ (c : K → ℕ) (s : MRing ι F), IsMultiHomog s c ∧ s ∉ J ∧
      (J.colon (Ideal.span {s})).IsPrime ∧ IsMultiHomogIdeal (J.colon (Ideal.span {s})) := by
  let 𝒮 : Set (Ideal (MRing ι F)) :=
    {P | ∃ s, (∃ i, s ∈ lexGrading ι F i) ∧ s ∉ J ∧ P = J.colon (Ideal.span {s})}
  have hne : 𝒮.Nonempty :=
    ⟨_, 1, ⟨0, SetLike.GradedOne.one_mem⟩, (Ideal.ne_top_iff_one J).mp hJt, rfl⟩
  have hnoeth : IsNoetherian (MRing ι F) (MRing ι F) := inferInstance
  obtain ⟨P, hP, hmax⟩ := set_has_maximal_iff_noetherian.mpr hnoeth 𝒮 hne
  obtain ⟨s, ⟨i, hsi⟩, hsJ, hPs⟩ := hP
  subst hPs
  have hs0 : s ≠ 0 := fun h => hsJ (h ▸ J.zero_mem)
  obtain ⟨c, hc⟩ := exists_multiHomog_of_mem hsi hs0
  have hmh := multiHomog_colon hJ hc
  have hcolon := isHomogeneous_of_multiHomog hmh
  have hprime : (J.colon (Ideal.span {s})).IsPrime := by
    refine hcolon.isPrime_of_homogeneous_mem_or_mem ?_ ?_
    · rw [Ne, Ideal.eq_top_iff_one, mem_colon_iff, one_mul]
      exact hsJ
    · intro x y hx _ hxy
      by_cases hxP : x ∈ J.colon (Ideal.span {s})
      · exact Or.inl hxP
      right
      obtain ⟨i', hxi⟩ := hx
      have hxs : x * s ∉ J := fun h => hxP (mem_colon_iff.mpr h)
      have hle : J.colon (Ideal.span {s}) ≤ J.colon (Ideal.span {x * s}) := by
        intro f hf
        rw [mem_colon_iff] at hf ⊢
        rw [show f * (x * s) = x * (f * s) by ring]
        exact J.mul_mem_left x hf
      have heq : J.colon (Ideal.span {s}) = J.colon (Ideal.span {x * s}) := by
        by_contra hne'
        exact hmax _ ⟨x * s, ⟨i' + i, SetLike.mul_mem_graded hxi hsi⟩, hxs, rfl⟩
          (lt_of_le_of_ne hle hne')
      rw [heq, mem_colon_iff, show y * (x * s) = x * y * s by ring]
      exact mem_colon_iff.mp hxy
  exact ⟨c, s, hc, hsJ, hprime, hmh⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
