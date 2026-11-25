-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_GenSESStep_mem_of_map_mem_344b3ce95714
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:27:53.95845+00:00
-- url     : https://prove2.me/submissions/531946d8-9f33-494b-9de1-d1c0f922115b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGenSESStep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_KleimanNefness_AlgCechSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGenSESStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
variable {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M]
  [IsScalarTower S (MRingOver S ι) M] {𝓜 : (K → ℤ) → Submodule S M}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
theorem _root_.solution {M' : Type*} [AddCommGroup M'] [Module (MRingOver S ι) M'] [Module S M']
    [IsScalarTower S (MRingOver S ι) M'] {𝓜' : (K → ℤ) → Submodule S M'} (h𝓜' : KH.IsMGraded S ι 𝓜')
    (h𝓜 : KH.IsMGraded S ι 𝓜) {g : M' →ₗ[MRingOver S ι] M} (hg : KH.IsMGradedMap S ι 𝓜' 𝓜 g)
    (hinj : Function.Injective g) {c : K → ℤ} {m' : M'} (hm : g m' ∈ 𝓜 c) : m' ∈ 𝓜' c := by
  classical
  have key : ∃ y ∈ 𝓜' c, g m' - g y ∈ ⨆ (j) (_ : j ≠ c), 𝓜 j := by
    have hx : m' ∈ ⨆ j, 𝓜' j := by
      rw [h𝓜'.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun x => ∃ y ∈ 𝓜' c, g x - g y ∈ ⨆ (j) (_ : j ≠ c), 𝓜 j)
      𝓜' hx ?_ ?_ ?_
    · intro j x hx
      by_cases hj : j = c
      · subst hj
        exact ⟨x, hx, by rw [sub_self]; exact zero_mem _⟩
      · refine ⟨0, zero_mem _, ?_⟩
        rw [map_zero, sub_zero]
        exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hg j x hx))
    · exact ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
    · intro x₁ x₂ h₁ h₂
      obtain ⟨y₁, hy₁, e₁⟩ := h₁
      obtain ⟨y₂, hy₂, e₂⟩ := h₂
      refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
      have : g (x₁ + x₂) - g (y₁ + y₂) = (g x₁ - g y₁) + (g x₂ - g y₂) := by
        simp only [map_add]
        abel
      rw [this]
      exact add_mem e₁ e₂
  obtain ⟨y, hy, hd⟩ := key
  have hc : g m' - g y ∈ 𝓜 c := sub_mem hm (hg c y hy)
  have h0 : g m' - g y = 0 := Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep c) _ hc hd
  rw [sub_eq_zero] at h0
  rw [hinj h0]
  exact hy
end GroundTheory.Heights₂.Heights.HilbertSamuel.GenSESStep
