-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_append_li
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:24:10.551802+00:00
-- url     : https://prove2.me/submissions/bcfff016-2c8b-46cd-abd6-e706b7280c21

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sdd_proj_eq_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open NumberField
variable {K : Type} [Field K] [NumberField K] {r e : ℕ}
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {k₀ k₁ : ℕ} (b₀ : Fin k₀ → Fin r → K) (c b₁ : Fin k₁ → Fin r → K)
    (hb₀cut : ∀ i, b₀ i ∈ cutSub K r e) (hb₀li : LinearIndependent K b₀)
    (hcb : ∀ j, projGe K r e (c j) = b₁ j) (hb₁li : LinearIndependent K b₁) :
    LinearIndependent K (Fin.append b₀ c) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_add] at hg
  simp only [Fin.append_left, Fin.append_right] at hg
  have hc' : ∀ j, cutProjK K r e (c j) = b₁ j := hcb
  have hb' : ∀ i, cutProjK K r e (b₀ i) = 0 := fun i => (sdd_proj_eq_zero_iff _).mpr (hb₀cut i)
  have h1 : ∑ j, g (Fin.natAdd k₀ j) • b₁ j = 0 := by
    have := congrArg (cutProjK K r e) hg
    simpa [map_add, map_sum, map_smul, hb', hc'] using this
  have h1' := Fintype.linearIndependent_iff.mp hb₁li _ h1
  have h0 : ∑ i, g (Fin.castAdd k₁ i) • b₀ i = 0 := by simpa [h1'] using hg
  have h0' := Fintype.linearIndependent_iff.mp hb₀li _ h0
  intro i
  exact Fin.addCases (fun i => h0' i) (fun j => h1' j) i
end ReciprocityTheory.MultiplicativeHeights
