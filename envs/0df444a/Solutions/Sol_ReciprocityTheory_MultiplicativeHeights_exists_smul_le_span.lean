-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.exists_smul_le_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:23:29.098874+00:00
-- url     : https://prove2.me/submissions/2bf099a7-8e41-4a65-b7c3-2953b3341504

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegBB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_exists_smul_mem_span

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
open Matrix NumberField
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (b : Fin k → Fin r → K) (B : Submodule (𝓞 K) (Fin r → K)) (hB : B.FG)
    (hBb : ∀ x ∈ B, x ∈ Submodule.span K (Set.range b)) :
    ∃ D : 𝓞 K, D ≠ 0 ∧ ∀ x ∈ B, D • x ∈ Submodule.span (𝓞 K) (Set.range b) := by
  obtain ⟨s, hs⟩ := hB
  have hgen : ∀ g ∈ s, ∃ d : 𝓞 K, d ≠ 0 ∧ d • g ∈ Submodule.span (𝓞 K) (Set.range b) :=
    fun g hg => exists_smul_mem_span b g (hBb g (by rw [← hs]; exact Submodule.subset_span hg))
  choose! d hd0 hdm using hgen
  refine ⟨∏ g ∈ s, d g, Finset.prod_ne_zero_iff.2 hd0, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem d hg
    rw [ht, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hdm g hg)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hx
end ReciprocityTheory.MultiplicativeHeights
