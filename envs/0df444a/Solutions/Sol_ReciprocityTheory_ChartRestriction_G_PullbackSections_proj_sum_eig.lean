-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.PullbackSections.proj_sum_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:33:42.971917+00:00
-- url     : https://prove2.me/submissions/fc769d9f-5d41-41e3-97cf-085e551c7a88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_LieBridgeB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_aevalS_eig
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_eval_lagr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open Polynomial
variable {K S M O ι : Type} [Field K] [CharZero K] [CommRing S] [Algebra K S] [AddCommGroup M] [Module S M]
  [CommRing O] [Fintype ι] [DecidableEq ι] (ρ : O →+* Module.End S M) (χ : ι → O →+* K) (α : O)
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution (hα : Function.Injective fun τ => χ τ α) (mm : ι → M)
    (hmm : ∀ τ, IsEigV ρ (χ τ) (mm τ)) (τ : ι) : proj ρ χ α τ (∑ τ', mm τ') = mm τ := by
  rw [map_sum]
  have key : ∀ τ', proj ρ χ α τ (mm τ') = if τ = τ' then mm τ' else 0 := by
    intro τ'
    have hm := hmm τ' α
    unfold proj
    rw [aevalS_eig (ρ α) hm, aeval_map_algebraMap, aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval,
      eval_lagr (fun τ => χ τ α) hα]
    split_ifs <;> simp
  simp only [key, Finset.sum_ite_eq, Finset.mem_univ, if_true]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
