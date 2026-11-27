-- Prove2me | solution 1 for ReciprocityTheory.Coh.section_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:53.254281+00:00
-- url     : https://prove2.me/submissions/894709eb-3537-41e2-86c3-9151d563fe59

import Definitions.Def_ReciprocityTheory_GroupCohomology_CupConnRightStatement
import Definitions.Def_ReciprocityTheory_GroupCohomology_SectionA
import Definitions.Def_ReciprocityTheory_GroupCohomology_Section
import Theorems.Thm_ReciprocityTheory_Coh_ContinuousSections_core


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open Function
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : SectionStatement.{u} := by
  intro B C _ _ _ _ _ _ p hp hsurj hcase
  rcases hcase with hd | ⟨hcB, hT2, hTD, hT2C⟩
  · exact ⟨surjInv hsurj, continuous_of_discreteTopology, surjInv_eq hsurj⟩
  · have : CompactSpace (Multiplicative B) := hcB
    have : T2Space (Multiplicative B) := hT2
    have : TotallyDisconnectedSpace (Multiplicative B) := hTD
    let U : Subgroup (Multiplicative B) :=
      { carrier := {x | p x.toAdd = 0}
        mul_mem' := fun {a b} ha hb => by
          simp only [Set.mem_ofPred_eq, toAdd_mul, map_add] at ha hb ⊢; rw [ha, hb, add_zero]
        one_mem' := by simp
        inv_mem' := fun {a} ha => by
          simp only [Set.mem_ofPred_eq, toAdd_inv, map_neg] at ha ⊢; rw [ha, neg_zero] }
    have hU : IsClosed (U : Set (Multiplicative B)) :=
      isClosed_singleton.preimage (hp.comp continuous_toAdd)
    obtain ⟨t, ht, htU, hc⟩ := ContinuousSections.core U hU
    let f : B → B := fun b => Multiplicative.toAdd (t (Multiplicative.ofAdd b))
    have hf : Continuous f := continuous_toAdd.comp (ht.comp continuous_ofAdd)
    have hpf : ∀ b, p (f b) = p b := by
      intro b
      have h := htU (Multiplicative.ofAdd b)
      change p (Multiplicative.toAdd (t (Multiplicative.ofAdd b) * (Multiplicative.ofAdd b)⁻¹)) = 0 at h
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, map_add, map_neg, add_neg_eq_zero] at h
      exact h
    have hfc : ∀ b b', p b = p b' → f b = f b' := by
      intro b b' hbb
      refine congrArg Multiplicative.toAdd (hc _ _ ?_)
      change p (Multiplicative.toAdd (Multiplicative.ofAdd b * (Multiplicative.ofAdd b')⁻¹)) = 0
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, map_add, map_neg, hbb, add_neg_cancel]
    refine ⟨fun c => f (surjInv hsurj c), continuous_iff_isClosed.2 fun F hF => ?_,
      fun c => by rw [hpf, surjInv_eq hsurj]⟩
    have e : (fun c => f (surjInv hsurj c)) ⁻¹' F = p '' (f ⁻¹' F) := by
      ext c
      constructor
      · intro hc'
        exact ⟨surjInv hsurj c, hc', surjInv_eq hsurj c⟩
      · rintro ⟨b, hb, rfl⟩
        show f (surjInv hsurj (p b)) ∈ F
        rw [hfc _ b (surjInv_eq hsurj _)]; exact hb
    rw [e]
    exact hp.isClosedMap _ (hF.preimage hf)
end ReciprocityTheory.Coh
