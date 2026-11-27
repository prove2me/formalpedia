-- Prove2me | solution 1 for ReciprocityTheory.Coh.trunc_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:30:31.945258+00:00
-- url     : https://prove2.me/submissions/5e02b170-5819-4d12-b670-e4d097edd2e0

import Definitions.Def_ReciprocityTheory_GroupCohomology_LocaliseA
import Definitions.Def_ReciprocityTheory_GroupCohomology_Localise
import Theorems.Thm_ReciprocityTheory_Coh_Cx_H_ind
import Theorems.Thm_ReciprocityTheory_Coh_Cx_Hom_H_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_cls_eq_zero_iff
import Theorems.Thm_ReciprocityTheory_Coh_Cx_exists_cls
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_succ
import Theorems.Thm_ReciprocityTheory_Coh_Cx_mem_B_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.Coh.Cx.Hom.H_cls
attribute [local simp] ReciprocityTheory.Coh.Cx.cls_eq_zero_iff



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh
open ReciprocityTheory.Gal Cx Function
universe u
namespace ReciprocityTheory.Coh
theorem _root_.solution : TruncStatement.{u} := by
  intro R _ A L
  refine ⟨truncCx A L, truncHom A L, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Hom.H_cls, cls_eq_zero_iff, mem_B_zero] at hc
      rw [cls_eq_zero_iff, mem_B_zero]
      exact Subtype.ext hc
  · intro c
    induction c using H_ind with
    | h x hx =>
      exact ⟨(truncCx A L).cls 0 ⟨x, Submodule.mem_top⟩ (Subtype.ext hx), rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro c hc
    induction c using H_ind with
    | h x hx =>
      rw [Hom.H_cls, cls_eq_zero_iff, mem_B_succ] at hc
      obtain ⟨y, hy⟩ := hc
      rw [cls_eq_zero_iff, mem_B_succ]
      exact ⟨⟨y, Submodule.mem_top⟩, Subtype.ext hy⟩
  · ext c
    constructor
    · rintro ⟨c', rfl⟩
      induction c' using H_ind with
      | h x hx =>
        rw [Hom.H_cls]
        obtain ⟨_, h⟩ := (mem_truncW_one A L).1 x.2
        exact h
    · intro hc
      obtain ⟨x, hx, rfl⟩ := exists_cls c
      have hm : x ∈ truncW A L 1 := (mem_truncW_one A L).2 ⟨hx, hc⟩
      exact ⟨(truncCx A L).cls 1 ⟨x, hm⟩ (Subtype.ext hx), rfl⟩
  · intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    constructor
    intro a b
    induction a using H_ind with
    | h x hx =>
    induction b using H_ind with
    | h y hy =>
      have h1 : x = 0 := Subtype.ext ((Submodule.mem_bot R).1 x.2)
      have h2 : y = 0 := Subtype.ext ((Submodule.mem_bot R).1 y.2)
      subst h1 h2; rfl
end ReciprocityTheory.Coh
