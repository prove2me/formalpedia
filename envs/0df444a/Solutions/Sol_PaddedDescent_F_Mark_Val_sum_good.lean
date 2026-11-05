-- Prove2me | solution 1 for PaddedDescent.F.Mark.Val.sum_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:11:18.746674+00:00
-- url     : https://prove2.me/submissions/4fd244a2-0404-4bac-a9ca-396b06034169

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_StepMachines_Math_SatNet
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Nodup
import Definitions.Def_PaddedDescent_F_MarkVal
import Theorems.Thm_PaddedDescent_F_Mark_Val_length_st
import Theorems.Thm_PaddedDescent_F_Mark_Val_st_good
import Theorems.Thm_PaddedDescent_F_Mark_Val_ext_of_le
import Theorems.Thm_PaddedDescent_F_Mark_Val_st_inj
import Theorems.Thm_PaddedDescent_F_Mark_Val_st_surj
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_mem_words
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.Val
open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark
variable {k g n β b : ℕ} {Ls : List Fml} {y : ℕ}
namespace PaddedDescent.F.Mark.Val
theorem _root_.solution (hg : 0 < g) (hw : WfL k n Ls) (F : (Fin g → List Bool) → ℤ) :
    (∑ z ∈ Fintype.piFinset fun a : Fin g => words (qv g n + (tch g n Ls a).length),
      by classical exact if Gd g n Ls z then F z else 0) =
      ∑ σ : Fin n → Bool, ∑ P ∈ (vset (ext σ) Ls).powerset, F fun a => st g n Ls (ext σ) P a := by
  classical
  rw [← Finset.sum_filter, Finset.sum_sigma']
  symm
  have hsub : ∀ σ : ℕ → Bool, vset σ Ls ⊆ Finset.range (cls Ls).length := fun σ => Finset.filter_subset _ _
  refine Finset.sum_nbij (fun x => fun a : Fin g => st g n Ls (ext x.1) x.2 a) ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨σ, P⟩ hx
    have hP : P ⊆ vset (ext σ) Ls := Finset.mem_powerset.1 (Finset.mem_sigma.1 hx).2
    exact Finset.mem_filter.2 ⟨Fintype.mem_piFinset.2 fun a => mem_words.2 (length_st _ _ _),
      st_good hg hw (fun x hx => ext_of_le hx) hP⟩
  · rintro ⟨σ, P⟩ hx ⟨σ', P'⟩ hx' h
    have hP : P ⊆ vset (ext σ) Ls := Finset.mem_powerset.1 (Finset.mem_sigma.1 (Finset.mem_coe.1 hx)).2
    have hP' : P' ⊆ vset (ext σ') Ls := Finset.mem_powerset.1 (Finset.mem_sigma.1 (Finset.mem_coe.1 hx')).2
    obtain ⟨h1, h2⟩ := st_inj hg hw (hP.trans (hsub _)) (hP'.trans (hsub _)) h
    subst h1; subst h2; rfl
  · intro z hz
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hz)
    obtain ⟨σ, P, hP, hzz⟩ := st_surj hg hw (fun a => mem_words.1 (Fintype.mem_piFinset.1 h1 a)) h2
    exact ⟨⟨σ, P⟩, Finset.mem_coe.2 (Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_powerset.2 hP⟩), hzz⟩
end PaddedDescent.F.Mark.Val
