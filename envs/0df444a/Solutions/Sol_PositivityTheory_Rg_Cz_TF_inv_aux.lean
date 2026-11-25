-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.TF.inv_aux
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:37:24.690803+00:00
-- url     : https://prove2.me/submissions/6ed24fd6-d891-486b-9c10-c04459aa0bdf

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinCK
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_TensorRelationsGL_PTransFinA
import Theorems.Thm_PositivityTheory_Rg_Cz_lift_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_apply
import Theorems.Thm_PositivityTheory_Rg_Cz_pm_one
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PositivityTheory.Rg.Cz.lift_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_apply
attribute [local simp] PositivityTheory.Rg.Cz.pm_one



set_option autoImplicit false
noncomputable section
open Formalism.REAL Matrix
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
open PositivityTheory.Rg.Cz.TF
namespace PositivityTheory.Rg.Cz.TF
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] (B : Subalgebra ℂ A) (x : A) (hx : x ∈ B) (u : ℂ) :
    ∀ L : List ℂ, (∀ c ∈ L, u + c ≠ 0) → ∃ h ∈ B, Commute h x ∧ ∃ β : ℂ, β ≠ 0 ∧
      (L.map fun c => x - algebraMap ℂ A c).prod = (algebraMap ℂ A u + x) * h + algebraMap ℂ A β := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨0, B.zero_mem, Commute.zero_left x, 1, one_ne_zero, ?_⟩
    simp
  | cons c L ih =>
    intro hL
    obtain ⟨h, hB, hc, β, hβ, heq⟩ := ih (fun d hd => hL d (List.mem_cons_of_mem _ hd))
    have hs : u + c ≠ 0 := hL c (by simp)
    have hcm : Commute ((x - algebraMap ℂ A c) * h + algebraMap ℂ A β) x :=
      (((Commute.refl x).sub_left (Algebra.commute_algebraMap_left c x)).mul_left hc).add_left
        (Algebra.commute_algebraMap_left β x)
    refine ⟨(x - algebraMap ℂ A c) * h + algebraMap ℂ A β,
      B.add_mem (B.mul_mem (B.sub_mem hx (B.algebraMap_mem c)) hB) (B.algebraMap_mem β),
      hcm, -((u + c) * β), neg_ne_zero.mpr (mul_ne_zero hs hβ), ?_⟩
    rw [List.map_cons, List.prod_cons, heq]
    have hq : x - algebraMap ℂ A c = (algebraMap ℂ A u + x) - algebraMap ℂ A (u + c) := by
      rw [map_add]; abel
    rw [hq, map_neg, map_mul]
    have ht := Algebra.commutes (u + c) (algebraMap ℂ A u + x)
    generalize algebraMap ℂ A u + x = v at ht ⊢
    generalize algebraMap ℂ A (u + c) = t at ht ⊢
    generalize algebraMap ℂ A β = w
    calc (v - t) * (v * h + w) = v * v * h + v * w - t * v * h - t * w := by noncomm_ring
      _ = v * v * h + v * w - v * t * h - t * w := by rw [ht]
      _ = v * ((v - t) * h + w) + -(t * w) := by noncomm_ring
end PositivityTheory.Rg.Cz.TF
