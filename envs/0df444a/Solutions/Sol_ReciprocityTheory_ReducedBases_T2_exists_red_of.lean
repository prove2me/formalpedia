-- Prove2me | solution 1 for ReciprocityTheory.ReducedBases.T2.exists_red_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:33:54.993802+00:00
-- url     : https://prove2.me/submissions/5f420a09-3510-4bb5-9e0d-90f5e3bd25d8

import Definitions.Def_ReciprocityTheory_ReducedBases_SizeReduce
import Definitions.Def_ReciprocityTheory_ReducedBases_NormGsoCompSwapRightSqMul
import Definitions.Def_ReciprocityTheory_ReducedBases_ExistsRedOf
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_gs_ne_zero
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_norm_swap_j
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_pot_swap
import Theorems.Thm_ReciprocityTheory_ReducedBases_T2_size_reduce


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2
open Finset InnerProductSpace
namespace ReciprocityTheory.ReducedBases.T2
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}
    (f : (Fin d → ℤ) →ₗ[ℤ] E)
    (hli : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), LinearIndependent ℝ (fun i => f (e i)))
    (hlow : ∃ c : ℝ, 0 < c ∧ ∀ (e : Module.Basis (Fin d) ℤ (Fin d → ℤ)) (k : Fin d),
      c ≤ ∏ j ∈ univ.filter (fun j : Fin d => j ≤ k), ‖gs (fun i => f (e i)) j‖ ^ 2) :
    ∃ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), IsRed (fun i => f (e i)) := by
  obtain ⟨c, hc0, hc⟩ := hlow
  set S : Set ℝ := Set.range (fun e : Module.Basis (Fin d) ℤ (Fin d → ℤ) =>
    pot (fun i => f (e i))) with hSdef
  have hpos : ∀ e : Module.Basis (Fin d) ℤ (Fin d → ℤ), c ^ d ≤ pot (fun i => f (e i)) := by
    intro e
    unfold pot
    calc c ^ d = ∏ _k : Fin d, c := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hc0.le) (fun k _ => hc e k)
  have hne : S.Nonempty := ⟨_, ⟨Pi.basisFun ℤ (Fin d), rfl⟩⟩
  have hbdd : BddBelow S := ⟨c ^ d, by rintro _ ⟨e, rfl⟩; exact hpos e⟩
  have hm : c ^ d ≤ sInf S := le_csInf hne (by rintro _ ⟨e, rfl⟩; exact hpos e)
  have hm0 : 0 < sInf S := lt_of_lt_of_le (pow_pos hc0 d) hm
  obtain ⟨_, ⟨e0, rfl⟩, he0⟩ :=
    exists_lt_of_csInf_lt hne (show sInf S < 4 / 3 * sInf S by linarith)
  obtain ⟨e1, hgs1, hsz1⟩ := size_reduce f hli e0
  have hpot1 : pot (fun i => f (e1 i)) = pot (fun i => f (e0 i)) := by unfold pot; rw [hgs1]
  have hb1 := hli e1
  by_contra hnot
  have hex : ∃ i j : Fin d, i.val = j.val + 1 ∧
      2 * ‖gs (fun i => f (e1 i)) i‖ ^ 2 < ‖gs (fun i => f (e1 i)) j‖ ^ 2 := by
    by_contra h
    push Not at h
    exact hnot ⟨e1, hb1, hsz1, fun i j hij => h i j hij⟩
  obtain ⟨j1, j, hj, hlt⟩ := hex
  have hjj1 : j < j1 := by rw [Fin.lt_def]; omega
  set e2 := e1.reindex (Equiv.swap j j1) with he2
  have hb2 : (fun i => f (e2 i)) = (fun i => f (e1 i)) ∘ Equiv.swap j j1 := by
    funext i; simp [he2, Module.Basis.coe_reindex, Equiv.symm_swap]
  have hp2 := pot_swap _ hb1 j j1 hj
  rw [← hb2] at hp2
  have hV := norm_swap_j (fun i => f (e1 i)) j j1 hj
  have hsz := hsz1 j1 j hjj1
  set m := mu (fun i => f (e1 i)) j1 j
  set A := ‖gs (fun i => f (e1 i)) j‖ ^ 2 with hA
  set B := ‖gs (fun i => f (e1 i)) j1‖ ^ 2
  have hA0 : 0 < A := by have := gs_ne_zero _ hb1 j; positivity
  have hm2 : m ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg m]
  have hVA : ‖gs (fun i => f (e1 i)) j1 + m • gs (fun i => f (e1 i)) j‖ ^ 2 / A < 3 / 4 := by
    rw [div_lt_iff₀ hA0, hV]; nlinarith
  have hP1 : 0 < pot (fun i => f (e1 i)) := lt_of_lt_of_le (pow_pos hc0 d) (hpos e1)
  have h2 : sInf S ≤ pot (fun i => f (e2 i)) := csInf_le hbdd ⟨e2, rfl⟩
  have h3 : pot (fun i => f (e2 i)) < pot (fun i => f (e1 i)) * (3 / 4) := by
    rw [hp2]; exact mul_lt_mul_of_pos_left hVA hP1
  rw [hpot1] at h3
  linarith
end ReciprocityTheory.ReducedBases.T2
