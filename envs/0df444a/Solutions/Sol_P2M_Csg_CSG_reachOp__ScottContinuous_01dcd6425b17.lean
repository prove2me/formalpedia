-- Prove2me | solution 1 for P2M_Csg_CSG_reachOp__ScottContinuous_01dcd6425b17
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:03:38.406276+00:00
-- url     : https://prove2.me/submissions/b1037c53-ab7d-4394-ad55-52b9fa099885

import Definitions.Def_Csg_ReachOp
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.FixedPoints
import Mathlib.Order.OmegaCompletePartialOrder
import Definitions.Def_Csg_ReachConverge
import Theorems.Thm_Csg_CSG_exists_forall_le_add_of_tendsto
import Theorems.Thm_Csg_CSG_stageValue_le_one
import Theorems.Thm_Csg_CSG_stageValue_lipschitz
import Theorems.Thm_Csg_CSG_stageValue_mono


set_option autoImplicit true
open Csg
open Csg.CSG
open OmegaCompletePartialOrder Filter Topology
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
variable (C : CSG S A1 A2)
namespace Csg.CSG
theorem _root_.solution (goal : S → Prop) [DecidablePred goal]
    (hr : ∀ s a1 a2, C.r s a1 a2 = 0) :
    ωScottContinuous (C.reachOp goal hr) := by
  rw [ωScottContinuous_iff_map_ωSup_of_orderHom]
  intro c
  funext s
  by_cases hgoal : goal s
  · -- `goal s`: both sides are the constant `1`, regardless of the chain.
    have hterm : ∀ n, (c.map (C.reachOp goal hr)) n s
        = (⟨1, by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
      intro n
      change C.reachOpFun goal hr (c n) s = _
      simp only [reachOpFun, if_pos hgoal]
    have hLHS : C.reachOp goal hr (ωSup c) s
        = (⟨1, by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
      change C.reachOpFun goal hr (ωSup c) s = _
      simp only [reachOpFun, if_pos hgoal]
    have hRHS : ωSup (c.map (C.reachOp goal hr)) s
        = (⟨1, by norm_num, by norm_num⟩ : Set.Icc (0 : ℝ) 1) := by
      refine le_antisymm (ωSup_le _ _ fun n => (hterm n).le) ?_
      rw [← hterm 0]
      exact le_ωSup (c.map (C.reachOp goal hr)) 0 s
    rw [hLHS, hRHS]
  · -- `¬ goal s`: reduces to `stageValue`'s continuity along the chain.
    apply Subtype.ext
    set g : S → ℝ := fun s' => ((ωSup c) s' : ℝ) with hg_def
    set d : ℕ → S → ℝ := fun n s' => ((c n) s' : ℝ) with hd_def
    have hle_g : ∀ n s', d n s' ≤ g s' := fun n s' => le_ωSup c n s'
    have hg_eq : ∀ s', g s' = ⨆ n, d n s' := by
      intro s'
      change ((ωSup c) s' : ℝ) = ⨆ n, d n s'
      have hpt : (ωSup c) s' = ⨆ n, (c n) s' := rfl
      rw [hpt, Set.Icc.coe_iSup (by norm_num : (0 : ℝ) ≤ 1)]
    have hmono : ∀ s', Monotone (fun n => d n s') := fun s' _ _ hnm =>
      OrderHomClass.mono c hnm s'
    have hbdd1 : ∀ s', BddAbove (Set.range (fun n => d n s')) :=
      fun s' => ⟨1, by rintro _ ⟨n, rfl⟩; exact (c n s').2.2⟩
    have htendsto : ∀ s', Tendsto (fun n => d n s') atTop (𝓝 (g s')) := fun s' => by
      rw [hg_eq s']
      exact tendsto_atTop_ciSup (hmono s') (hbdd1 s')
    have hstage_bdd : BddAbove (Set.range (fun n => C.stageValue s (d n))) :=
      ⟨1, by rintro _ ⟨n, rfl⟩; exact C.stageValue_le_one hr fun s' => (c n s').2.2⟩
    have hkey : C.stageValue s g = ⨆ n, C.stageValue s (d n) := by
      refine le_antisymm (le_of_forall_sub_le fun ε hε => ?_) (ciSup_le fun n => ?_)
      · obtain ⟨N, hN⟩ := exists_forall_le_add_of_tendsto htendsto hε
        have hbound : ∀ s', |g s' - d N s'| ≤ ε := fun s' =>
          abs_le.mpr ⟨by linarith [hle_g N s'], by linarith [hN N le_rfl s']⟩
        have hlip := abs_le.mp (C.stageValue_lipschitz (s := s) hε.le hbound)
        have hNle : C.stageValue s (d N) ≤ ⨆ n, C.stageValue s (d n) := le_ciSup hstage_bdd N
        linarith [hlip.1]
      · exact C.stageValue_mono fun s' => hle_g n s'
    change (C.reachOp goal hr (ωSup c) s : ℝ) = (ωSup (c.map (C.reachOp goal hr)) s : ℝ)
    have hLHS_eq : (C.reachOp goal hr (ωSup c) s : ℝ) = C.stageValue s g := by
      change (C.reachOpFun goal hr (ωSup c) s : ℝ) = _
      simp only [reachOpFun, if_neg hgoal]
      rfl
    have hRHS_eq : (ωSup (c.map (C.reachOp goal hr)) s : ℝ) = ⨆ n, C.stageValue s (d n) := by
      have hpt : (ωSup (c.map (C.reachOp goal hr)) s : Set.Icc (0 : ℝ) 1)
          = ⨆ n, (c.map (C.reachOp goal hr)) n s := rfl
      rw [hpt, Set.Icc.coe_iSup (by norm_num : (0 : ℝ) ≤ 1)]
      congr 1
      funext n
      change (C.reachOpFun goal hr (c n) s : ℝ) = _
      simp only [reachOpFun, if_neg hgoal]
      rfl
    rw [hLHS_eq, hRHS_eq, hkey]
end Csg.CSG
