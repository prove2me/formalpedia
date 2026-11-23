-- Prove2me | solution 1 for PI.VolStabW.reach_of_approx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:14.800172+00:00
-- url     : https://prove2.me/submissions/1d3ae38d-78a9-4f28-84e7-d65db559a9ad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_MeasureEqOfCos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_EventuallySmulSub
import Theorems.Thm_PI_VolStabW_mem_smulSub
import Theorems.Thm_PI_VolStabW_coe_smulSub
import Theorems.Thm_PI_VolStabW_eventually_smul_sub
import Theorems.Thm_PI_VolStabW_iInter_thick


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Topology Filter Set
variable {K V X : Type} [Field K] [TopologicalSpace K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul K V]
  [AddCommGroup X] [Module K X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul K X]
variable [T2Space X]
namespace PI.VolStabW
theorem _root_.solution (π : K) (hπ : Tendsto (fun k : ℕ => π ^ k) atTop (𝓝 0))
    (L : AddSubgroup V) (hLc : IsCompact (L : Set V)) (hπL : ∀ w ∈ L, π • w ∈ L)
    (D : V →+ X) (hDc : Continuous D) (hDs : ∀ (t : K) w, D (t • w) = t • D w)
    (P : AddSubgroup X) (hPc : IsCompact (P : Set X))
    (hbase : ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub π P) :
    ∀ p ∈ P, ∃ l ∈ L, D l = p := by
  have hπkL : ∀ k : ℕ, ∀ w ∈ L, π ^ k • w ∈ L := by
    intro k
    induction k with
    | zero => intro w hw; simpa using hw
    | succ k ih =>
      intro w hw
      rw [pow_succ, mul_smul]
      exact ih _ (hπL w hw)
  have hstep : ∀ k : ℕ, ∀ p ∈ P, ∃ l ∈ L, p - D l ∈ smulSub (π ^ k) P := by
    intro k
    induction k with
    | zero =>
      intro p hp
      exact ⟨0, L.zero_mem, (mem_smulSub _ _ _).2 ⟨p, hp, by simp⟩⟩
    | succ k ih =>
      intro p hp
      obtain ⟨l, hl, hpl⟩ := ih p hp
      obtain ⟨p', hp', e1⟩ := (mem_smulSub _ _ _).1 hpl
      obtain ⟨l', hl', hpl'⟩ := hbase p' hp'
      obtain ⟨p'', hp'', e2⟩ := (mem_smulSub _ _ _).1 hpl'
      refine ⟨l + π ^ k • l', L.add_mem hl (hπkL k l' hl'), (mem_smulSub _ _ _).2 ⟨p'', hp'', ?_⟩⟩
      rw [map_add, hDs, pow_succ, mul_smul, e2, smul_sub, e1]
      abel
  set S : Set X := D '' (L : Set V) with hS
  have hSc : IsClosed S := (hLc.image hDc).isClosed
  have hb : ∀ N ∈ 𝓝 (0 : X), ∃ k, (smulSub (π ^ k) P : Set X) ⊆ N := by
    intro N hN
    obtain ⟨k, hk⟩ := eventually_smul_sub (P : Set X) hPc (fun k => π ^ k) hπ N hN
    refine ⟨k, ?_⟩
    rw [coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp
  intro p hp
  have hmem : p ∈ ⋂ k, thick S (smulSub (π ^ k) P) := by
    refine mem_iInter.2 fun k => ?_
    obtain ⟨l, hl, hpl⟩ := hstep k p hp
    exact ⟨D l, ⟨l, hl, rfl⟩, hpl⟩
  rw [iInter_thick S hSc (fun k => smulSub (π ^ k) P) hb] at hmem
  obtain ⟨l, hl, e⟩ := hmem
  exact ⟨l, hl, e⟩
end PI.VolStabW
