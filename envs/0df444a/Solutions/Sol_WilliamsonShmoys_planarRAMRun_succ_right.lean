-- Prove2me | solution 1 for WilliamsonShmoys.planarRAMRun_succ_right
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T06:04:29.433424+00:00
-- url     : https://prove2.me/submissions/2e7c810f-5b1a-4582-939d-a6bd677b0559

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMSpec

set_option autoImplicit false

namespace Aux
open WilliamsonShmoys

theorem planarRAMRun_add (program : List PlanarRAMInstruction) (s : PlanarRAMState) (a b : ℕ) :
    planarRAMRun program s (a + b) = planarRAMRun program (planarRAMRun program s a) b := by
  unfold planarRAMRun
  rw [add_comm, Function.iterate_add_apply]

theorem planarRAMRun_succ_right (program : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun program s (t + 1) = planarRAMStep program (planarRAMRun program s t) := by
  unfold planarRAMRun
  rw [Function.iterate_succ_apply']

theorem planarRAMStep_of_halt (program : List PlanarRAMInstruction) (s : PlanarRAMState)
    (h : program[s.pc]? = some PlanarRAMInstruction.halt) :
    planarRAMStep program s = s := by
  unfold planarRAMStep
  simp [h]

theorem planarRAMRun_of_halt (program : List PlanarRAMInstruction) (s : PlanarRAMState)
    (h : program[s.pc]? = some PlanarRAMInstruction.halt) (t : ℕ) :
    planarRAMRun program s t = s := by
  induction t with
  | zero => rfl
  | succ t ih => rw [planarRAMRun_succ_right, ih, planarRAMStep_of_halt program s h]

theorem RAMReachesWithin.step (program : List PlanarRAMInstruction) (s : PlanarRAMState) :
    RAMReachesWithin program s (fun s' => s' = planarRAMStep program s) 1 :=
  ⟨1, le_rfl, rfl⟩

theorem RAMSpec.seq (program : List PlanarRAMInstruction) (P Q R : PlanarRAMState → Prop)
    (t₁ t₂ : ℕ) (h₁ : RAMSpec program P Q t₁) (h₂ : RAMSpec program Q R t₂) :
    RAMSpec program P R (t₁ + t₂) := by
  intro s hs
  obtain ⟨τ₁, hτ₁, hQ⟩ := h₁ s hs
  obtain ⟨τ₂, hτ₂, hR⟩ := h₂ _ hQ
  exact ⟨τ₁ + τ₂, by omega, by rw [planarRAMRun_add]; exact hR⟩

theorem RAMSpec.consequence (program : List PlanarRAMInstruction)
    (P P' Q Q' : PlanarRAMState → Prop) (t t' : ℕ)
    (h : RAMSpec program P Q t) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s) (ht : t ≤ t') :
    RAMSpec program P' Q' t' := by
  intro s hs
  obtain ⟨τ, hτ, hq⟩ := h s (hP s hs)
  exact ⟨τ, le_trans hτ ht, hQ _ hq⟩

theorem RAMSpec.loop (program : List PlanarRAMInstruction)
    (I E : PlanarRAMState → Prop) (μ : PlanarRAMState → ℕ) (c : ℕ)
    (hbody : ∀ s, I s → ¬ E s →
      RAMReachesWithin program s (fun s' => I s' ∧ μ s' < μ s) c)
    (m : ℕ) :
    RAMSpec program (fun s => I s ∧ μ s ≤ m) (fun s => I s ∧ E s) (c * m) := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rintro s ⟨hI, hμ⟩
    by_cases hE : E s
    · exact ⟨0, Nat.zero_le _, hI, hE⟩
    · obtain ⟨τ, hτ, hI', hlt⟩ := hbody s hI hE
      have hm : μ (planarRAMRun program s τ) < m := lt_of_lt_of_le hlt hμ
      obtain ⟨τ', hτ', hfin⟩ :=
        ih (μ (planarRAMRun program s τ)) hm _ ⟨hI', le_rfl⟩
      refine ⟨τ + τ', ?_, by rw [planarRAMRun_add]; exact hfin⟩
      have h1 : c * μ (planarRAMRun program s τ) + c ≤ c * m := by
        have := Nat.mul_le_mul_left c (Nat.succ_le_of_lt hm)
        simpa [Nat.mul_succ] using this
      omega

end Aux

open WilliamsonShmoys

theorem solution (program : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun program s (t + 1) = planarRAMStep program (planarRAMRun program s t) :=
  Aux.planarRAMRun_succ_right program s t
