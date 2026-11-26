-- Prove2me | solution 1 for SSLMultiView.cmi_input_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T22:37:32.38997+00:00
-- url     : https://prove2.me/submissions/05b2f28a-3ae4-4843-a515-b1a644be6d96

import Mathlib
import Definitions.Def_SSLMultiView_Basic

set_option autoImplicit false

open Real

namespace S72E
open SSLMultiView

lemma law_comp_inj {Ω α β : Type*} [Fintype Ω] [DecidableEq α] [DecidableEq β]
    (P : Ω → ℝ) (f : Ω → α) (φ : α → β) (hφ : Function.Injective φ) (a : α) :
    law P (fun ω => φ (f ω)) (φ a) = law P f a := by
  unfold law
  congr 1
  ext ω
  simp [hφ.eq_iff]

lemma law_comp_notin {Ω α β : Type*} [Fintype Ω] [DecidableEq α] [DecidableEq β]
    (P : Ω → ℝ) (f : Ω → α) (φ : α → β) (b : β) (hb : ∀ a, φ a ≠ b) :
    law P (fun ω => φ (f ω)) b = 0 := by
  unfold law
  rw [Finset.sum_eq_zero]
  intro ω hω
  simp only [Finset.mem_filter] at hω
  exact absurd hω.2 (hb _)

lemma entropy_comp_inj {Ω α β : Type*} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (P : Ω → ℝ) (f : Ω → α) (φ : α → β) (hφ : Function.Injective φ) :
    entropy P (fun ω => φ (f ω)) = entropy P f := by
  unfold entropy
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image φ))]
  · rw [Finset.sum_image (fun x _ y _ h => hφ h)]
    exact Finset.sum_congr rfl (fun a _ => by rw [law_comp_inj P f φ hφ a])
  · intro b _ hb
    have : ∀ a, φ a ≠ b := fun a ha => hb (Finset.mem_image.2 ⟨a, Finset.mem_univ _, ha⟩)
    rw [law_comp_notin P f φ b this]; simp

end S72E

open SSLMultiView S72E in
theorem solution {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P) (F : X → Zs) :
    condMutualInfo P (rep F) inputX taskT =
      condMutualInfo P (rep F) signalS taskT + condMutualInfo P (rep F) inputX signalTask := by
  have h1 : entropy P (fun ω => (rep F ω, inputX ω, taskT ω)) =
      entropy P (fun ω => (inputX ω, taskT ω)) :=
    entropy_comp_inj P (fun ω => (inputX ω, taskT ω)) (fun p : X × T => (F p.1, p.1, p.2))
      (fun p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2)
  have h2 : entropy P (fun ω => (rep F ω, inputX ω, signalTask ω)) =
      entropy P (fun ω => (inputX ω, signalTask ω)) :=
    entropy_comp_inj P (fun ω => (inputX ω, signalTask ω)) (fun p : X × (S × T) => (F p.1, p.1, p.2))
      (fun p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 h.2.2)
  have h3 : entropy P (fun ω => (rep F ω, signalTask ω)) =
      entropy P (fun ω => (rep F ω, signalS ω, taskT ω)) := rfl
  have h4 : entropy P (fun ω => (signalS ω, taskT ω)) = entropy P signalTask := rfl
  have h5 : entropy P (fun ω => (inputX ω, signalTask ω)) = entropy P (fun ω : X × S × T => ω) := rfl
  unfold condMutualInfo
  rw [h1, h2, h3, h4]
  ring
