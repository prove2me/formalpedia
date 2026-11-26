-- Prove2me | solution 1 for SSLMultiView.mutualInfo_task_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T22:40:30.498159+00:00
-- url     : https://prove2.me/submissions/051b829a-a6a8-4ca2-a023-67d3d63d886a

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
namespace S72N
open SSLMultiView

lemma sum_law {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (P : Ω → ℝ) (f : Ω → α) (φ : α → ℝ) :
    ∑ a, law P f a * φ a = ∑ ω, P ω * φ (f ω) := by
  unfold law
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise Finset.univ f (fun ω => P ω * φ (f ω))]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun ω hω => ?_))
  simp only [Finset.mem_filter] at hω
  rw [hω.2]

lemma entropy_eq {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (P : Ω → ℝ) (f : Ω → α) :
    entropy P f = -∑ ω, P ω * Real.log (law P f (f ω)) := by
  unfold entropy
  have := sum_law P f (fun a => Real.log (law P f a))
  rw [← this, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Real.negMulLog]; ring

lemma marg {Ω α γ : Type*} [Fintype Ω] [Fintype α] [DecidableEq α] [DecidableEq γ]
    (P : Ω → ℝ) (f : Ω → α) (h : Ω → γ) (c : γ) :
    ∑ a, law P (fun ω => (f ω, h ω)) (a, c) = law P h c := by
  unfold law
  rw [← Finset.sum_fiberwise (Finset.univ.filter (fun ω => h ω = c)) f P]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.filter_filter]
  congr 1; ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  tauto

lemma law_ge {Ω α : Type*} [Fintype Ω] [DecidableEq α] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (f : Ω → α) (ω : Ω) : P ω ≤ law P f (f ω) := by
  unfold law
  exact Finset.single_le_sum (f := P) (fun ω _ => hP ω) (by simp)

lemma law_nn {Ω α : Type*} [Fintype Ω] [DecidableEq α] (P : Ω → ℝ) (hP : ∀ ω, 0 ≤ P ω)
    (f : Ω → α) (a : α) : 0 ≤ law P f a := by
  unfold law; exact Finset.sum_nonneg (fun ω _ => hP ω)

lemma cmi_nonneg {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] [Fintype γ] [DecidableEq γ] (P : Ω → ℝ) (hP : IsPMF P)
    (f : Ω → α) (g : Ω → β) (h : Ω → γ) : 0 ≤ condMutualInfo P f g h := by
  obtain ⟨hP0, hP1⟩ := hP
  set Lfh := law P (fun ω => (f ω, h ω))
  set Lgh := law P (fun ω => (g ω, h ω))
  set Lh := law P h
  set L := law P (fun ω => (f ω, g ω, h ω))
  set φ : α × β × γ → ℝ := fun x => Lfh (x.1, x.2.2) * Lgh (x.2.1, x.2.2) / Lh x.2.2 / L x
  -- termwise
  have key : ∀ ω, P ω * (Real.log (Lfh (f ω, h ω)) + Real.log (Lgh (g ω, h ω)) -
      Real.log (Lh (h ω)) - Real.log (L (f ω, g ω, h ω))) ≤ P ω * φ (f ω, g ω, h ω) - P ω := by
    intro ω
    rcases (hP0 ω).lt_or_eq with hp | hp
    · have h1 : 0 < Lfh (f ω, h ω) := lt_of_lt_of_le hp (law_ge P hP0 (fun ω => (f ω, h ω)) ω)
      have h2 : 0 < Lgh (g ω, h ω) := lt_of_lt_of_le hp (law_ge P hP0 (fun ω => (g ω, h ω)) ω)
      have h3 : 0 < Lh (h ω) := lt_of_lt_of_le hp (law_ge P hP0 h ω)
      have h4 : 0 < L (f ω, g ω, h ω) := lt_of_lt_of_le hp (law_ge P hP0 (fun ω => (f ω, g ω, h ω)) ω)
      have hr : 0 < φ (f ω, g ω, h ω) := by
        simp only [φ]; positivity
      have e : Real.log (Lfh (f ω, h ω)) + Real.log (Lgh (g ω, h ω)) -
          Real.log (Lh (h ω)) - Real.log (L (f ω, g ω, h ω)) = Real.log (φ (f ω, g ω, h ω)) := by
        simp only [φ]
        have hA : 0 < Lfh (f ω, h ω) * Lgh (g ω, h ω) / Lh (h ω) := by positivity
        rw [Real.log_div hA.ne' h4.ne', Real.log_div (mul_pos h1 h2).ne' h3.ne',
          Real.log_mul h1.ne' h2.ne']
      rw [e]
      have := Real.log_le_sub_one_of_pos hr
      nlinarith
    · rw [← hp]; simp
  have hsum := Finset.sum_le_sum (fun ω (_ : ω ∈ Finset.univ) => key ω)
  rw [Finset.sum_sub_distrib, hP1] at hsum
  have hφ : ∑ ω, P ω * φ (f ω, g ω, h ω) ≤ 1 := by
    rw [← sum_law P (fun ω => (f ω, g ω, h ω)) φ]
    calc ∑ x, L x * φ x ≤ ∑ x : α × β × γ, Lfh (x.1, x.2.2) * Lgh (x.2.1, x.2.2) / Lh x.2.2 := by
          refine Finset.sum_le_sum (fun x _ => ?_)
          have hn : 0 ≤ Lfh (x.1, x.2.2) * Lgh (x.2.1, x.2.2) / Lh x.2.2 := by
            have := law_nn P hP0 (fun ω => (f ω, h ω)) (x.1, x.2.2)
            have := law_nn P hP0 (fun ω => (g ω, h ω)) (x.2.1, x.2.2)
            have := law_nn P hP0 h x.2.2
            positivity
          by_cases hx : L x = 0
          · rw [hx, zero_mul]; exact hn
          · simp only [φ]; rw [mul_div_cancel₀ _ hx]
      _ = ∑ c, Lh c := by
          simp only [Fintype.sum_prod_type]
          conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          have e : ∑ a, ∑ b, Lfh (a, c) * Lgh (b, c) / Lh c =
              (∑ a, Lfh (a, c)) * (∑ b, Lgh (b, c)) / Lh c := by
            rw [Finset.sum_mul_sum, Finset.sum_div]; simp_rw [Finset.sum_div]
          rw [e, marg P f h c, marg P g h c]
          exact mul_self_div_self _
      _ = 1 := by
          have := sum_law P h (fun _ => 1)
          simp only [mul_one] at this
          rw [this, hP1]
  have hc : condMutualInfo P f g h = -∑ ω, P ω * (Real.log (Lfh (f ω, h ω)) +
      Real.log (Lgh (g ω, h ω)) - Real.log (Lh (h ω)) - Real.log (L (f ω, g ω, h ω))) := by
    unfold condMutualInfo
    rw [entropy_eq P (fun ω => (f ω, h ω)), entropy_eq P (fun ω => (g ω, h ω)),
      entropy_eq P (fun ω => (f ω, g ω, h ω)), entropy_eq P h]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  rw [hc]
  linarith

end S72N
open SSLMultiView S72E S72N in
theorem solution {X S T Zs : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    [Fintype T] [DecidableEq T] [Fintype Zs] [DecidableEq Zs]
    (P : X × S × T → ℝ) (hP : IsPMF P) (F : X → Zs) :
    mutualInfo P (rep F) signalS - condMutualInfo P inputX signalS taskT -
        condMutualInfo P (rep F) inputX signalTask ≤ mutualInfo P (rep F) taskT := by
  have hC := cmi_nonneg P hP (rep F) inputX signalTask
  have hA : 0 ≤ entropy P (fun ω => (rep F ω, signalS ω)) + entropy P (fun ω => (taskT ω, signalS ω))
      - entropy P (fun ω => (rep F ω, taskT ω, signalS ω)) - entropy P signalS :=
    cmi_nonneg P hP (rep F) taskT signalS
  have hB : 0 ≤ entropy P (fun ω => (inputX ω, rep F ω, taskT ω)) +
      entropy P (fun ω => (signalS ω, rep F ω, taskT ω)) -
      entropy P (fun ω => (inputX ω, signalS ω, rep F ω, taskT ω)) -
      entropy P (fun ω => (rep F ω, taskT ω)) :=
    cmi_nonneg P hP inputX signalS (fun ω => (rep F ω, taskT ω))
  have e1 : entropy P (fun ω => (taskT ω, signalS ω)) = entropy P (fun ω => (signalS ω, taskT ω)) :=
    entropy_comp_inj P (fun ω => (signalS ω, taskT ω)) (fun p : S × T => (p.2, p.1))
      (fun p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1)
  have e2 : entropy P (fun ω => (signalS ω, rep F ω, taskT ω)) =
      entropy P (fun ω => (rep F ω, taskT ω, signalS ω)) :=
    entropy_comp_inj P (fun ω => (rep F ω, taskT ω, signalS ω)) (fun p : Zs × T × S => (p.2.2, p.1, p.2.1))
      (fun p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.2.1 (Prod.ext h.2.2 h.1))
  have e3 : entropy P (fun ω => (inputX ω, rep F ω, taskT ω)) =
      entropy P (fun ω => (inputX ω, taskT ω)) :=
    entropy_comp_inj P (fun ω => (inputX ω, taskT ω)) (fun p : X × T => (p.1, F p.1, p.2))
      (fun p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 h.2.2)
  have e4 : entropy P (fun ω => (inputX ω, signalS ω, rep F ω, taskT ω)) =
      entropy P (fun ω => (inputX ω, signalS ω, taskT ω)) :=
    entropy_comp_inj P (fun ω => (inputX ω, signalS ω, taskT ω))
      (fun p : X × S × T => (p.1, p.2.1, F p.1, p.2.2))
      (fun p q h => by simp only [Prod.mk.injEq] at h; exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2.2))
  rw [e1] at hA; rw [e2, e3, e4] at hB
  unfold mutualInfo
  have hD : condMutualInfo P inputX signalS taskT = entropy P (fun ω => (inputX ω, taskT ω)) +
      entropy P (fun ω => (signalS ω, taskT ω)) - entropy P (fun ω => (inputX ω, signalS ω, taskT ω)) -
      entropy P taskT := rfl
  rw [hD]
  linarith
