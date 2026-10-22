-- Prove2me | solution 1 for OpenPitMIP.UltPit.feasible_nested_pits
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:05:28.030033+00:00
-- url     : https://prove2.me/submissions/137967b6-e42b-4143-9e36-d066d4235f8e

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

set_option autoImplicit false
open OpenPitMIP.UltPit PCPSPC

theorem mm_chain {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (w : C → ℝ)
    (harc : ∀ c c', I.arc c c' → w c ≤ w c') :
    ∀ c1 c2, I.cprec c1 c2 → w c2 ≤ w c1 := by
  haveI := hI.strictOrder
  haveI : IsTrans C (fun a b => I.cprec b a) := ⟨fun a b c h1 h2 => _root_.trans h2 h1⟩
  haveI : IsIrrefl C (fun a b => I.cprec b a) := ⟨fun a h => irrefl a h⟩
  have wf : WellFounded (fun a b : C => I.cprec b a) :=
    Finite.wellFounded_of_trans_of_irrefl _
  have wf' : WellFounded I.cprec := Finite.wellFounded_of_trans_of_irrefl _
  intro c1
  induction c1 using wf.induction with
  | _ c1 ih =>
    intro c2 h12
    -- minimal element of S = {c' | c1 ≺ c' ∧ (c' = c2 ∨ c' ≺ c2)}
    obtain ⟨c', ⟨hc1, hc2⟩, hmin⟩ := wf'.has_min {c' | I.cprec c1 c' ∧ (c' = c2 ∨ I.cprec c' c2)}
      ⟨c2, h12, Or.inl rfl⟩
    have harc' : I.arc c' c1 := by
      refine ⟨hc1, ?_⟩
      rintro ⟨c'', h1, h2⟩
      exact hmin c'' ⟨h1, Or.inr (by rcases hc2 with rfl | h; exact h2; exact _root_.trans h2 h)⟩ h2
    have h1 := harc c' c1 harc'
    rcases hc2 with rfl | h
    · exact h1
    · exact (ih c' hc1 c2 h).trans h1

theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (κ : Integrality)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) (hxy : I.Feasible κ x y) :
    (∀ t, I.IsPit {b | 0 < cum x (I.clu b) t}) ∧
      ∀ t t', t ≤ t' → {b | 0 < cum x (I.clu b) t} ⊆ {b | 0 < cum x (I.clu b) t'} := by
  obtain ⟨hx, hle, harc, -, hy, -⟩ := hxy
  have hnn : ∀ c t, 0 ≤ x c t := by
    intro c t
    obtain ⟨b, rfl⟩ := hI.clu_surjective c
    rw [hx]
    exact Finset.sum_nonneg (fun d _ => hy b d t)
  refine ⟨?_, ?_⟩
  · intro t b1 b2 h12 h2
    have hc : I.cprec (I.clu b1) (I.clu b2) := ⟨b1, b2, rfl, rfl, h12⟩
    have := mm_chain I hI (fun c => cum x c t) (fun c c' h => harc c c' h t) _ _ hc
    exact lt_of_lt_of_le h2 this
  · intro t t' htt b hb
    have : cum x (I.clu b) t ≤ cum x (I.clu b) t' :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.2 htt)
        (fun i _ _ => hnn _ i)
    exact lt_of_lt_of_le hb this
