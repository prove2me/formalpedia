-- Prove2me | solution 1 for SaddleSplit.Async.proposition_2_2_iii_iv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T16:24:38.304208+00:00
-- url     : https://prove2.me/submissions/2bb9816e-e3b0-4393-b9bd-8079c4c0c1b9

import Mathlib
import Definitions.Def_SaddleSplit_Async_Setting

open InnerProductSpace Filter Topology
open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR
open SaddleSplit.Async

theorem solution {I K : Type*} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    {H : I → Type*} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    {G : K → Type*} [∀ k, NormedAddCommGroup (G k)] [∀ k, InnerProductSpace ℝ (G k)]
    [∀ k, CompleteSpace (G k)]
    (prob : Problem H G) (hprob : prob.Hyp) :
    (∀ X ∈ zer (saddleOp prob), (pX X, pV X) ∈ ktSet prob) ∧
    ktSet prob ⊆ primalSet prob ×ˢ dualSet prob ∧
    ((dualSet prob).Nonempty ↔ (zer (saddleOp prob)).Nonempty) ∧
    ((zer (saddleOp prob)).Nonempty ↔ (ktSet prob).Nonempty) ∧
    ((ktSet prob).Nonempty → (primalSet prob).Nonempty) := by
  -- (iii) zeros of 𝓢 give Kuhn–Tucker points
  have h1 : ∀ X ∈ zer (saddleOp prob), (pX X, pV X) ∈ ktSet prob := by
    intro X hX
    obtain ⟨hx, hy, hz, hv⟩ := hX
    refine ⟨fun i => ?_, fun k => ?_⟩
    · obtain ⟨a, ha, he⟩ := hx i
      refine ⟨a, ha, ?_⟩
      have h0 : pX (0 : XSpace H G) i = 0 := rfl
      rw [h0] at he
      simp only
      rw [sub_eq_iff_eq_add]
      have := congrArg (fun w => w + prob.s i) he
      simp only [zero_add] at this
      rw [this]; abel
    · obtain ⟨b, hb, heb⟩ := hy k
      obtain ⟨d, hd, hed⟩ := hz k
      have hv0 := hv k
      have e0 : pY (0 : XSpace H G) k = 0 := rfl
      have e1 : pZ (0 : XSpace H G) k = 0 := rfl
      have e2 : pV (0 : XSpace H G) k = 0 := rfl
      rw [e0] at heb; rw [e1] at hed; rw [e2] at hv0
      refine ⟨pY X k, ?_, pZ X k, ?_, ?_⟩
      · show pV X k ∈ prob.Bsum k (pY X k)
        refine ⟨b + prob.Bc k (pY X k), ⟨b, hb, rfl⟩, ?_⟩
        have := congrArg (fun w => w + pV X k) heb
        simp only [zero_add, sub_add_cancel] at this
        exact this
      · show pV X k ∈ prob.Dsum k (pZ X k)
        refine ⟨d + prob.Dc k (pZ X k), ⟨d, hd, rfl⟩, ?_⟩
        have := congrArg (fun w => w + pV X k) hed
        simp only [zero_add, sub_add_cancel] at this
        exact this
      · show prob.Lx (pX X) k - prob.r k = pY X k + pZ X k
        have := hv0
        rw [eq_comm, sub_eq_zero] at this
        rw [← this]; abel
  -- Z ⊂ 𝒫 × 𝒟
  have h2 : ktSet prob ⊆ primalSet prob ×ˢ dualSet prob := by
    rintro ⟨x, v⟩ ⟨hx, hk⟩
    refine ⟨fun i => ⟨fun k => v k, fun k => hk k, ?_⟩, ⟨x, hx, fun k => hk k⟩⟩
    obtain ⟨a, ha, he⟩ := hx i
    refine ⟨a, ha, ?_⟩
    rw [sub_eq_iff_eq_add] at he
    rw [he]; rfl
  -- Z ≠ ∅ ⇒ zer 𝓢 ≠ ∅
  have h3 : (ktSet prob).Nonempty → (zer (saddleOp prob)).Nonempty := by
    rintro ⟨⟨x, v⟩, hx, hk⟩
    have hk' := fun k => hk k
    choose y hy z hz hyz using hk'
    refine ⟨mkX x (WithLp.toLp 2 y) (WithLp.toLp 2 z) v, ?_, ?_, ?_, ?_⟩
    · intro i
      obtain ⟨a, ha, he⟩ := hx i
      refine ⟨a, ha, ?_⟩
      show (0 : H i) = -prob.s i + a + prob.C i (x i) + prob.Q i (x i) + prob.R x i
        + prob.Ladj v i
      rw [sub_eq_iff_eq_add] at he
      rw [he]; abel
    · intro k
      obtain ⟨u, ⟨b, hb, rfl⟩, hu⟩ := hy k
      refine ⟨b, hb, ?_⟩
      show (0 : G k) = b + prob.Bc k (y k) + prob.Bl k (y k) - v k
      rw [hu]; abel
    · intro k
      obtain ⟨u, ⟨d, hd, rfl⟩, hu⟩ := hz k
      refine ⟨d, hd, ?_⟩
      show (0 : G k) = d + prob.Dc k (z k) + prob.Dl k (z k) - v k
      rw [hu]; abel
    · intro k
      show (0 : G k) = prob.r k + y k + z k - prob.Lx x k
      have := hyz k
      rw [sub_eq_iff_eq_add] at this
      rw [this]; abel
  have h4 : (zer (saddleOp prob)).Nonempty → (ktSet prob).Nonempty :=
    fun ⟨X, hX⟩ => ⟨_, h1 X hX⟩
  have h5 : (dualSet prob).Nonempty → (ktSet prob).Nonempty := by
    rintro ⟨v, x, hx, hk⟩
    exact ⟨(x, v), hx, hk⟩
  refine ⟨h1, h2, ⟨fun h => h3 (h5 h), fun h => ?_⟩, ⟨h4, h3⟩, ?_⟩
  · obtain ⟨p, hp⟩ := h4 h
    exact ⟨p.2, (h2 hp).2⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.1, (h2 hp).1⟩
