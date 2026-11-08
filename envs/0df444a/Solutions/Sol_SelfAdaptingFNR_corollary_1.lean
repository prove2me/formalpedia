-- Prove2me | solution 1 for SelfAdaptingFNR.corollary_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:57:06.798594+00:00
-- url     : https://prove2.me/submissions/595171e5-e7fe-40e9-b812-9c5803f528d6

import Mathlib
import Definitions.Def_SelfAdaptingFNR_slackNetwork

open scoped Classical

namespace Aux_SelfAdaptingFNR_corollary_1
open SelfAdaptingFNR

theorem sv_succ {J K T : ℕ} (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (j : Fin J) :
    M.slackValue t s a j.succ = fun k => M.slackValue t s a j.castSucc k - M.C t k j (s j) (a j) := by
  funext k
  simp only [WDP.slackValue]
  have : Finset.univ.filter (fun j' : Fin J => (j' : ℕ) < (j.succ : ℕ)) =
      insert j (Finset.univ.filter (fun j' : Fin J => (j' : ℕ) < (j.castSucc : ℕ))) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.coe_castSucc, Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp)]; ring

theorem sv_zero {J K T : ℕ} (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (i : Fin (J + 1)) (hi : (i : ℕ) = 0) :
    M.slackValue t s a i = M.b := by
  funext k
  simp only [WDP.slackValue, hi]
  simp

theorem sv_last {J K T : ℕ} (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (k : Fin K) :
    M.slackValue t s a (Fin.last J) k = M.b k - ∑ j, M.C t k j (s j) (a j) := by
  simp only [WDP.slackValue]
  rw [Finset.filter_true_of_mem (fun j _ => by simp)]

theorem nonneg_of_mem {J K T : ℕ} (M : WDP J K T) (t : ℕ) (ht : t < T)
    (u : Fin K → ℝ) (hu : u ∈ M.slackLayer t (Fin.last J)) (k : Fin K) : 0 ≤ u k := by
  unfold WDP.slackLayer at hu
  split_ifs at hu with hJ
  · rw [Finset.mem_singleton] at hu
    subst hu
    have hJ' : J = 0 := by simpa using hJ
    subst hJ'
    obtain ⟨a, _, hb⟩ := M.A_nonempty t ht (fun j => j.elim0)
    simpa using hb k
  · rw [Finset.mem_image] at hu
    obtain ⟨⟨s', a'⟩, hm, rfl⟩ := hu
    rw [Finset.mem_filter] at hm
    have hC := hm.2.2 k
    rw [sv_last]; linarith

theorem mem_layer {J K T : ℕ} (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (hf : (s, a) ∈ M.feasiblePairs t) (i : Fin (J + 1)) :
    M.slackValue t s a i ∈ M.slackLayer t i := by
  unfold WDP.slackLayer
  split_ifs with hi
  · rw [sv_zero M t s a i hi]; exact Finset.mem_singleton_self _
  · rw [Finset.mem_image]
    exact ⟨(s, a), by simp [hf], rfl⟩

end Aux_SelfAdaptingFNR_corollary_1

open SelfAdaptingFNR Aux_SelfAdaptingFNR_corollary_1 in
theorem solution {J K T : ℕ} (M : WDP J K T) (t : ℕ) (ht : t < T) :
    (M.slackNetwork t).IsFeasibilityNetwork := by
  constructor
  · rintro ⟨⟨np, s, a⟩, hp0, hps⟩ ⟨⟨nq, s', a'⟩, hq0, hqs⟩ h
    dsimp only at hp0 hps hq0 hqs
    simp only [LayeredNetwork.Path.labels, LayeredNetwork.Path.st, LayeredNetwork.Path.act,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hn : np = nq := by
      funext i
      induction i using Fin.induction with
      | zero => rw [hp0, hq0]
      | succ j ih =>
        have := (hps j).symm.trans
          ((congrArg (fun v => (M.slackNetwork t).succ j v (s j) (a j)) ih).trans (hqs j))
        exact Option.some_injective _ this
    subst hn; rfl
  · ext ⟨s, a⟩
    constructor
    · rintro ⟨⟨⟨np, s', a'⟩, hp0, hps⟩, h⟩
      dsimp only at hp0 hps
      simp only [LayeredNetwork.Path.labels, LayeredNetwork.Path.st, LayeredNetwork.Path.act,
        Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hval : ∀ i, (np i).1 = M.slackValue t s' a' i := by
        intro i
        induction i using Fin.induction with
        | zero =>
          rw [hp0, sv_zero M t s' a' 0 rfl] <;> rfl
        | succ j ih =>
          have h := hps j
          simp only [WDP.slackNetwork] at h
          split_ifs at h with hc
          all_goals first
            | exact absurd h (by simp)
            | rw [← Option.some_injective _ h, sv_succ, ← ih]
      have hA : ∀ j, a' j ∈ M.A t j (s' j) := fun j =>
        (M.slackNetwork t).succ_feasible j _ _ _ _ (hps j)
      refine ⟨hA, fun k => ?_⟩
      have hl := (np (Fin.last J)).2
      rw [hval] at hl
      have := nonneg_of_mem M t ht _ hl k
      rw [sv_last] at this
      linarith
    · intro hf
      refine ⟨⟨⟨fun i => ⟨M.slackValue t s a i, mem_layer M t s a hf i⟩, s, a⟩, ?_, ?_⟩, rfl⟩
      · apply Subtype.ext
        exact sv_zero M t s a 0 rfl
      · intro j
        simp only [WDP.slackNetwork]
        rw [dif_pos ⟨hf.1 j, by rw [← sv_succ]; exact mem_layer M t s a hf _⟩]
        congr 1
        apply Subtype.ext
        exact (sv_succ M t s a j).symm
