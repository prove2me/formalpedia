-- Prove2me | solution 1 for OnlineRandomization.Tightness.offline_forces_ratio
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T05:40:07.059435+00:00
-- url     : https://prove2.me/submissions/d2c46ccf-d738-43d2-84b1-15099f009d04

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame



namespace OnlineRandomization.Tightness

open MeasureTheory

def offQ {t : ℕ} (x0 : Fin t × Bool) : OfflineAdv (Fin t × Bool) (Fin t × Bool) where
  next a := match a with
    | [] => some x0
    | [a1] => some (mate a1)
    | _ :: _ :: _ => none
  depth := 2
  stop_of_le a h := by
    match a, h with
    | _ :: _ :: _, _ => rfl

lemma mate_ne {t : ℕ} (x : Fin t × Bool) : x ≠ mate x := by
  intro h
  have := congrArg Prod.snd h
  simp [mate] at this

lemma mate_mate {t : ℕ} (x : Fin t × Bool) : mate (mate x) = x := by
  simp [mate]

lemma play_offQ {t : ℕ} (x0 : Fin t × Bool) (G : DetAlg (Fin t × Bool) (Fin t × Bool)) :
    play G (offQ x0) = ([x0, mate (G [x0])], [G [x0], G [x0, mate (G [x0])]]) := by
  simp [play, offQ, playAux]

lemma opt_two {t : ℕ} [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M) (x y : Fin t × Bool) :
    (matesGame t m M).opt [x, y] = 1 := by
  unfold Game.opt
  apply le_antisymm
  · have := Finset.inf'_le (s := Finset.univ) (fun a : Fin [x, y].length → Fin t × Bool =>
      (matesGame t m M).cost [x, y] (List.ofFn a)) (Finset.mem_univ (fun _ => y))
    refine this.trans (le_of_eq ?_)
    simp [matesGame, matesCost, pairCost, List.ofFn_succ]
  · apply Finset.le_inf'
    intro a _
    simp only [matesGame, List.length_cons, List.length_nil, List.ofFn_succ, matesCost, pairCost]
    split_ifs <;> linarith

theorem offline_core (t : ℕ) [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (Ω : Type) [MeasurableSpace Ω] (K : RandAlg (Fin t × Bool) (Fin t × Bool) Ω) :
    ∃ Q : OfflineAdv (Fin t × Bool) (Fin t × Bool),
      ∫ ω, algCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = M ∧
      ∫ ω, advCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = 1 := by
  have := K.isProb
  refine ⟨offQ (0, false), ?_, ?_⟩
  · have : ∀ ω, algCostOffline (matesGame t m M) (K.alg ω) (offQ (0, false)) = M := by
      intro ω
      simp only [algCostOffline, play_offQ, matesGame, matesCost, pairCost]
      rw [if_neg (mate_ne _), if_pos (mate_mate _).symm]
    simp [this]
  · have : ∀ ω, advCostOffline (matesGame t m M) (K.alg ω) (offQ (0, false)) = 1 := by
      intro ω
      simp only [advCostOffline, play_offQ]
      exact opt_two m M hm hmM _ _
    simp [this]

end OnlineRandomization.Tightness

open OnlineRandomization.Tightness


theorem solution (t : ℕ) [NeZero t] (m M : ℝ) (hm : 1 ≤ m) (hmM : m ≤ M)
    (Ω : Type) [MeasurableSpace Ω] (K : RandAlg (Fin t × Bool) (Fin t × Bool) Ω) :
    ∃ Q : OfflineAdv (Fin t × Bool) (Fin t × Bool),
      ∫ ω, algCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = M ∧
      ∫ ω, advCostOffline (matesGame t m M) (K.alg ω) Q ∂K.μ = 1 := by
  exact offline_core t m M hm hmM Ω K
