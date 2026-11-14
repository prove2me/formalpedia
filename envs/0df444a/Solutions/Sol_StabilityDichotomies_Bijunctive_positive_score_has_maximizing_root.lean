-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.positive_score_has_maximizing_root
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:38:18.628595+00:00
-- url     : https://prove2.me/submissions/69f24cb0-2954-4a7e-9f81-06704666d0e5

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (target : Literal V) (hpos : (0 : WithBot ℝ) < literalScore rep G F δ target) :
    ∃ root : Literal V, ∃ n : ℕ, feasibleLiteral F root ∧
      implicationDistance rep G root target = some n ∧
      literalScore rep G F δ target = ((δ root - n : ℝ) : WithBot ℝ) ∧
      ∀ r : Literal V, ∀ m : ℕ, feasibleLiteral F r →
        implicationDistance rep G r target = some m → δ r - m ≤ δ root - n := by
  classical
  let f : Literal V → WithBot ℝ := fun root =>
    if feasibleLiteral F root then
      match implicationDistance rep G root target with
      | some n => ((δ root - n : ℝ) : WithBot ℝ)
      | none => ⊥
    else ⊥
  have hun : (Finset.univ : Finset (Literal V)).Nonempty := by
    by_contra h
    have he : (Finset.univ : Finset (Literal V)) = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hs : literalScore rep G F δ target = ⊥ := by simp [literalScore,he]
    rw [hs] at hpos
    exact not_lt_of_ge bot_le hpos
  obtain ⟨root,_,hmax⟩ := Finset.exists_mem_eq_sup Finset.univ hun f
  have hs : literalScore rep G F δ target = f root := hmax
  have hbot : f root ≠ ⊥ := by
    intro hb
    rw [hs,hb] at hpos
    exact not_lt_of_ge bot_le hpos
  have hfeas : feasibleLiteral F root := by
    by_contra h; simp [f,h] at hbot
  cases hdist : implicationDistance rep G root target with
  | none => simp [f,hfeas,hdist] at hbot
  | some n =>
    refine ⟨root,n,hfeas,hdist,?_,?_⟩
    · simpa [f,hfeas,hdist] using hs
    · intro r m hfr hdr
      have hle : f r ≤ f root := by
        rw [← hmax]
        exact Finset.le_sup (Finset.mem_univ r)
      simpa [f,hfr,hdr,hfeas,hdist] using hle
