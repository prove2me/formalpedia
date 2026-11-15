-- Prove2me | solution 1 for QuantumLTF.Membership.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:51:14.464511+00:00
-- url     : https://prove2.me/submissions/296ad80f-53b4-46bd-8f6b-0dcaa06991cc

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_Leps
import Definitions.Def_QuantumLTF_Membership_IsFp
import Definitions.Def_QuantumLTF_Membership_QueryTree
import Definitions.Def_QuantumLTF_Membership_boundarySearchTreeStrict
import Definitions.Def_QuantumLTF_Membership_orientedBisectValue
import Theorems.Thm_QuantumLTF_Membership_theorem_3_1_parameters
import Theorems.Thm_QuantumLTF_Membership_boundarySearchTreeStrict_run
import Theorems.Thm_QuantumLTF_Membership_boundarySearchTreeStrict_depth
import Theorems.Thm_QuantumLTF_Membership_orientedBisectValue_error
import Theorems.Thm_QuantumLTF_Membership_orientedBisectValue_isFp_pow_two

open QuantumLTF.Membership

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ε ζ : ℝ, 0 < ε → ε ≤ 1 / 2 → 0 < ζ → ζ < 1 →
      ∀ p : EuclideanSpace ℝ (Fin n),
        ∃ (B f : ℕ) (T : QueryTree n (ℤ × ℝ)),
          (T.depth : ℝ) ≤ C * Real.log (Leps ε / ζ) ∧ (B : ℝ) ≤ C * Real.log (Leps ε / ζ) ∧
          ∀ (w : EuclideanSpace ℝ (Fin n)) (θ : ℝ), ‖w‖ = 1 →
            1 / 10 ≤ |inner ℝ w p| → |inner ℝ w p| ≤ 3 → |height w θ p 0| ≤ Leps ε →
              (T.run (ltf w θ)).1 = sgn (inner ℝ w p) ∧
              |(T.run (ltf w θ)).2 - height w θ p 0| ≤ ζ ∧
              IsFp B f (T.run (ltf w θ)).2 := by
  rcases theorem_3_1_parameters with ⟨C, hC, hparams⟩
  refine ⟨C, hC, ?_⟩
  intro n hn ε ζ hε hε' hζ hζ' p
  rcases hparams ε ζ hε hε' hζ hζ' with ⟨m, q, hL, hdepth, hbits, herr⟩
  refine ⟨m + q + 2, q + 1, boundarySearchTreeStrict p (Leps ε) q, ?_, ?_, ?_⟩
  · simpa [boundarySearchTreeStrict_depth] using hdepth
  · exact hbits
  · intro w θ hw hlo hhi hh
    have ha : inner ℝ w p ≠ 0 := by
      intro ha0
      rw [ha0, abs_zero] at hlo
      norm_num at hlo
    rw [boundarySearchTreeStrict_run w p θ (Leps ε) q ha hh]
    simp only [Prod.fst, Prod.snd]
    refine ⟨trivial, ?_, ?_⟩
    · calc
        |orientedBisectValue (sgn (inner ℝ w p)) q (-Leps ε) (Leps ε)
            (height w θ p 0) - height w θ p 0| ≤
            (Leps ε - (-Leps ε)) / (2 : ℝ) ^ (q + 1) :=
          orientedBisectValue_error _ _ _ _ _ (abs_le.mp hh).1 (abs_le.mp hh).2
        _ = 2 * Leps ε / (2 : ℝ) ^ (q + 1) := by ring
        _ ≤ ζ := herr
    · rw [hL]
      exact orientedBisectValue_isFp_pow_two (sgn (inner ℝ w p)) m q (height w θ p 0)
