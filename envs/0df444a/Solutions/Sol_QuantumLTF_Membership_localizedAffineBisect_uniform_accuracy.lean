-- Prove2me | solution 1 for QuantumLTF.Membership.localizedAffineBisect_uniform_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T20:08:16.946489+00:00
-- url     : https://prove2.me/submissions/bac63264-37bd-4280-a4b6-edccf63bd563

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QuantumLTF_Membership_affineBoundaryBisect
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_height
import Definitions.Def_QuantumLTF_Membership_rho
import Definitions.Def_QuantumLTF_Membership_gridVec
import Theorems.Thm_QuantumLTF_Membership_localizedAffineBisect_error
import Theorems.Thm_QuantumLTF_Membership_local_bisection_parameters

open QAlgorithms
open QuantumLTF.Membership

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ {n b : ℕ}, 2 ≤ n → ∀ ε η : ℝ,
      0 < ε → ε ≤ 1 / 2 → 0 < η → η < 1 / 8 →
      ∀ (w p : EuclideanSpace ℝ (Fin n)) (θ htil : ℝ),
        ‖w‖ = 1 → 1 / 10 ≤ |inner ℝ w p| →
        |htil - height w θ p 0| ≤ ε / 100 →
        ∃ q : ℕ, (q : ℝ) ≤ C * Real.log (1 / η) ∧
          ∀ x : Fin n → Qubits b,
            |(affineBoundaryBisect p (rho n • gridVec n b x) (sgn (inner ℝ w p)) q
                (htil - 1 / 4) (htil + 1 / 4)).run (ltf w θ) -
              height w θ p (rho n • gridVec n b x)| ≤ η := by
  obtain ⟨C, hC, hparams⟩ := local_bisection_parameters
  refine ⟨C, hC, ?_⟩
  intro n b hn ε η hε hε2 hη hη8 w p θ htil hw ha hhtil
  obtain ⟨q, hq, hqerr⟩ := hparams η hη hη8
  refine ⟨q, hq, ?_⟩
  intro x
  exact (localizedAffineBisect_error hn ε hε hε2 w p θ htil hw ha hhtil x q).trans hqerr

