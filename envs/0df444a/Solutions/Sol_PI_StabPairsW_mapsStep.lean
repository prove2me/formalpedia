-- Prove2me | solution 1 for PI.StabPairsW.mapsStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:03:52.715573+00:00
-- url     : https://prove2.me/submissions/6223c24b-b4e0-4c71-9710-09d16522772b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Theorems.Thm_PI_StabPairsW_Sset_frame
import Theorems.Thm_PI_StabPairsW_rho_conj
import Theorems.Thm_PI_StabPairsW_Zhat_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.StabPairsW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {k r : ℕ}
namespace PI.StabPairsW
theorem _root_.solution : MapsStep := by
  intro k r z z' γ hs hp ρ hρ
  obtain ⟨⟨hρS, s', hs', hρeq⟩, -⟩ := hρ
  obtain ⟨hρG, hρF, hρU⟩ := Sset_frame z hs.2.1 ρ hρS
  obtain ⟨-, hsF, hsU⟩ := Sset_frame z' hs.2.2 s' hs'
  obtain ⟨hc1, hc2⟩ := rho_conj γ hp.1 ρ s' hρeq
  have hρH : ρᴴ * Hpk k r * ρ = Hpk k r := hρG
  refine ⟨hρU, ?_, ?_⟩
  · show uMap k r z' (γ⁻¹ * ρ * γ) ∈ UTset (r + 1)
    rw [hc1]
    exact hsU
  · show (uMap k r z ρ)ᴴ * Zhat k r z z' γ * uMap k r z' (γ⁻¹ * ρ * γ) = Zhat k r z z' γ
    rw [hc1, Zhat_eq]
    calc (uMap k r z ρ)ᴴ * ((Ff k r z)ᴴ * Hpk k r * γ * Ff k r z') * uMap k r z' s'
        = (Ff k r z * uMap k r z ρ)ᴴ * Hpk k r * γ * (Ff k r z' * uMap k r z' s') := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (ρ * Ff k r z)ᴴ * Hpk k r * (γ * s') * Ff k r z' := by
          rw [← hρF, ← hsF]
          simp only [Matrix.mul_assoc]
      _ = (Ff k r z)ᴴ * (ρᴴ * Hpk k r * ρ) * γ * Ff k r z' := by
          rw [hc2, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = (Ff k r z)ᴴ * Hpk k r * γ * Ff k r z' := by rw [hρH]
end PI.StabPairsW
