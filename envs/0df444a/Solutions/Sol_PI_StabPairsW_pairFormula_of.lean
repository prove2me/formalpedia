-- Prove2me | solution 1 for PI.StabPairsW.pairFormula_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:09:58.466409+00:00
-- url     : https://prove2.me/submissions/099cb2ed-f8bb-411b-a2fb-627605895bfd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_IsUnitDetOfMemGV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerPairs_Forward
import Theorems.Thm_PI_StabPairsW_Sset_frame
import Theorems.Thm_PI_StabPairsW_rho_conj
import Theorems.Thm_PI_StabPairsW_mul_eq_of_fix
import Theorems.Thm_PI_StabPairsW_Fm_eq
import Theorems.Thm_PI_StabPairsW_gramM_eq


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
theorem _root_.solution (hG : GramInv) : PairFormula := by
  intro k r z z' γ hs hp ρ hρ
  obtain ⟨⟨hρS, s', hs', hρeq⟩, hfix⟩ := hρ
  obtain ⟨-, hρF, -⟩ := Sset_frame z hs.2.1 ρ hρS
  obtain ⟨-, hsF, -⟩ := Sset_frame z' hs.2.2 s' hs'
  obtain ⟨hc1, hc2⟩ := rho_conj γ hp.1 ρ s' hρeq
  have hGinv : gramM k r z z' γ * (gramM k r z z' γ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (hG k r z z' γ hs hp)
  have hρFm : ρ * Fm k r z z' γ =
      Fm k r z z' γ * Wm (uMap k r z ρ) (uMap k r z' (γ⁻¹ * ρ * γ)) := by
    rw [hc1, Fm_eq, Wm, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, add_zero, zero_add]
    congr 1
    all_goals first
      | exact hρF
      | rw [← Matrix.mul_assoc, ← hc2, Matrix.mul_assoc, hsF, Matrix.mul_assoc]
  have hQ : ((Fm k r z z' γ)ᴴ * Hpk k r) * (1 - Fm k r z z' γ * Km k r z z' γ) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Km]
    have e : (Fm k r z z' γ)ᴴ * Hpk k r *
        (Fm k r z z' γ * ((gramM k r z z' γ)⁻¹ * (Fm k r z z' γ)ᴴ * Hpk k r)) =
        ((Fm k r z z' γ)ᴴ * Hpk k r * Fm k r z z' γ) * (gramM k r z z' γ)⁻¹ *
          ((Fm k r z z' γ)ᴴ * Hpk k r) := by
      simp only [Matrix.mul_assoc]
    rw [e, ← gramM_eq, hGinv, Matrix.one_mul, sub_self]
  have hfixQ := mul_eq_of_fix z z' γ ρ hfix _ hQ
  calc ρ = ρ * (Fm k r z z' γ * Km k r z z' γ) + ρ * (1 - Fm k r z z' γ * Km k r z z' γ) := by
        rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_one]
    _ = Fm k r z z' γ * Wm (uMap k r z ρ) (uMap k r z' (γ⁻¹ * ρ * γ)) * Km k r z z' γ +
          (1 - Fm k r z z' γ * Km k r z z' γ) := by
        rw [hfixQ, ← Matrix.mul_assoc, hρFm]
    _ = rhoOf k r z z' γ (pairMap k r z z' γ ρ).1 (pairMap k r z z' γ ρ).2 := by
        simp only [rhoOf, pairMap, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
        abel
end PI.StabPairsW
