-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:52:42.427228+00:00
-- url     : https://prove2.me/submissions/9bb2c69b-f6e2-41c3-b602-f482a89ddcf6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_continuous_DjU
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_mem_steps
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_RdV_eq_Dx
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_step_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_congr_loc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U Formalism.REAL Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution : Expand := by
  intro k j ρ E _ _ m F hF w
  induction w with
  | nil => intro L _ _ _ g _ _; rfl
  | cons X w ih =>
    intro L hw hL hm g hg hD
    have hO : IsOpen {g : Mat k (j + ρ) | DjU k j ρ g ≠ 0} :=
      isOpen_ne_fun (continuous_DjU k j ρ) continuous_const
    have hIH : ∀ g' ∈ GV k (j + ρ), g' ∈ {g : Mat k (j + ρ) | DjU k j ρ g ≠ 0} →
        Rw w (shape k j ρ F L) g' = shape k j ρ F (steps k j ρ w L) g' :=
      fun g' hg' hg'O => ih L (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) hL
        (fun e he => by have := hm e he; simp only [List.length_cons] at this; omega) g' hg' hg'O
    have hX := hw X List.mem_cons_self
    show RdV X (Rw w (shape k j ρ F L)) g = shape k j ρ F (step k j ρ X (steps k j ρ w L)) g
    rw [RdV_eq_Dx, Dx_congr_loc (x := (false, X)) hX hO hIH g hg hD, ← RdV_eq_Dx]
    refine step_eq hF hX (fun e he Y hY => ?_) (fun e he => ?_) hg hD
    · obtain ⟨e₀, he₀, _, hm'⟩ := mem_steps he
      rcases hm' Y hY with h | h
      · exact hL e₀ he₀ Y h
      · exact hw Y (List.mem_cons_of_mem _ h)
    · obtain ⟨e₀, he₀, hl, _⟩ := mem_steps he
      have := hm e₀ he₀
      simp only [List.length_cons] at this
      omega
end PI.UnitaryGroupMassFormula.UsCompose
