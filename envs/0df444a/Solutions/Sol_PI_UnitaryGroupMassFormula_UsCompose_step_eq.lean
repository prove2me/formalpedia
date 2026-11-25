-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCompose.step_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:39:09.257997+00:00
-- url     : https://prove2.me/submissions/23f08a54-671e-4539-9864-dd943dba152a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_listSum
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_RdV_eq_Dx
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_ck_Rw
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_diff
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_hasDerivAt_sv
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_shape_flatMap


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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.UnitaryGroupMassFormula.UsCompose
theorem _root_.solution {k j ρ m : ℕ} {F : Mat k (j + ρ) → E} (hF : CkOn (m : ℕ∞) (GV k (j + ρ)) F)
    {X : Mat k (j + ρ)} (hX : inLie k (j + ρ) X) {L : FS k (j + ρ)}
    (hL : ∀ e ∈ L, ∀ Y ∈ e.2, inLie k (j + ρ) Y) (hm : ∀ e ∈ L, e.2.length + 1 ≤ m)
    {g : Mat k (j + ρ)} (hg : g ∈ GV k (j + ρ)) (hD : DjU k j ρ g ≠ 0) :
    RdV X (shape k j ρ F L) g = shape k j ρ F (step k j ρ X L) g := by
  have hterm : ∀ e ∈ L, HasDerivAt
      (fun t => sv k j ρ e.1 (crv (false, X) g t) • Rw e.2 F (crv (false, X) g t))
      (sv k j ρ e.1 g • Dx (false, X) (Rw e.2 F) g +
        (sv k j ρ (dP X e.1.1, e.1.2.1, e.1.2.2) g
          + sv k j ρ (C (-(e.1.2.1 : ℂ)) * e.1.1 * dP X (qD k j ρ), e.1.2.1 + 1, e.1.2.2) g
          + sv k j ρ (C (-(e.1.2.2 : ℂ)) * e.1.1 * dP X (qDb k j ρ), e.1.2.1, e.1.2.2 + 1) g)
          • Rw e.2 F g) 0 := by
    intro e he
    have h1 := hasDerivAt_sv X g hD e.1
    have hc := ck_Rw hF (hL e he) 1 (by have := hm e he; omega)
    rw [Nat.cast_one] at hc
    have h2 : HasDerivAt (fun t => Rw e.2 F (crv (false, X) g t)) (Dx (false, X) (Rw e.2 F) g) 0 :=
      CkOn_diff (x := (false, X)) hX hc hg hg
    have h3 := h1.smul h2
    simp only [crv_zero] at h3
    exact h3
  have hsum := hasDerivAt_listSum L _ _ hterm
  have hsum' : HasDerivAt (fun t => shape k j ρ F L (crv (false, X) g t)) _ 0 := hsum
  rw [RdV_eq_Dx, Dx_eq, hsum'.deriv, step, shape_flatMap]
  congr 1
  apply List.map_congr_left
  intro e _
  simp only [shape, stepOne, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [show Rw (X :: e.2) F g = Dx (false, X) (Rw e.2 F) g by rw [← RdV_eq_Dx]; rfl]
  simp only [add_smul]
  abel
end PI.UnitaryGroupMassFormula.UsCompose
