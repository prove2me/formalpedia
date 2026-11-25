-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.coreStar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:36.966664+00:00
-- url     : https://prove2.me/submissions/d59ad843-499c-4830-8398-845d1efd8142

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CCCNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CoreStarOf
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cD_list
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cD_delta
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_cD_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open PI PI.UnitaryCorollaryDerivatives
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace PI.UnitaryCorollaryDerivatives
theorem _root_.solution (hP : PolyB) (hDp : DjPoly) (hC : DjCurve) : CoreStar := by
  intro k j ρ Wp Wq _ _ _ _ _ o κ d Θ χ φ hΘ hχ Q mm₀ A₀ hQ hφ hφ0 hWBe
  obtain ⟨Cφ, hWB⟩ := hWBe
  have hD := (hP k (j + ρ) j (DjU k j ρ) (hDp k j ρ)).1
  obtain ⟨δ, hδ, hδχ⟩ := cD_delta hχ
  obtain ⟨C, _, hCg⟩ := cD_list (k := k) (j := j) (ρ := ρ) (Q := Q)
    (A₁ := A₀ - (κ : ℝ) - (j : ℝ) * (o : ℝ) - (d : ℝ) * ((Q + o : ℕ) : ℝ)) (O := {g | DjU k j ρ g ∉ tsupport χ})
    (fun (T : B.DTerm k (j + ρ) Wp Wq) (f : B.Mat k (j + ρ) → (Wq →L[ℂ] Wp)) =>
      ap T.coef (B.Rw T.word (fun g => φ g • f g)))
    (fun f c => B.CCle A₀ mm₀ f c) Θ
    (fun T hT => cD_term hP hC hD hχ hδ hδχ hφ hφ0 hWB hQ T (hΘ T hT))
  refine ⟨C, fun f c hf => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hCg f c hf
  refine ⟨h1, fun g hg hne => ?_, h3⟩
  by_contra hK
  exact hne (h2 g hg (fun hD' => hK ⟨_, hD', rfl⟩))
end PI.UnitaryCorollaryDerivatives
