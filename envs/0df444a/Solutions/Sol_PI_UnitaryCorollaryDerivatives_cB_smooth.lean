-- Prove2me | solution 1 for PI.UnitaryCorollaryDerivatives.cB_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:35:36.465591+00:00
-- url     : https://prove2.me/submissions/bed1e667-4434-4419-8c98-6113c7035cf0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CADwlSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CBLamnorm

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
theorem _root_.solution {k j ρ : ℕ} (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (DjU k j ρ)) {P : B.Mat k (j + ρ) → ℂ}
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P) (a b : ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => P g * (DjU k j ρ g)⁻¹ ^ a * (star (DjU k j ρ g))⁻¹ ^ b)
      {g | DjU k j ρ g ≠ 0} := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (DjU k j ρ g)⁻¹) {g | DjU k j ρ g ≠ 0} :=
    hD.contDiffOn.inv (fun g hg => hg)
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => star (DjU k j ρ g)) := by
    have := Complex.conjCLE.contDiff.comp hD
    simpa [Function.comp_def, Complex.star_def] using this
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun g => (star (DjU k j ρ g))⁻¹) {g | DjU k j ρ g ≠ 0} :=
    hs.contDiffOn.inv (fun g hg => by simpa using hg)
  exact (hP.contDiffOn.mul (h1.pow a)).mul (h2.pow b)
end PI.UnitaryCorollaryDerivatives
