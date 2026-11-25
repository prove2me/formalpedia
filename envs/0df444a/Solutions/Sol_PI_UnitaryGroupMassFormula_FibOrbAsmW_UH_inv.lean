-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FibOrbAsmW.UH_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:26.854538+00:00
-- url     : https://prove2.me/submissions/c87ff960-2bcf-4f68-9ceb-35f66d88f523

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FibreOrbits_FibreOrbitOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_FibOrbAsmW_UH_det

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FibOrbAsmW
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace PI.UnitaryGroupMassFormula.FibOrbAsmW
theorem _root_.solution {H g : Matrix ι ι ℂ} (hH : IsUnit H.det) (hg : g ∈ UH H) : g⁻¹ ∈ UH H := by
  have hd := UH_det hH hg
  have hg' : gᴴ * H * g = H := hg
  have hd' : IsUnit gᴴ.det := by
    rw [det_conjTranspose, isUnit_iff_ne_zero, star_ne_zero, ← isUnit_iff_ne_zero]; exact hd
  show g⁻¹ᴴ * H * g⁻¹ = H
  rw [conjTranspose_nonsing_inv]
  calc gᴴ⁻¹ * H * g⁻¹ = gᴴ⁻¹ * (gᴴ * H * g) * g⁻¹ := by rw [hg']
    _ = (gᴴ⁻¹ * gᴴ) * H * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = H := by rw [nonsing_inv_mul _ hd', mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
end PI.UnitaryGroupMassFormula.FibOrbAsmW
