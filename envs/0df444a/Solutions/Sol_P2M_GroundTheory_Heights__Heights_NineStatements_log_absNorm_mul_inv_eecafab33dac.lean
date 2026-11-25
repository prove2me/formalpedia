-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_mul_inv_eecafab33dac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:59.599073+00:00
-- url     : https://prove2.me/submissions/7eaca76c-f100-4dab-bbbd-3acd01e6e9d6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
namespace GroundTheory.Heights₂.Heights.NineStatements
theorem _root_.solution {L : Type} [Field L] [NumberField L] {a b : FractionalIdeal (𝓞 L)⁰ L}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log (FractionalIdeal.absNorm (a * b⁻¹) : ℝ) =
      Real.log (FractionalIdeal.absNorm a : ℝ) - Real.log (FractionalIdeal.absNorm b : ℝ) := by
  have ha' : (FractionalIdeal.absNorm a : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr ha)
  have hb' : (FractionalIdeal.absNorm b : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.mpr hb)
  rw [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, Real.log_mul ha' (inv_ne_zero hb'), Real.log_inv]
  ring
end GroundTheory.Heights₂.Heights.NineStatements
