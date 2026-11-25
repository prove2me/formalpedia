-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.z_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:15:59.778886+00:00
-- url     : https://prove2.me/submissions/01e73e8e-b3ff-4088-a9b2-caee39df1a55

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace BL
section Lv2
variable {k r' : ℕ}
private lemma liftVec_apply_sh (v : Fin (2 * r' + k + 1) → ℂ) (q : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' v (sh q) = v q := by
  have h1 : 1 ≤ (sh q : Fin (2 * (1 + r') + k + 1)).val ∧
      (sh q : Fin (2 * (1 + r') + k + 1)).val < 2 * r' + k + 1 + 1 := by
    have := q.isLt
    simp only [sh, Fin.val_mk]
    omega
  simp only [liftVec]
  rw [dif_pos h1]
  exact congrArg v (Fin.ext (by simp [sh]))
end Lv2
end BL
end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (z : Fin (2 * (1 + r') + k + 1) → ℂ) (hz : inWb k (1 + r') z) :
    z = liftVec k 1 r' (fun q => z (sh q)) := by
  unfold inWb at hz
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    rw [hz p (by omega)]
    simp only [liftVec, dif_neg h0]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
