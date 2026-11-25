-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.hpk_sh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:09.921103+00:00
-- url     : https://prove2.me/submissions/ef4f89ad-b343-4bef-ba53-7e49ea3f27c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
variable {k r' : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution (p q : Fin (2 * r' + k + 1)) : Hpk k (1 + r') (sh p) (sh q) = Hpk k r' p q := by
  simp only [Hpk, sh, Fin.ext_iff, Fin.val_mk]
  have e1 : (p.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (p.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e2 : (q.val + 1 < 1 + r' ∧ p.val + 1 + (q.val + 1) = 2 * (1 + r') + k) ↔
      (q.val < r' ∧ p.val + q.val = 2 * r' + k) := by
    constructor <;> intro h <;> omega
  have e3 : (1 + r' ≤ p.val + 1 ∧ p.val + 1 ≤ 1 + r' + k ∧ p.val + 1 = q.val + 1) ↔
      (r' ≤ p.val ∧ p.val ≤ r' + k ∧ p.val = q.val) := by
    constructor <;> intro h <;> omega
  have e4 : (p.val + 1 = 1 + r' + k) ↔ (p.val = r' + k) := by
    constructor <;> intro h <;> omega
  simp only [e1, e2, e3, e4]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
