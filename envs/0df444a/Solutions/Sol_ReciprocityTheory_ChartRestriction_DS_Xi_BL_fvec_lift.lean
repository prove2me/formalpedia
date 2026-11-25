-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.BL.fvec_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:48.327085+00:00
-- url     : https://prove2.me/submissions/0b7f2972-a2bd-4c76-b214-7cef4b88e8a3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LevelDeterminantOfTriangularChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianFormLiftVecFirstVector
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_BL_eI_succ
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
private lemma liftVec_bvec_eq_bvec_sh (i : Fin (2 * r' + k + 1)) :
    liftVec k 1 r' (bvec i) = bvec (sh i) := by
  funext p
  by_cases hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k
  · have h0 : ¬(1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := by omega
    have hne : p ≠ sh i := by
      intro he
      rw [he] at hp
      have := i.isLt
      simp only [sh, Fin.val_mk] at hp
      omega
    simp only [liftVec, dif_neg h0, bvec, Pi.single_apply, if_neg hne]
  · have hp' : p = sh ⟨p.val - 1, by have := p.isLt; omega⟩ := by
      ext
      simp only [sh, Fin.val_mk]
      omega
    rw [hp', liftVec_apply_sh]
    simp [bvec, Pi.single_apply, sh, Fin.ext_iff]
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
theorem _root_.solution (z1 : Fin (2 * r' + k + 1) → ℂ) (a : Fin (1 + r')) :
    fvec k (1 + r') (liftVec k 1 r' z1) ⟨a.val + 1, by omega⟩ = liftVec k 1 r' (fvec k r' z1 ⟨a.val, by omega⟩) := by
  by_cases ha : a.val < r'
  · have h1 : a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_pos h1, dif_pos ha]
    rw [eI_succ a.val h1]
    exact (liftVec_bvec_eq_bvec_sh _).symm
  · have h1 : ¬ a.val + 1 < 1 + r' := by omega
    simp only [fvec, Fin.val_mk, dif_neg h1, dif_neg ha]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
