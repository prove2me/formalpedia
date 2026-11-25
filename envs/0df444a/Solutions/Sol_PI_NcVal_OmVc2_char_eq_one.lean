-- Prove2me | solution 1 for PI.NcVal.OmVc2.char_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:18:26.98869+00:00
-- url     : https://prove2.me/submissions/7379b27a-8d31-42f5-9faf-bd696c5ad6dd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_MulTupDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc2
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct
namespace PI.NcVal.OmVc2
theorem _root_.solution {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G]
    (e p : G ≃ₜ+ G) (hp : ∀ x, p (p x) = x) (he : ∀ x, p (e (p x)) = e.symm x) :
    addEquivAddHaarChar e = 1 := by
  have h1 : e.symm = p.trans (e.trans p) := by
    ext x
    exact (he x).symm
  have h2 : p.trans p = ContinuousAddEquiv.refl G := by
    ext x
    exact hp x
  have hpp : addEquivAddHaarChar p * addEquivAddHaarChar p = 1 := by
    rw [← addEquivAddHaarChar_trans, h2, addEquivAddHaarChar_refl]
  have h3 : (addEquivAddHaarChar e)⁻¹ = addEquivAddHaarChar e := by
    rw [← addEquivAddHaarChar_symm, h1, addEquivAddHaarChar_trans, addEquivAddHaarChar_trans]
    calc addEquivAddHaarChar p * (addEquivAddHaarChar e * addEquivAddHaarChar p)
        = (addEquivAddHaarChar p * addEquivAddHaarChar p) * addEquivAddHaarChar e := by ring
      _ = addEquivAddHaarChar e := by rw [hpp, one_mul]
  have hpos := addEquivAddHaarChar_pos e
  have h4 : addEquivAddHaarChar e * addEquivAddHaarChar e = 1 := by
    calc addEquivAddHaarChar e * addEquivAddHaarChar e
        = addEquivAddHaarChar e * (addEquivAddHaarChar e)⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have h5 : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) * (addEquivAddHaarChar e : ℝ) = 1 := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (addEquivAddHaarChar e : ℝ) := (addEquivAddHaarChar e).2
  have hx : ((addEquivAddHaarChar e : ℝ≥0) : ℝ) = 1 := by
    rcases mul_self_eq_one_iff.1 h5 with h | h
    · exact h
    · linarith
  exact_mod_cast hx
end PI.NcVal.OmVc2
