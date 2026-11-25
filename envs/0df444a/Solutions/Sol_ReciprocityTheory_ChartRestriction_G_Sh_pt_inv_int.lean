-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.pt_inv_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:36.615221+00:00
-- url     : https://prove2.me/submissions/212b1957-18c9-4c83-b6f4-2819e70a9895

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTAgree_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh
open MvPowerSeries ReciprocityTheory.PGsh
open Classical
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh
theorem _root_.solution {M : Matrix (Fin d) (Fin d) C} (hM : ∀ i j, M i j ∈ ptIntSub v)
    (hdet : v M.det = 0) : IsUnit M.det ∧ ∀ i j, M⁻¹ i j ∈ ptIntSub v := by
  have hdet0 : M.det ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hdet
    exact WithTop.top_ne_coe hdet
  refine ⟨isUnit_iff_ne_zero.mpr hdet0, fun i j => ?_⟩
  obtain ⟨M', rfl⟩ : ∃ M' : Matrix (Fin d) (Fin d) (ptIntSub v), M = M'.map (ptIntSub v).subtype :=
    ⟨fun i j => ⟨M i j, hM i j⟩, by ext i j; rfl⟩
  have hadj : (M'.map (ptIntSub v).subtype).adjugate i j = (ptIntSub v).subtype (M'.adjugate i j) :=
    (congrArg (fun N : Matrix (Fin d) (Fin d) C => N i j) (RingHom.map_adjugate (ptIntSub v).subtype M')).symm
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, hadj, Ring.inverse_eq_inv']
  refine (ptIntSub v).mul_mem ?_ (M'.adjugate i j).2
  show 0 ≤ v (M'.map (ptIntSub v).subtype).det⁻¹
  rw [AddValuation.map_inv, hdet, neg_zero]
end ReciprocityTheory.ChartRestriction.G.Sh
