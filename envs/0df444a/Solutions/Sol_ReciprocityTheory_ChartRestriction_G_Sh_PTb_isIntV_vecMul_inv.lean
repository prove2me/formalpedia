-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.PTb.isIntV_vecMul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:41:54.841836+00:00
-- url     : https://prove2.me/submissions/43542dbf-4913-482c-aba1-465dd3a987fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_TangentEqLcZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_EqZeroOfVecMulTmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_PTb_isIntV_tmat_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Sh ReciprocityTheory.ChartRestriction.G.Sh.PTb
open MvPowerSeries ReciprocityTheory.PGsh
noncomputable section
variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.Sh.PTb
theorem _root_.solution {γ : Fin d → Fin d → PowerSeries C} (hγ : ∀ a, IsCurve v (γ a))
    (hdet : v (tmat γ).det = 0) {w : Fin d → C} (hw : ∀ c, IsIntV v (w c)) (b : Fin d) :
    IsIntV v (Matrix.vecMul w (tmat γ)⁻¹ b) := by
  let S : Subring C :=
    { carrier := {x | 0 ≤ v x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, AddValuation.map_mul] at *
        exact add_nonneg ha hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (AddValuation.map_add v a b)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa [AddValuation.map_neg] using ha }
  have hmem : Matrix.vecMul w (tmat γ)⁻¹ b ∈ S := by
    simp only [Matrix.vecMul, dotProduct]
    exact S.sum_mem fun c _ => S.mul_mem (hw c) (isIntV_tmat_inv hγ hdet c b)
  exact hmem
end ReciprocityTheory.ChartRestriction.G.Sh.PTb
