-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.norm_dmin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:13:50.123137+00:00
-- url     : https://prove2.me/submissions/ab0502c5-a9d2-4330-963e-2153b47246ff

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfJ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dOf_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dmin_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    ‖dmin X.Gm y τ i‖ = ∏ k ∈ range i, fδ X y τ k := by
  rw [dmin_prod X hy τ i, norm_prod, ← Fin.prod_univ_eq_prod_range (fδ X y τ)]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < r := lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ i.isLt)
  rw [fδ, dif_pos hj, δ]
  have hre := dOf_real X hy τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j)
  have hc : Fin.castLE (Nat.le_of_lt_succ i.isLt) j = (⟨j, hj⟩ : Fin r) := Fin.ext rfl
  rw [hc] at hre ⊢
  exact (Complex.abs_re_eq_norm.2 hre).symm
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
