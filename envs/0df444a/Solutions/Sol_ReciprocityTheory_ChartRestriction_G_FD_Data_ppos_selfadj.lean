-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_selfadj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:46.708212+00:00
-- url     : https://prove2.me/submissions/cd37b34c-64d2-40b8-b65a-7aa70227336b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowFixesComplementOfIsotropic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UnitaryComplementMoveOfIsotropic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_det_ne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_orth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_sum_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hC_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hA := gramPos_det_ne X hx τ
  have hsymm : ∀ v v', hermC τ.1 X.Gm v v' = conj (hermC τ.1 X.Gm v' v) := fun v v' =>
    hC_symm τ.1 X.Gm X.Gm_herm v' v

  have hspan : ∀ (y v : Fin r → ℂ), (∀ b : Fin X.p0, hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) →
      hermC τ.1 X.Gm (X.ppos x τ v) y = 0 := by
    intro y v hy
    unfold ppos
    rw [hC_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hC_smul_left, hsymm, hy a, map_zero, mul_zero]
  have h1 : hermC τ.1 X.Gm (X.ppos x τ u) (w - X.ppos x τ w) = 0 :=
    hspan (w - X.ppos x τ w) u (ppos_orth X x τ hA w)
  have h2 : hermC τ.1 X.Gm (u - X.ppos x τ u) (X.ppos x τ w) = 0 :=
    hspan (u - X.ppos x τ u) w (ppos_orth X x τ hA u) |> fun h => by rw [hsymm, h, map_zero]
  have e1 : hermC τ.1 X.Gm (X.ppos x τ u) w =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : w = X.ppos x τ w + (w - X.ppos x τ w) := by abel
    conv_lhs => rw [this]
    rw [hC_add_right, h1, add_zero]
  have e2 : hermC τ.1 X.Gm u (X.ppos x τ w) =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : u = X.ppos x τ u + (u - X.ppos x τ u) := by abel
    conv_lhs => rw [this]
    rw [hC_add_left, h2, add_zero]
  rw [e1, e2]
end ReciprocityTheory.ChartRestriction.G.FD.Data
