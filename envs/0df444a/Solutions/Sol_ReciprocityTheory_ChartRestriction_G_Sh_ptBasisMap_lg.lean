-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptBasisMap_lg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:28.536796+00:00
-- url     : https://prove2.me/submissions/cfced2a0-5d5a-4d16-87bd-13827cff3221

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptOn_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptOn_lg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSumL_lg


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
theorem _root_.solution (G : LogFGL v d) {γ : Fin d → Fin d → PowerSeries C}
    (hγ : ∀ a, IsCurve v (γ a)) (b : Fin d) :
    subst (ptBasisMap G γ) (G.lg b) =
      ∑ a, PowerSeries.subst (X a : MvPowerSeries (Fin d) C) (G.lgCurve (γ a) b) := by
  have hc : ∀ x ∈ List.ofFn (fun a => ptOn a (γ a)), ∀ c, constantCoeff (x c) = 0 := by
    intro x hx c
    obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
    exact (ptOn_good a (hγ a) c).1
  rw [ptBasisMap, ptSumL_lg G _ hc b, List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_congr rfl fun a _ => ptOn_lg G a (hγ a) b
end ReciprocityTheory.ChartRestriction.G.Sh
