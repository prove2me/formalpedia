-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Sh.ptBasisMap_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:04:14.198331+00:00
-- url     : https://prove2.me/submissions/89d8a061-9d23-41dd-bc96-9d8ffca79eae

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtRescaleGood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PtBasisMapGood
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptOn_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptOn_lin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Sh_ptSumL_lin


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
    (hγ : ∀ a, IsCurve v (γ a)) (b s : Fin d) :
    coeff (Finsupp.single s 1) (ptBasisMap G γ b) = tangent (γ s) b := by
  have hc : ∀ x ∈ List.ofFn (fun a => ptOn a (γ a)), ∀ c, constantCoeff (x c) = 0 := by
    intro x hx c
    obtain ⟨a, rfl⟩ : ∃ a, ptOn a (γ a) = x := by simpa [List.mem_ofFn] using hx
    exact (ptOn_good a (hγ a) c).1
  rw [ptBasisMap, ptSumL_lin G _ hc b s, List.map_ofFn, List.sum_ofFn]
  simp [Function.comp_def, ptOn_lin _ (hγ _)]
end ReciprocityTheory.ChartRestriction.G.Sh
