-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.germComp1_germComp1_eq_substitute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:04.953799+00:00
-- url     : https://prove2.me/submissions/5318d3b6-595f-4f76-985b-c57b549f8411

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
variable {k : Type} [CommRing k] [Algebra ℚ k]
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
theorem _root_.solution {n d : ℕ} (φ ψ : Pt k 1 d) (a : Pt k n d) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (ha : ∀ i, constantCoeff (a i) = 0) : comp1 φ (comp1 ψ a) = comp1 (comp1 φ ψ) a := by
  funext i
  unfold comp1
  rw [ev_ev (![ψ] : Fin 1 → Pt k 1 d) (![a] : Fin 1 → Pt k n d) (fun j i => by fin_cases j; exact hψ i)
    (fun j i => by fin_cases j; exact ha i)]
  congr 1
  funext j
  fin_cases j
  rfl
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
