-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.conj_bGram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:56.815213+00:00
-- url     : https://prove2.me/submissions/93231d93-6410-44a9-b896-60f8faa02370

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_secFun_conjPt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_wgt_conjPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module
variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {m : ConeMetric ℂ J} {μ : Measure (J → ℂ)} (hm : IsConjInvariant m)
    (hμ : μ.map conjPt = μ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial J ℚ) (i j : Fin r) :
    starRingEnd ℂ (bGram μ (fun k => secFun (b k)) (wgt m n) i j) =
      bGram μ (fun k => secFun (b k)) (wgt m n) i j := by
  have hμ' : μ.map (conjEquiv J) = μ := hμ
  have he : ∀ x, conjEquiv J x = conjPt x := fun x => rfl
  simp only [bGram, Matrix.of_apply]
  rw [← integral_conj]
  conv_rhs => rw [← hμ']
  rw [integral_map_equiv (conjEquiv J)]
  congr 1
  funext x
  simp [he, secFun_conjPt, wgt_conjPt hm]
  try ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
