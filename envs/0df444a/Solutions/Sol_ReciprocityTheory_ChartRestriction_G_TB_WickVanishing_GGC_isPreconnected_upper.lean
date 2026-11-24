-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC.isPreconnected_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:03.305838+00:00
-- url     : https://prove2.me/submissions/b010750a-f7bd-49ee-9068-54ace4a403fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GGConnA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_GGC_isPreconnected_det_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
open Matrix
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {r : ℕ} (p0 : ℕ)
variable {p0}
variable {p0 : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
theorem _root_.solution {ι : Type*} [Fintype ι] :
    IsPreconnected {b : ι → Matrix (Fin r) (Fin r) ℂ |
      ∀ i, (b i).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b i a c = 0} := by
  have h := isPreconnected_det_ne {x : ι → Matrix (Fin r) (Fin r) ℂ | ∀ i (a c : Fin r), c < a → x i a c = 0}
    (by
      intro a ha b hb z i k l hkl
      simp [ha i k l hkl, hb i k l hkl])
  convert h using 1
  ext b
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨fun i => (h i).2, fun i => (h i).1⟩, fun h i => ⟨h.2 i, h.1 i⟩⟩
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.GGC
