-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.secFun_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:51.91069+00:00
-- url     : https://prove2.me/submissions/0a76dfcc-a00c-4bca-8e03-46ea57944fb6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eval_smul_of_homog

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
theorem _root_.solution {b : MvPolynomial J ℚ} {n : ℕ}
    (hb : ∃ f : MvPolynomial J ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : J → ℂ) : secFun b (c • z) = c ^ n * secFun b z := by
  obtain ⟨f, hf, rfl⟩ := hb
  have hmap : map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℂ) f := by
    rw [map_map]
    congr 1 <;> exact RingHom.ext_int _ _
  simp only [secFun, hmap]
  exact eval_smul_of_homog (hf.map _) c z
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
