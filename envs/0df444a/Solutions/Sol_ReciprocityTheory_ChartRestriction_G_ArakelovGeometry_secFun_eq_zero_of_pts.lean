-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.secFun_eq_zero_of_pts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:16.966928+00:00
-- url     : https://prove2.me/submissions/efa12089-26d1-40a1-a04c-756450f1a497

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eval_smul_of_homog
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_secFun_map_int

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
theorem _root_.solution {x : J → Ω} {n : ℕ} {d : MvPolynomial J ℤ} (hd : d.IsHomogeneous n)
    (h0 : aeval x d = 0) {z : J → ℂ} (hz : z ∈ pts (coordIdeal ℤ x)) :
    secFun (map (Int.castRingHom ℚ) d) z = 0 := by
  have hmem : d ∈ coordIdeal ℤ x := by
    unfold coordIdeal coneMap
    rw [RingHom.mem_ker, aeval_def, ← eval_map]
    have hpt : (fun i => Polynomial.C (x i) * Polynomial.X) =
        (Polynomial.X : Polynomial Ω) • fun i => Polynomial.C (x i) := by
      funext i
      exact mul_comm _ _
    have hC : eval (fun i => Polynomial.C (x i)) (map (algebraMap ℤ (Polynomial Ω)) d) =
        Polynomial.C (aeval x d) := by
      rw [eval_map, aeval_def, hom_eval₂]
      congr 1 <;> exact RingHom.ext_int _ _
    rw [hpt, eval_smul_of_homog (hd.map _), hC, h0, map_zero, mul_zero]
  rw [secFun_map_int]
  exact hz.2 d hmem
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
