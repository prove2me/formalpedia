-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_secFun_eq__d81f0b965cfc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:04:54.855096+00:00
-- url     : https://prove2.me/submissions/c1cbe0d1-d782-445c-a158-87cf17f298d2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_CSandwichStE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_aeval_map_intQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_secFun_map_intQ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_coordIdeal_of_isHomogeneous


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder Matrix
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) (g : MvPolynomial (Ix κ) ℤ) (hg : g.IsHomogeneous n) (c : Fin r → ℤ)
    (hc : ∑ j, (c j : Ω) * aeval x (b j) = aeval x g) :
    ∀ z ∈ pts (coordIdeal ℤ x),
      ∑ j, (c j : ℂ) * secFun (b j) z = eval z (map (Int.castRingHom ℂ) g) := by
  choose f hf hbf using hb.1
  intro z hz
  set h : MvPolynomial (Ix κ) ℤ := ∑ j, c j • f j - g with hh_def
  have hh : h.IsHomogeneous n := by
    have := Submodule.sub_mem _ (Submodule.sum_mem (homogeneousSubmodule (Ix κ) ℤ n) (t := Finset.univ)
      fun j _ => Submodule.smul_mem _ (c j) ((mem_homogeneousSubmodule _ _).mpr (hf j)))
      ((mem_homogeneousSubmodule _ _).mpr hg)
    exact (mem_homogeneousSubmodule _ _).mp this
  have hx : aeval x h = 0 := by
    rw [hh_def, map_sub, map_sum, ← hc, sub_eq_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, zsmul_eq_mul, hbf j, aeval_map_intQ]
  have h0 := hz.2 h (mem_coordIdeal_of_isHomogeneous (o := ℤ) (x := x) hh hx)
  rw [hh_def, map_sub, map_sum, map_sub, map_sum, sub_eq_zero] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, map_zsmul, zsmul_eq_mul, hbf j, secFun_map_intQ]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
