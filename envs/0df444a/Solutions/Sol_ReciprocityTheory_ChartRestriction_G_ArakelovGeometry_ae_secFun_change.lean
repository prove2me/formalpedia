-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.ae_secFun_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:04:00.558451+00:00
-- url     : https://prove2.me/submissions/c28c2bba-ec7d-4943-87d1-26a27d6e70fd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_secFun_eq_zero_of_pts
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder
variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
theorem _root_.solution {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} {b b' : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (hb' : IsSecBasis x n b') :
    ∃ A : Matrix (Fin r) (Fin r) ℤ, ∀ k, (fun z => secFun (b' k) z) =ᵐ[μ]
      fun z => ∑ l, (A k l : ℂ) * secFun (b l) z := by
  classical
  have hpts : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := by
    rw [ae_iff]
    exact hg.vol.2.1
  have hmem : ∀ k, ∃ a : Fin r → ℤ, ∑ l, a l • aeval x (b l) = aeval x (b' k) := by
    intro k
    have hk : aeval x (b' k) ∈ sec ℤ x n := by
      rw [← hb'.2.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [← hb.2.2, Submodule.mem_span_range_iff_exists_fun] at hk
    exact hk
  choose A hA using hmem
  choose f hfh hf using hb.1
  have hcast : ∀ g : MvPolynomial (Ix κ) ℤ, aeval x (map (Int.castRingHom ℚ) g) = aeval x g := by
    intro g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  refine ⟨Matrix.of A, fun k => ?_⟩
  obtain ⟨f', hf'h, hf'⟩ := hb'.1 k
  let d : MvPolynomial (Ix κ) ℤ := f' - ∑ l, C (A k l) * f l
  have hdh : d.IsHomogeneous n := by
    rw [← mem_homogeneousSubmodule]
    refine Submodule.sub_mem _ ((mem_homogeneousSubmodule n _).2 hf'h)
      (Submodule.sum_mem _ fun l _ => (mem_homogeneousSubmodule n _).2 ((hfh l).C_mul _))
  have hd0 : aeval x d = 0 := by
    have e1 : aeval x f' = aeval x (b' k) := by rw [hf', hcast]
    have e2 : ∀ l, aeval x (f l) = aeval x (b l) := fun l => by rw [hf l, hcast]
    simp only [d, map_sub, map_sum, map_mul, aeval_C, algebraMap_int_eq, eq_intCast, map_intCast, e1, e2]
    rw [← hA k, sub_eq_zero]
    exact Finset.sum_congr rfl fun l _ => zsmul_eq_mul _ _
  filter_upwards [hpts] with z hz
  have h := secFun_eq_zero_of_pts hdh hd0 hz
  rw [secFun_map_int] at h
  simp only [d, map_sub, map_sum, map_mul, map_C, eval_sub, eval_sum, eval_mul, eval_C, eq_intCast,
    map_intCast] at h
  rw [hf', secFun_map_int]
  simp only [Matrix.of_apply, hf, secFun_map_int]
  linear_combination h
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
