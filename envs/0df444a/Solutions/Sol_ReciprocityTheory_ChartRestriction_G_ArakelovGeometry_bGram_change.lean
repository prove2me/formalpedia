-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.bGram_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:29.579858+00:00
-- url     : https://prove2.me/submissions/8965056f-fc60-4a3f-b327-2d5521eec701

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt

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
theorem _root_.solution {J : Type} {μ : Measure (J → ℂ)} {r : ℕ} (s s' : Fin r → (J → ℂ) → ℂ)
    (w : (J → ℂ) → ℝ) (A : Matrix (Fin r) (Fin r) ℤ)
    (hint : ∀ i j, Integrable (fun z => starRingEnd ℂ (s i z) * s j z * (w z : ℂ)) μ)
    (hs : ∀ k, s' k =ᵐ[μ] fun z => ∑ l, (A k l : ℂ) * s l z) :
    bGram μ s' w = A.map (Int.cast : ℤ → ℂ) * bGram μ s w * (A.map (Int.cast : ℤ → ℂ)).transpose := by
  ext i j
  simp only [bGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  have hae : (fun z => starRingEnd ℂ (s' i z) * s' j z * (w z : ℂ)) =ᵐ[μ]
      fun z => ∑ k, ∑ l, ((A i k : ℂ) * (A j l : ℂ)) * (starRingEnd ℂ (s k z) * s l z * (w z : ℂ)) := by
    filter_upwards [hs i, hs j] with z hi hj
    rw [hi, hj]
    simp only [map_sum, map_mul, map_intCast, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [integral_congr_ae hae,
    integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun l _ => (hint k l).const_mul _)]
  simp_rw [integral_finset_sum _ (fun l _ => (hint _ l).const_mul _), integral_const_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
