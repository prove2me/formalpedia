-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.realGram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:52:26.35481+00:00
-- url     : https://prove2.me/submissions/5b5acfd6-7156-4a23-863f-2f8693dfea2b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_LemCone
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA

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
theorem _root_.solution (m : ConeMetric ℂ J) (μ : Measure (J → ℂ)) (n : ℕ) {r : ℕ}
    (b : Fin r → MvPolynomial J ℚ) (k l : Fin r) :
    realGram (K := ℚ) (fun _ => m) (fun _ => μ) n b k l =
      (bGram μ (fun k => secFun (b k)) (wgt m n) k l).re := by
  have hsub : ∀ w₁ w₂ : NumberField.InfinitePlace ℚ, w₁ = w₂ := by
    rintro ⟨_, φ₁, rfl⟩ ⟨_, φ₂, rfl⟩
    exact Subtype.ext (by rw [RingHom.ext_rat φ₁ φ₂])
  let w₀ : NumberField.InfinitePlace ℚ := NumberField.InfinitePlace.mk (algebraMap ℚ ℂ)
  have hemb : w₀.embedding = algebraMap ℚ ℂ := RingHom.ext_rat _ _
  have hmult : (w₀.mult : ℝ) = 1 := by
    have hr : w₀.IsReal := NumberField.InfinitePlace.isReal_iff.mpr
      (NumberField.ComplexEmbedding.isReal_iff.mpr (RingHom.ext_rat _ _))
    simp [NumberField.InfinitePlace.mult, hr]
  simp only [realGram]
  rw [Fintype.sum_eq_single w₀ (fun w hw => absurd (hsub w w₀) hw), hmult, one_mul, hemb,
    ← Complex.conj_re (bGram μ (fun k => secFun (b k)) (wgt m n) k l)]
  congr 1
  simp only [bGram, Matrix.of_apply]
  rw [← integral_conj]
  congr 1
  funext z
  simp [secFun, wgt, div_eq_mul_inv]
  try ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
