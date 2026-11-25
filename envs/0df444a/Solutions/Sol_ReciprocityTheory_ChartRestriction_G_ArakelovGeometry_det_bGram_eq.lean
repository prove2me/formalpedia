-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.det_bGram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:21.319217+00:00
-- url     : https://prove2.me/submissions/29915bda-e5a5-4827-89d2-29b263636d6e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_integrable_secFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_posDef_bGram_secFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_bGram_change
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_ae_secFun_change

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
    (bGram μ (fun k => secFun (b' k)) (wgt m n)).det =
      (bGram μ (fun k => secFun (b k)) (wgt m n)).det := by
  obtain ⟨A, hA⟩ := ae_secFun_change hg hb hb'
  obtain ⟨B, hB⟩ := ae_secFun_change hg hb' hb
  have h1 := bGram_change _ _ (wgt m n) A (integrable_secFun hg hb) hA
  have h2 := bGram_change _ _ (wgt m n) B (integrable_secFun hg hb') hB
  have hG0 : (bGram μ (fun k => secFun (b k)) (wgt m n)).det ≠ 0 :=
    (posDef_bGram_secFun hg hb).det_pos.ne'
  have hcast : ∀ M : Matrix (Fin r) (Fin r) ℤ, (M.map (Int.cast : ℤ → ℂ)).det = ((M.det : ℤ) : ℂ) :=
    fun M => (RingHom.map_det (Int.castRingHom ℂ) M).symm
  have e1 : (bGram μ (fun k => secFun (b' k)) (wgt m n)).det =
      ((A.det : ℤ) : ℂ) ^ 2 * (bGram μ (fun k => secFun (b k)) (wgt m n)).det := by
    rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hcast]
    ring
  have e2 : (bGram μ (fun k => secFun (b k)) (wgt m n)).det =
      ((B.det : ℤ) : ℂ) ^ 2 * (bGram μ (fun k => secFun (b' k)) (wgt m n)).det := by
    rw [h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hcast]
    ring
  have key : ((A.det : ℤ) : ℂ) ^ 2 * ((B.det : ℤ) : ℂ) ^ 2 = 1 := by
    have h := e2
    rw [e1] at h
    have h3 : (((B.det : ℤ) : ℂ) ^ 2 * ((A.det : ℤ) : ℂ) ^ 2 - 1) *
        (bGram μ (fun k => secFun (b k)) (wgt m n)).det = 0 := by
      linear_combination (-1 : ℂ) * h
    have h4 := (mul_eq_zero.1 h3).resolve_right hG0
    linear_combination h4
  have keyZ : A.det ^ 2 * B.det ^ 2 = 1 := by exact_mod_cast key
  have hA2 : A.det ^ 2 = 1 := Int.eq_one_of_mul_eq_one_right (sq_nonneg _) keyZ
  have hA2' : ((A.det : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast hA2
  rw [e1, hA2', one_mul]
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
