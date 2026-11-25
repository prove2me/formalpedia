-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.posDef_bGram_secFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:32:20.83181+00:00
-- url     : https://prove2.me/submissions/9b20d8ea-2d42-4b13-8984-31d8d109c765

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_integrable_secFun
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_eq_zero_of_ae_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_secFun_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_isDegZero_normSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_continuousOn_normSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_nonempty_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_linIndep_rat_of_isSecBasis
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_coeff_eq_zero_of_vanish
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_bGram_isHermitian
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_dot_bGram
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_integrable_normSq_mul


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
    (hg : IsGood D x m μ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b) :
    (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef := by
  have hint := integrable_secFun hg hb
  have hρ00 : m.ρ 0 = 0 := by
    have h := m.smul 0 0
    rwa [zero_smul, norm_zero, zero_mul] at h
  have hρ0 : ∀ z, 0 ≤ m.ρ z := fun z => by
    by_cases hz : z = 0
    · rw [hz, hρ00]
    · exact (m.pos z hz).le
  have hwnn : ∀ z, 0 ≤ wgt m n z := fun z => inv_nonneg.2 (pow_nonneg (hρ0 z) _)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (bGram_isHermitian _ _ _) fun c hc => ?_
  rw [dot_bGram _ _ _ hint c, Complex.zero_lt_real]
  have hgnn : ∀ z, 0 ≤ ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z :=
    fun z => mul_nonneg (sq_nonneg _) (hwnn z)
  have hgint : Integrable (fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z) μ :=
    integrable_normSq_mul μ _ _ hint c
  by_contra hle
  push_neg at hle
  have h0 : ∫ z, ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z ∂μ = 0 :=
    le_antisymm hle (integral_nonneg hgnn)
  have hae := (integral_eq_zero_iff_of_nonneg hgnn hgint).1 h0
  have hvan : ∀ z₀ ∈ pts (coordIdeal ℤ x), ∑ i, c i * secFun (b i) z₀ = 0 := by
    intro z₀ hz₀
    have hg0 := eq_zero_of_ae_zero hg (continuousOn_normSq hg.semipos.1 b c) (isDegZero_normSq hb.1 c)
      hgnn hae hz₀
    have hw : 0 < wgt m n z₀ := inv_pos.2 (pow_pos (m.pos z₀ hz₀.1) _)
    have h1 := (mul_eq_zero.1 hg0).resolve_right hw.ne'
    simpa using h1
  apply hc
  apply coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb)
  intro z hz
  by_cases hz0 : z = 0
  · obtain ⟨z₀, hz₀⟩ := nonempty_pts hg
    have h2 := sum_secFun_smul hb.1 c 0 z₀
    rw [zero_smul, hvan z₀ hz₀, mul_zero] at h2
    rw [hz0]
    exact h2
  · exact hvan z ⟨hz0, hz⟩
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
