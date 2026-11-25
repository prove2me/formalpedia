-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isDegZero_normSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:02:32.199108+00:00
-- url     : https://prove2.me/submissions/b5cd2242-dd99-478b-bd87-019eddb8bd7b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsBergDensity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_SectionModuleEqSpanPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_AParamSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeStB
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_PluriharmonicAnalysis_BergmanDerivSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ABridgeSt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_ArakelovGeometry_sum_secFun_smul

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
theorem _root_.solution {m : ConeMetric ℂ (Ix κ)} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → ℂ) : IsDegZero fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z := by
  intro a z ha
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hpow : ‖a‖ ^ (2 * n) ≠ 0 := pow_ne_zero _ hn
  simp only [wgt]
  rw [sum_secFun_smul hb, m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖a‖), mul_inv, ← pow_mul]
  field_simp
  ring
end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
