-- Prove2me | solution 1 for SumProduct.zInfty_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:37:40.798809+00:00
-- url     : https://prove2.me/submissions/0b4e93be-fc5c-4f2b-a083-ef6b7a0a1d2b

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin

set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
namespace SumProduct
theorem _root_.solution (s : ℝ) :
    DedekindZeta.ZInfty K (s : ℂ)
      = ((|(NumberField.discr K : ℝ)| ^ (s / 2)
          * (Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2)) ^ NumberField.InfinitePlace.nrRealPlaces K
          * (2 * (2 * Real.pi) ^ (-s) * Real.Gamma s)
              ^ NumberField.InfinitePlace.nrComplexPlaces K : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hdisc : (0 : ℝ) ≤ |(NumberField.discr K : ℝ)| := abs_nonneg _
  -- LReal
  have hLReal : DedekindZeta.LReal (s : ℂ)
      = ((Real.pi ^ (-(s / 2)) * Real.Gamma (s / 2) : ℝ) : ℂ) := by
    rw [DedekindZeta.LReal]
    rw [show (-(s : ℂ) / 2) = ((-(s / 2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpi]
    rw [show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  -- LComplex
  have hLComplex : DedekindZeta.LComplex (s : ℂ)
      = ((2 * (2 * Real.pi) ^ (-s) * Real.Gamma s : ℝ) : ℂ) := by
    rw [DedekindZeta.LComplex]
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring]
    rw [show (-(s : ℂ)) = ((-s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow h2pi, Complex.Gamma_ofReal]
    push_cast; ring
  -- discriminant factor
  have hDR : ((|NumberField.discr K| : ℤ) : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [Int.cast_abs]
  have hDisc : (((|NumberField.discr K| : ℤ) : ℂ)) ^ ((s : ℂ) / 2)
      = ((|(NumberField.discr K : ℝ)| ^ (s / 2) : ℝ) : ℂ) := by
    rw [show (((|NumberField.discr K| : ℤ) : ℂ)) = ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) by
        rw [← hDR]; norm_cast,
      show (s : ℂ) / 2 = ((s / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hdisc]
  rw [DedekindZeta.ZInfty, hLReal, hLComplex, hDisc]
  push_cast
  ring
end SumProduct
