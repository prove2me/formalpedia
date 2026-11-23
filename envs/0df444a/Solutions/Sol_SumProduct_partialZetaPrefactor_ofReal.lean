-- Prove2me | solution 1 for SumProduct.partialZetaPrefactor_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:03:34.801896+00:00
-- url     : https://prove2.me/submissions/5c376f6b-91cb-41d9-a312-55da4a9d33a4

import Definitions.Def_DedekindZeta_PerClass
import Definitions.Def_DedekindZeta_ConeMellinBridge
import Definitions.Def_SumProduct_PartialZetaMellin

set_option autoImplicit true
open scoped NumberField nonZeroDivisors
open MeasureTheory NumberField NumberField.InfinitePlace NumberField.Units
open SumProduct
variable (K : Type*) [Field K] [NumberField K]
open DedekindZeta DedekindZeta.ConeRadialReduction DedekindZeta.ConeMellinBridge
  DedekindZeta.MellinPrinciple
open scoped nonZeroDivisors
variable {K}
namespace SumProduct
theorem _root_.solution (𝔞 : Ideal (𝓞 K)) (s : ℝ) :
    (1 / (Units.torsionOrder K : ℂ)) * (Ideal.absNorm 𝔞 : ℂ) ^ (s : ℂ)
        * (((|NumberField.discr K| : ℤ) : ℂ) ^ ((s : ℂ) / 2))
      = (((1 / (Units.torsionOrder K : ℝ)) * (Ideal.absNorm 𝔞 : ℝ) ^ s
          * (|(NumberField.discr K : ℝ)|) ^ (s / 2) : ℝ) : ℂ) := by
  have hN : (Ideal.absNorm 𝔞 : ℂ) = (((Ideal.absNorm 𝔞 : ℝ)) : ℂ) := by push_cast; ring
  have hDR : ((|NumberField.discr K| : ℤ) : ℝ) = |(NumberField.discr K : ℝ)| := by
    rw [Int.cast_abs]
  have hD : (((|NumberField.discr K| : ℤ) : ℂ)) = ((|(NumberField.discr K : ℝ)| : ℝ) : ℂ) := by
    rw [← hDR]; norm_cast
  rw [hN, hD, show ((s : ℂ) / 2) = (((s/2 : ℝ)) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_cpow (by positivity)]
  push_cast
  ring
end SumProduct
