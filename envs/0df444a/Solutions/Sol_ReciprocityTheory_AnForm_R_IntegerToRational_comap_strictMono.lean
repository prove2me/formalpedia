-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:20:09.204257+00:00
-- url     : https://prove2.me/submissions/21c0460b-8683-4397-a314-30d37a7d3611

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_HeightAddRingKrullDimQuotientMvPolynomialField
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IntegerToRational
open MvPolynomial
variable {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.algebraMvPolynomial
namespace ReciprocityTheory.AnForm.R.IntegerToRational
theorem _root_.solution :
    StrictMono (fun Q : Ideal (MvPolynomial σ ℚ) => Q.comap (MvPolynomial.map (Int.castRingHom ℚ))) := by
  have hA : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  rw [← hA]
  exact (IsLocalization.orderEmbedding (intS σ) (MvPolynomial σ ℚ)).strictMono
end ReciprocityTheory.AnForm.R.IntegerToRational
