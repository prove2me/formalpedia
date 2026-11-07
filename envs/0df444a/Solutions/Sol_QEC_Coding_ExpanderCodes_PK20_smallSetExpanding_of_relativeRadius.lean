-- Prove2me | solution 1 for QEC.Coding.ExpanderCodes.PK20.smallSetExpanding_of_relativeRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:20:58.694396+00:00
-- url     : https://prove2.me/submissions/e003dda4-602b-45cb-868b-39efea0a6f42

import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicLocality
import Definitions.Def_QEC_Coding_BalancedProduct_CyclicDimension
import Definitions.Def_QEC_Coding_ExpanderCodes_AlmostLinear

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ExpanderCodes QEC.Coding.ExpanderCodes.PK20
open QEC.Coding
open QEC.Coding.BalancedProduct
namespace QEC.Coding.ExpanderCodes.PK20
theorem _root_.solution
    {F ι κ : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Fintype κ]
    (f : Word F ι →ₗ[F] Word F κ)
    {radius radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : Nat}
    (hExpansion : f.SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator)
    (hRadius : radiusDenominator * radius ≤
      radiusNumerator * Fintype.card ι) :
    f.SmallSetExpanding radius expansionNumerator expansionDenominator := by
  refine ⟨hExpansion.2.1, ?_⟩
  intro x hx
  exact hExpansion.2.2 x <|
    (Nat.mul_le_mul_left radiusDenominator hx).trans hRadius
end QEC.Coding.ExpanderCodes.PK20
