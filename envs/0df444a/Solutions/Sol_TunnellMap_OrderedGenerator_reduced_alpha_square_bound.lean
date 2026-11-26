-- Prove2me | solution 1 for TunnellMap.OrderedGenerator.reduced_alpha_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:50.304845+00:00
-- url     : https://prove2.me/submissions/a1d67936-8443-4b01-8987-e02f4700fa3b

import Definitions.Def_TunnellMap_OrderedGenerator
import Definitions.Def_TunnellMap_ReducedBasisBound
import Theorems.Thm_TunnellMap_OrderedGenerator_alpha_pos
import Theorems.Thm_TunnellMap_OrthogonalFrame_gram_det


set_option autoImplicit true
open TunnellMap
open TunnellMap.OrderedGenerator
variable {p : Triple}
namespace TunnellMap.OrderedGenerator
theorem _root_.solution (F : OrthogonalFrame p)
    (hred : IsLagrangeGaussReduced F) :
    3 * alpha F ^ 2 ≤ 4 * dot p p := by
  rcases hred with ⟨hbetaAbs, hAlphaGamma⟩
  have hAlpha : 0 < alpha F := alpha_pos F
  have hbetaBounds : -alpha F ≤ 2 * beta F ∧ 2 * beta F ≤ alpha F :=
    (abs_le.mp hbetaAbs)
  have hbetaSq : 4 * beta F ^ 2 ≤ alpha F ^ 2 := by
    have hleft : 0 ≤ alpha F - 2 * beta F := sub_nonneg.mpr hbetaBounds.2
    have hright : 0 ≤ alpha F + 2 * beta F := by omega
    nlinarith [mul_nonneg hleft hright]
  have hAlphaSq : alpha F ^ 2 ≤ alpha F * gamma F := by
    have hnonneg : 0 ≤ alpha F * (gamma F - alpha F) :=
      mul_nonneg hAlpha.le (sub_nonneg.mpr hAlphaGamma)
    nlinarith
  have hGram := F.gram_det
  change alpha F * gamma F - beta F ^ 2 = dot p p at hGram
  nlinarith
end TunnellMap.OrderedGenerator
