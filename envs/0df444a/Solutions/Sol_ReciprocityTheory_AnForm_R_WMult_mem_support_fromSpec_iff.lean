-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.WMult.mem_support_fromSpec_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:25.448863+00:00
-- url     : https://prove2.me/submissions/0f752367-307e-42ad-99a5-358490a15a0c

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.WMult
theorem _root_.solution (I : W.IdealSheafData) (U : W.affineOpens) (hU : IsAffineOpen U.1)
    (P : PrimeSpectrum Γ(W, U.1)) :
    hU.fromSpec P ∈ (I.support : Set W) ↔ I.ideal U ≤ P.asIdeal := by
  have hmem : hU.fromSpec P ∈ U.1 := by
    have hr : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
    rw [hU.range_fromSpec] at hr
    exact hr
  show hU.fromSpec P ∈ I.support ↔ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hmem]
  exact (Set.ext_iff.1 (hU.fromSpec_preimage_zeroLocus (I.ideal U : Set Γ(W, U.1))) P).trans
    ((PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe)
end ReciprocityTheory.AnForm.R.WMult
