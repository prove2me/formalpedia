-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiCubeProduct.hasSum_signedEuler_jtpPairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:52:37.983279+00:00
-- url     : https://prove2.me/submissions/07dc1698-c790-406e-b4dd-ded5b50b03b9

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_FPSAlgebra
import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_summable_signedTriangularTerm_nonnegative
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_hasSum_signedEuler_jtpIntegerTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_signedEuler_jtpPair
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiCubeProduct_summable_signedEuler_jtpPositiveShift

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
open JacobiGeneralCore.FormalPowerSeries
set_option linter.style.haveILetI false
namespace QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
theorem _root_.solution :
    letI : TopologicalSpace LaurentQ := ⊥
    HasSum (fun t : ℕ =>
        signedEuler (jtpIntegerTerm ((t : ℤ) + 1)) +
          signedEuler (jtpIntegerTerm (-(t : ℤ))))
      (signedEuler jacobiBilateral) := by
  letI : TopologicalSpace LaurentQ := ⊥
  letI : DiscreteTopology LaurentQ := ⟨rfl⟩
  let f := fun z : ℤ => signedEuler (jtpIntegerTerm z)
  have hall : HasSum f (signedEuler jacobiBilateral) :=
    hasSum_signedEuler_jtpIntegerTerm
  have hpos : Summable (fun t : ℕ => f ((t : ℤ) + 1)) := by
    apply summable_signedEuler_jtpPositiveShift.congr
    intro t
    change signedEuler (jtpPositiveTerm (t + 1)) =
      signedEuler (jtpIntegerTerm ((t : ℤ) + 1))
    rw [jtpIntegerTerm, if_pos (by omega)]
    congr 2
  have hpairs : Summable (fun t : ℕ =>
      f ((t : ℤ) + 1) + f (-(t : ℤ))) := by
    apply summable_signedTriangularTerm_nonnegative.neg.congr
    intro t
    exact (signedEuler_jtpPair t).symm
  have hnonpos : Summable (fun t : ℕ => f (-(t : ℤ))) := by
    apply (hpairs.sub hpos).congr
    intro t
    ring
  have hsplit : HasSum
      (fun s : ℕ ⊕ ℕ => f (cubePairEquiv s))
      ((∑' t : ℕ, f ((t : ℤ) + 1)) +
        ∑' t : ℕ, f (-(t : ℤ))) := by
    apply HasSum.sum
    · exact hpos.hasSum
    · exact hnonpos.hasSum
  have hreindexed : HasSum
      (fun s : ℕ ⊕ ℕ => f (cubePairEquiv s))
      (signedEuler jacobiBilateral) := by
    change HasSum (f ∘ cubePairEquiv) (signedEuler jacobiBilateral)
    exact (Equiv.hasSum_iff cubePairEquiv).2 hall
  rw [← hsplit.unique hreindexed]
  exact hpos.hasSum.add hnonpos.hasSum
end QEC.Coding.TannerLiftedProduct.JacobiCubeProduct
