-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCosetCuspResidueData_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:44:41.084864+00:00
-- url     : https://prove2.me/submissions/bbf50a82-8e93-4719-9f6b-d4ac2e18d28f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModularEquation
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.KummerExtension
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspPhaseResidue
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetCuspData_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhaseResidue_charP
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalLevelPhaseMap_injectiveOnRoots
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalCosetPhaseElement_pow

set_option autoImplicit false
open Complex Filter Topology
open scoped UpperHalfPlane MatrixGroups
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhasePrime_isMaximal
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalLevelPhaseResidue_field
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) (p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N) :
    Function.Injective (lpsOriginalCosetCuspResidueData N hN p hp) := by
  let K := LPSOriginalLevelPhaseResidue N hN p hp
  let : CharP K p := lpsOriginalLevelPhaseResidue_charP N hN p hp
  let φ := Ideal.Quotient.mk (lpsOriginalLevelPhasePrime N hN p hp)
  have hNK : (N : K) ≠ 0 := (CharP.cast_eq_zero_iff K p N).not.mpr hpN
  intro x y hxy
  apply lpsOriginalCosetCuspData_injective N hN
  apply Prod.ext
  · exact congrArg (fun z : ℕ × K => z.1) hxy
  · have hφ : φ (lpsOriginalCosetPhaseElement N hN x) =
        φ (lpsOriginalCosetPhaseElement N hN y) :=
      congrArg (fun z : ℕ × K => z.2) hxy
    have he : lpsOriginalCosetPhaseElement N hN x =
        lpsOriginalCosetPhaseElement N hN y :=
      lpsOriginalLevelPhaseMap_injectiveOnRoots N hN K φ hNK
        (lpsOriginalCosetPhaseElement_pow N hN x)
        (lpsOriginalCosetPhaseElement_pow N hN y) hφ
    exact congrArg Subtype.val he
end QEC.Coding.TannerLiftedProduct
