-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_SemilocalFiniteRank_proof_9f2f42e18824
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:30:41.631526+00:00
-- url     : https://prove2.me/submissions/c48dad44-739c-4757-948e-797e74d11fc0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsSemilocalFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_finrank_eq_relfinrank_of_div_a165af8765a4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_homFracDegZero_of_mem_degZeroLoc_d64725dd4b85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_algebraMap_contract_coe_ebf358cf7871
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace SemilocalFiniteRank
theorem _root_.solution (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFinite.Statement.{u}) (h3 : DegZeroLocFrac.Statement.{u}) :
    SemilocalFiniteRank.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  have inj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro a b hab
    apply Subtype.ext
    apply (contractFracMap j P').toRingHom.injective
    have := congrArg Subtype.val hab
    rwa [degZeroLoc.algebraMap_contract_coe, degZeroLoc.algebraMap_contract_coe] at this
  refine ⟨h2 F K K' j ι' P' hP' n hd' hd W hW hdW hle, ⟨fun r hr x y hxy => ?_⟩, ?_⟩
  · have hr0 : algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W)) r ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W))), inj.eq_iff]
      exact hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
  · refine finrank_eq_relfinrank_of_div (contractFracMap j P') (map_homFracDegZero_le j ι' P')
      (degZeroLoc.algebraMap_contract_coe j P' W)
      (mem_homFracDegZero_of_mem_degZeroLoc _ _) (mem_homFracDegZero_of_mem_degZeroLoc _ _) ?_ ?_
    · intro x hx
      refine h3 F K (fun k => ι' (j k)) (contractPrime j P')
        (isMultiProjPrime_contractPrime _ _ hP') {W} (Set.finite_singleton W) ?_ x hx
      intro W₁ hW₁
      rw [Set.mem_singleton_iff.mp hW₁]
      exact hW
    · exact h3 F K' ι' P' hP' (fibrePrimes j P' W) hfin (fun W' hW' => hW'.1)
end SemilocalFiniteRank
end GroundTheory.Heights₂.Heights.FieldNumbers
