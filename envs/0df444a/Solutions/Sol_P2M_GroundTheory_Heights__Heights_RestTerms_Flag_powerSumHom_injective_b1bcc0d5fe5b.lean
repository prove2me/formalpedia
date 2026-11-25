-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:07:27.474031+00:00
-- url     : https://prove2.me/submissions/d4a18d0f-cfbc-416d-b959-705437ff8fe5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_injective_of_surjective_endo_1043597ed6bc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_exists_powerSumHom_eq_7cf93073418c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_isSymmetric_d4be3b011480

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section
namespace GroundTheory.Heights₂.Heights.RestTerms.Flag
theorem _root_.solution (N : ℕ) : Function.Injective (powerSumHom N) := by

  let e := esymmAlgEquiv (Fin N) ℚ (n := N) (by simp)
  let π : MvPolynomial (Fin N) ℚ →ₐ[ℚ] symmetricSubalgebra (Fin N) ℚ :=
    (powerSumHom N).codRestrict _ (fun S => powerSumHom_isSymmetric N S)
  let φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ := e.symm.toAlgHom.comp π
  have hsurj : Function.Surjective φ := by
    intro T
    obtain ⟨S, hS⟩ := exists_powerSumHom_eq (e T).2
    refine ⟨S, ?_⟩
    apply e.injective
    simp only [φ, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact Subtype.ext hS
  have hinj : Function.Injective φ := injective_of_surjective_endo φ.toRingHom hsurj
  intro S T hST
  apply hinj
  simp only [φ, AlgHom.comp_apply]
  congr 1
  exact Subtype.ext hST
end GroundTheory.Heights₂.Heights.RestTerms.Flag
