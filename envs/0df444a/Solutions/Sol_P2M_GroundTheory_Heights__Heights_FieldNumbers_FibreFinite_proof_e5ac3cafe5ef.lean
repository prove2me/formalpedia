-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_FibreFinite_proof_e5ac3cafe5ef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:21:30.846668+00:00
-- url     : https://prove2.me/submissions/b92d4c4c-c429-49b9-9b7a-9ae7a383cb22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFibreFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PContractRelDimLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFibreFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelDimLe_proof_46b509c2b5c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_exists_ringKrullDim_eq_65838c645fa5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_killBlocks_mem_of_isMultiHomogIdeal_8504d8e804fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_natCast_withBot_withTop_eb5b1b957aeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_proof_c7e248874611
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_relDim_eq_int_8d437d865d06
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_ringKrullDim_add_one_le_36765965af2f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659


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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace FibreFinite
theorem _root_.solution : FibreFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _
  have := hP'.isPrime
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
    (P' ⊔ W.map (rename (blockIncl j ι')))).subset ?_
  rintro W' ⟨hW', hPW', hc⟩
  have := hW'.isPrime
  obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW' (Ideal.map_le_iff_le_comap.mpr hc.ge))
  have := hQ.1.1
  have hP'Q : P' ≤ Q := le_sup_left.trans hQ.1.2
  suffices Q = W' by rwa [← this]
  by_contra hne
  have hQc : contractPrime j Q = W := le_antisymm (hc ▸ Ideal.comap_mono hQW')
    (Ideal.le_comap_map.trans (Ideal.comap_mono (le_sup_right.trans hQ.1.2)))
  have hne' : P' ≠ Q := by
    rintro rfl
    rw [hQc, hWn] at hPn
    simp only [natCast_withBot_withTop] at hPn
    have := WithTop.coe_inj.mp (WithBot.coe_inj.mp hPn)
    omega
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hP'Q hne')
  obtain ⟨g, hgW, hgQ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQW' hne)
  have h1 := ringKrullDim_add_one_le hP'Q hfP hfQ
  have h2 := ringKrullDim_add_one_le hQW' hgQ hgW
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant
  obtain ⟨E, -, hE⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hW'.multiHomog T hq) hW'.relevant
  have h3 := ContractRelDimLe.proof F K K' j ι' W' hW'
  rw [hc, hWn, relDim_eq_int hE, natCast_withBot_withTop] at h3
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hP'n
  have h4 : ((E + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ D := by
    rw [← hD]
    rw [hE] at h2
    push_cast
    exact le_trans (by gcongr) h1
  have h3' : (n : ℤ) ≤ E - Fintype.card K' := by exact_mod_cast h3
  have hP'n' : (D : ℤ) - Fintype.card K' = (n + 1 : ℕ) := by exact_mod_cast hP'n
  have h4' : E + 1 + 1 ≤ D := by exact_mod_cast h4
  omega
end FibreFinite
end GroundTheory.Heights₂.Heights.FieldNumbers
