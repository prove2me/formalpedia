-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocLocalize_proof_06a2ff5a902a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:00.698137+00:00
-- url     : https://prove2.me/submissions/feae4a24-a3d2-4dc4-856a-72d873a63285

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocLocalize
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_RelevantMinimalOfDivCycleNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PDegZeroLocLocalize
import Theorems.Thm_GroundTheory_Arith_Toric_LowerBound_mul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_CutRational_proof_c27e72dcc134
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_DegZeroLocQuot_proof_f2e3f8a36e28
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ExistsForm_proof_d5dace6f400d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ProjectionFormulaDegree_proof_0aacacc92e0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_RelevantPrimeDimGe_proof_f3a1f51a2659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_div_mem_degZeroLoc_250927a4bb6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_AvoidingFormExists_proof_39d2ee9f3bcd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_DivCycleMul_proof_5282581d8898
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MinimalPrimeMultiHomog_proof_00f169244e2b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultAtPrimeAtMinimal_proof_af70a5a37a53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Representative_proof_61b56da860aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SupSpanMultiHomog_proof_861d53cbe2c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_avoid_primes_f8b11e5baf19
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_not_mem_of_isRelevant_8f453759efa5


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
namespace DegZeroLocLocalize
theorem _root_.solution : DegZeroLocLocalize.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro W hW y hy
  have hWp := h𝒲P W hW
  have : W.IsPrime := hWp.1.isPrime
  obtain ⟨c, f, g, hf, hg, hgP, hgW, rfl⟩ :=
    DegZeroLocQuot.proof F K ι P {W} (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact this)
      y hy
  have hgW' : g ∉ W := hgW W rfl
  obtain ⟨e, h, hh, hce, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W' hW' => by
      rcases Finset.mem_insert.mp hW' with rfl | hW'
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have h' := (h𝒲P W' (h𝒲.mem_toFinset.mp hW')).1
        exact ⟨h'.isPrime, h'.multiHomog, h'.relevant⟩) c
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W' ∈ 𝒲, h ∉ W' := fun W' hW' =>
    hhS W' (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW'))
  obtain ⟨m, hm, hmW⟩ := exists_form_not_mem_of_isRelevant (H := W) hWp.1.relevant (e - c)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hce] at this
  have hgmW : g * m ∉ W := fun h' => (this.mem_or_mem h').elim hgW' hmW
  have hgmP : g * m ∉ P := fun h' => hgmW (hWp.2 h')
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    ⟨_, div_mem_degZeroLoc P {W} hh hgm hgmP (fun W' hW' => by rw [Set.mem_singleton_iff.mp hW']; exact hgmW),
      ?_⟩, ?_⟩
  · rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hq0 _ hhP) (hq0 _ hgmP))]
  · have h1 := hq0 _ hgP
    have h2 := hq0 _ hhP
    simp only [map_mul]
    field_simp
end DegZeroLocLocalize
end GroundTheory.Heights₂.Heights.FieldNumbers
