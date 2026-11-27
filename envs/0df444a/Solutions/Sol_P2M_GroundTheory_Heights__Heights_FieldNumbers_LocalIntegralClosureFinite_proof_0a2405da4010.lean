-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_LocalIntegralClosureFinite_proof_0a2405da4010
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:56:05.234938+00:00
-- url     : https://prove2.me/submissions/13262f52-344f-4095-ad38-f55778d3f632

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsLocalIntegralClosureFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsNoetherIntegralClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLocFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSemilocalFiniteRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_LocalIntegralClosureChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PLocalIntegralClosureFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_degZeroLoc_map_eq_mul_inv_ec8cfa21930e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_exists_finset_integral_span_73e78e11898a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiProjPrime_contractPrime_7e3d9fd91401
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_map_homFracDegZero_le_99e71cc4273e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_homFracDegZero_of_mem_degZeroLoc_d64725dd4b85


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
namespace LocalIntegralClosureFinite
theorem _root_.solution (hN : NoetherIntegralClosureFinite.Statement.{u})
    (hF : FunctionFieldFinite.Statement.{u}) (hQ : DegZeroLocQuot.Statement.{u})
    (hD : MChartDehomog.Statement.{u}) (hFr : DegZeroLocFrac.Statement.{u}) :
    LocalIntegralClosureFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' hdim W hW hle
  have := hP'.isPrime
  have := hW.isPrime
  set P := contractPrime j P'
  set φ := contractFracMap j P'
  set A' := (degZeroLoc P {W}).map φ
  set L := homFracDegZero P'
  choose u hu using hW.relevant
  obtain ⟨hRA, hloc⟩ := degZeroLoc_map_eq_mul_inv hQ hD P W hle u hu φ
  set S := Set.range fun v => φ (chartMap P u (X v))
  have hAL : ∀ a ∈ A', a ∈ L := by
    rintro _ ⟨a, ha, rfl⟩
    exact map_homFracDegZero_le j ι' P' ⟨a, mem_homFracDegZero_of_mem_degZeroLoc P {W} a ha, rfl⟩
  have hEL : IntermediateField.adjoin F S ≤ L :=
    IntermediateField.adjoin_le_iff.mpr fun _ hx => hAL _ (hRA (Algebra.subset_adjoin hx))
  have hAE : ∀ a ∈ A', a ∈ IntermediateField.adjoin F S := fun a ha => by
    obtain ⟨r, hr, d, hd, -, -, rfl⟩ := hloc a ha
    exact mul_mem (IntermediateField.algebra_adjoin_le_adjoin F S hr)
      (inv_mem (IntermediateField.algebra_adjoin_le_adjoin F S hd))
  have hκE : (homFracDegZero P).map φ ≤ IntermediateField.adjoin F S := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, w, hw, -, rfl⟩ := hFr F K (fun k => ι' (j k)) P
      (isMultiProjPrime_contractPrime j ι' hP') {W} (Set.finite_singleton W)
      (fun W' h => by rw [Set.mem_singleton_iff.mp h]; exact hW) z hz
    rw [map_div₀]
    exact div_mem (hAE _ ⟨y, hy, rfl⟩) (hAE _ ⟨w, hw, rfl⟩)
  have hdeg : IntermediateField.relfinrank ((homFracDegZero P).map φ) L ≠ 0 :=
    hF F K K' j ι' P' hP' hdim
  rw [← IntermediateField.relfinrank_mul_relfinrank hκE hEL,
    IntermediateField.relfinrank_eq_finrank_of_le hEL] at hdeg
  exact exists_finset_integral_span hN (Set.finite_range _) A' L hRA hloc hEL
    (FiniteDimensional.of_finrank_pos (Nat.pos_of_ne_zero (right_ne_zero_of_mul hdeg)))
end LocalIntegralClosureFinite
end GroundTheory.Heights₂.Heights.FieldNumbers
