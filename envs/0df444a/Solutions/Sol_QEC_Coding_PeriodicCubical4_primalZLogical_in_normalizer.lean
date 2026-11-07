-- Prove2me | solution 1 for QEC.Coding.PeriodicCubical4.primalZLogical_in_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:44:25.914205+00:00
-- url     : https://prove2.me/submissions/bd8f7a6b-e546-476a-9384-cadb2fa022cf

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Hamiltonian
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_LogicalSectors
import Theorems.Thm_QEC_Coding_PauliSymplectic_inStabilizerNormalizer_iff_commutes_generators


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.PeriodicCubical4
open scoped Classical BigOperators
open PauliSymplectic
namespace QEC.Coding.PeriodicCubical4
theorem _root_.solution {L : Nat} [NeZero L] [Fact (1 < L)]
    (z w : ZMod L) :
    InStabilizerNormalizer (toricGenerator (L := L)) (primalZLogical z w) := by
  rw [inStabilizerNormalizer_iff_commutes_generators]
  intro j
  cases j with
  | inl e =>
      rw [toricGenerator_inl]
      apply cssZCheck_commutes_cssXCheck_of_mem_dual
        (plaquetteChainComplex (L := L)).firstCoboundaryCheckCode
      · exact ((plaquetteChainComplex (L := L)).mem_firstCoboundaryCheckCode_iff _).2
          ⟨Pi.single e 1, rfl⟩
      · rw [(plaquetteChainComplex (L := L)).firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
        exact primalXYMembrane_mem_middleCycleCode z w
  | inr c =>
      rw [toricGenerator_inr]
      exact cssZCheck_commutes_cssZCheck _ _
end QEC.Coding.PeriodicCubical4
