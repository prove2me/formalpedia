-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DimStrictDrop_proof_15777780f510
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:29.449831+00:00
-- url     : https://prove2.me/submissions/c824da7e-c5e9-4093-895a-66037bf78709

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDimStrictDrop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DimStrictDrop
theorem _root_.solution : DimStrictDrop.Statement.{u} := by
  intro A _ Q Q' _ _ hlt
  let q : PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    ⟨⟨Q, inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q' : Set A)) :=
    ⟨⟨⟨Q', inferInstance⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr le_rfl⟩⟩
  have : Nonempty (PrimeSpectrum.zeroLocus (R := A) (Q : Set A)) := ⟨q⟩
  let f : PrimeSpectrum.zeroLocus (R := A) (Q' : Set A) → PrimeSpectrum.zeroLocus (R := A) (Q : Set A) :=
    fun x => ⟨x.1, (PrimeSpectrum.mem_zeroLocus _ _).mpr
      (le_trans (show (Q : Set A) ⊆ Q' from hlt.le) ((PrimeSpectrum.mem_zeroLocus _ _).mp x.2))⟩
  have hf : StrictMono f := fun a b h => h
  rw [ringKrullDim_quotient, ringKrullDim_quotient, Order.krullDim_eq_iSup_length,
    Order.krullDim_eq_iSup_length, ← WithBot.coe_one, ← WithBot.coe_add,
    ENat.iSup_add, WithBot.coe_le_coe, iSup_le_iff]
  intro l
  have hq : q < f l.head := by
    show Q < (l.head.1.asIdeal)
    exact lt_of_lt_of_le hlt ((PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2)
  refine le_trans ?_ (le_iSup _ ((l.map f hf).cons q hq))
  have hlen : ((l.map f hf).cons q hq).length = l.length + 1 := by
    simp [RelSeries.cons_length, LTSeries.map]
  rw [hlen]
  simp
end DimStrictDrop
end GroundTheory.Heights₂.Heights.NumbersDVR
