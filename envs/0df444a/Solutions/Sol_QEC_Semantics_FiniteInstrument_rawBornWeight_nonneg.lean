-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.rawBornWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:22:33.202186+00:00
-- url     : https://prove2.me/submissions/0ec5942b-9766-4d48-944f-02c6b2d3215b

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBranchOperator_positive

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K) (index : κ)
    (rho : DensityOperator H) :
    0 ≤ I.rawBornWeight index rho :=
  (Complex.nonneg_iff.mp
    (I.rawBranchOperator_positive index rho.positive).trace_nonneg).1
end QEC.Semantics.FiniteInstrument
