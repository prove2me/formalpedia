-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.sum_bornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:38:14.863385+00:00
-- url     : https://prove2.me/submissions/f559c0c4-7f30-4627-acf2-9cb1c2655a5d

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Instruments_Core
import Theorems.Thm_QEC_Semantics_FiniteInstrument_sum_bornWeight_eq_trace_re

set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
attribute [local instance] QEC.Semantics.FiniteInstrument._p2m_local_instance_a5f1a79248_39
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution (I : FiniteInstrument κ Ω H K)
    (hComplete : I.kraus.Complete) (rho : DensityOperator H) :
    ∑ outcome : Ω, I.bornWeight outcome rho = 1 := by
  rw [I.sum_bornWeight_eq_trace_re hComplete rho, rho.trace_one]
  norm_num
end QEC.Semantics.FiniteInstrument
