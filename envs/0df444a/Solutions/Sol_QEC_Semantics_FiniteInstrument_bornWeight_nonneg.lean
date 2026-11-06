-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bornWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:24:50.275982+00:00
-- url     : https://prove2.me/submissions/c9b70eec-8aca-4839-994d-0c65f17ac5a2

import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Instruments_Core

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
theorem _root_.solution (I : FiniteInstrument κ Ω H K) (outcome : Ω)
    (rho : DensityOperator H) :
    0 ≤ I.bornWeight outcome rho := by
  exact
    (Complex.nonneg_iff.mp
      (I.branchOperator_positive outcome rho.positive).trace_nonneg).1
end QEC.Semantics.FiniteInstrument
