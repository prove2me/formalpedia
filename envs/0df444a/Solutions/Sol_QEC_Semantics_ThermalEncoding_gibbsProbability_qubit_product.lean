-- Prove2me | solution 1 for QEC.Semantics.ThermalEncoding.gibbsProbability_qubit_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:59:39.517013+00:00
-- url     : https://prove2.me/submissions/149d509f-ecb1-449f-b846-2d93d784b41a

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Core_Qubit
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Definitions.Def_QEC_Semantics_Dynamics_ThermalEncoding
import Theorems.Thm_QEC_Semantics_ThermalEncoding_gibbsPartitionFunction_qubit_product

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.ThermalEncoding
open Classical
open scoped BigOperators ComplexOrder TensorProduct
variable {H : Type}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics.ThermalEncoding
theorem _root_.solution {ι : Type} [Fintype ι] [Nonempty ι]
    (beta : Real) (energy : ι → Real) (q : Fin 2) (i : ι) :
    gibbsProbability beta (fun qi : Fin 2 × ι => energy qi.2) (q, i) =
      (2 : Real)⁻¹ * gibbsProbability beta energy i := by
  rw [gibbsProbability, gibbsProbability,
    gibbsPartitionFunction_qubit_product]
  field_simp [gibbsPartitionFunction_pos beta energy |>.ne']
end QEC.Semantics.ThermalEncoding
