-- Prove2me | solution 1 for QEC.Semantics.krausOperatorOfChoiVector_adjoint_inner_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:46.378248+00:00
-- url     : https://prove2.me/submissions/780facf9-5b03-4eb9-973e-d0f51eafceae

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Theorems.Thm_QEC_Semantics_krausOperatorOfChoiVector_inner_basis

set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics
theorem _root_.solution {n : Nat} {betaK : Type*}
    [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) (i : Fin n) (p : betaK) :
    inner Complex (bH i)
      ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p)) =
      v (i, p) := by
  rw [LinearMap.adjoint_inner_right]
  exact krausOperatorOfChoiVector_inner_basis bH bK v i p
end QEC.Semantics
