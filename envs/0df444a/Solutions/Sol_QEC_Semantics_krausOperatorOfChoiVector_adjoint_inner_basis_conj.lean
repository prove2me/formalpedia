-- Prove2me | solution 1 for QEC.Semantics.krausOperatorOfChoiVector_adjoint_inner_basis_conj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:44:05.420723+00:00
-- url     : https://prove2.me/submissions/23eeabc6-0e23-4c21-a8f4-951455bddb2b

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Theorems.Thm_QEC_Semantics_krausOperatorOfChoiVector_adjoint_inner_basis

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
    inner Complex
      ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))
      (bH i) =
      star (v (i, p)) := by
  calc
    inner Complex
        ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))
        (bH i)
        = star (inner Complex (bH i)
            ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))) := by
          exact (inner_conj_symm
            ((LinearMap.adjoint (krausOperatorOfChoiVector bH bK v)) (bK p))
            (bH i)).symm
    _ = star (v (i, p)) := by
          rw [krausOperatorOfChoiVector_adjoint_inner_basis]
end QEC.Semantics
