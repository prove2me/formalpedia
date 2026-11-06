-- Prove2me | solution 1 for QEC.Semantics.krausOperatorOfChoiVector_toMatrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:33:28.674886+00:00
-- url     : https://prove2.me/submissions/dc6e8738-e42c-41f6-a056-c203f68cc76c

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus

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
theorem _root_.solution {n : Nat} {betaK : Type*} [Fintype betaK]
    (bH : OrthonormalBasis (Fin n) Complex H)
    (bK : OrthonormalBasis betaK Complex K)
    (v : Fin n × betaK → Complex) :
    LinearMap.toMatrix bH.toBasis bK.toBasis (krausOperatorOfChoiVector bH bK v) =
      fun p i => star (v (i, p)) := by
  classical
  unfold krausOperatorOfChoiVector
  exact LinearMap.toMatrix_toLin bH.toBasis bK.toBasis _
end QEC.Semantics
