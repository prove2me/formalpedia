-- Prove2me | solution 1 for QEC.Semantics.exists_finiteKrausFamily_of_stdChoiMatrix_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:43:40.193124+00:00
-- url     : https://prove2.me/submissions/5b3b6ee4-b4f8-4974-8d58-4136757bd81c

import Definitions.Def_QEC_Semantics_Channels_Choi
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_Channels_ChoiKraus
import Theorems.Thm_QEC_Semantics_exists_finiteKrausFamily_of_choiMatrix_posSemidef

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
theorem _root_.solution
    (Φ : Operator H →ₗ[Complex] Operator K)
    (hchoi : (stdChoiMatrix Φ).PosSemidef) :
    ∃ (m : Nat), ∃ R : FiniteKrausFamily (Fin m) H K,
      R.inducedMap = Φ := by
  exact exists_finiteKrausFamily_of_choiMatrix_posSemidef Φ
    (stdOrthonormalBasis Complex H) (stdOrthonormalBasis Complex K) hchoi
end QEC.Semantics
