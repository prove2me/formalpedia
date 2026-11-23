-- Prove2me | solution 1 for PI.Dv.ProjGramW.idx_eq_zero_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:07.651088+00:00
-- url     : https://prove2.me/submissions/41bd9d05-88fd-410c-bdb8-df14eefe28a6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_IdxCalc
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Theorems.Thm_PI_Dv_ProjGramW_idxAt_antisymm
import Theorems.Thm_PI_Dv_ProjGramW_span_le_of_locLe
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X Y : Submodule (𝓞 K) V}
    (hX : X.FG) (hY : Y.FG) (hXY : LocLe w 0 X Y) (hYX : LocLe w 0 Y X) : idxAt w X Y = 0 := by
  have hs : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V) :=
    le_antisymm (span_le_of_locLe w hXY) (span_le_of_locLe w hYX)
  have h1 := (hI K V w Y X hY hX hs.symm).2.2.2.1 0 hXY
  have h2 := (hI K V w X Y hX hY hs).2.2.2.1 0 hYX
  have h3 := idxAt_antisymm w Y X
  simp only [Nat.cast_zero, zero_mul] at h1 h2
  linarith
end PI.Dv.ProjGramW
