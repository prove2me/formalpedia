-- Prove2me | solution 1 for PI.FJMX.hwVec_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:24.561892+00:00
-- url     : https://prove2.me/submissions/5db5110a-d15a-44a7-8f43-aaa31b3596bb

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_IsDiagonalBlockIndexRightOfPositiveRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
variable {p q r s : ℕ}
namespace PI.FJMX
theorem _root_.solution (w : Ln p q r s → ℕ) (a b c d : List ℤ) (d1 d2 d3 d4 : ℕ)
    (h1 : IsWeightedHomogeneous w (shapeProd (varMat (fun i : Fin p => (Sum.inl i : Ix p q))
      (fun k : Fin r => (Sum.inl k : Ix r s))) (posPart a)) d1)
    (h2 : IsWeightedHomogeneous w (shapeProd (varMat (fun i : Fin p => (Sum.inl (Fin.rev i) : Ix p q))
      (fun l : Fin s => (Sum.inr (Fin.rev l) : Ix r s))) (negPart b)) d2)
    (h3 : IsWeightedHomogeneous w (shapeProd (varMat (fun j : Fin q => (Sum.inr j : Ix p q))
      (fun l : Fin s => (Sum.inr l : Ix r s))) (posPart c)) d3)
    (h4 : IsWeightedHomogeneous w (shapeProd (varMat (fun j : Fin q => (Sum.inr (Fin.rev j) : Ix p q))
      (fun k : Fin r => (Sum.inl (Fin.rev k) : Ix r s))) (negPart d)) d4) :
    IsWeightedHomogeneous w (hwVec p q r s a b c d) (d1 + d2 + d3 + d4) := by
  unfold hwVec
  exact ((h1.mul h2).mul h3).mul h4
end PI.FJMX
