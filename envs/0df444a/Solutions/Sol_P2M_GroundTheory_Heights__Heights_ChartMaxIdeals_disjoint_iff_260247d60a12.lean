-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartMaxIdeals_disjoint_iff_260247d60a12
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:51:32.264177+00:00
-- url     : https://prove2.me/submissions/f73be4c9-8dbd-4229-b203-e98649885a35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProperSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartMaxIdeals

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMaxIdeals
variable {F : Type} [Field F] {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartMaxIdeals
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) F)} {t : Fin n → F}
    {p : Ideal (MvPolynomial (Fin e × Fin n) F)} [p.IsPrime] (P : Ideal (ChartInc I t e)) :
    Disjoint (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl : Set (ChartInc I t e)) (P : Set _) ↔
      P.comap (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) ≤ p := by
  constructor
  · intro hd s hs
    by_contra hsp
    exact Set.disjoint_left.mp hd ⟨s, hsp, rfl⟩ hs
  · intro hle
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hs (hle hmem)
end GroundTheory.Heights₂.Heights.ChartMaxIdeals
