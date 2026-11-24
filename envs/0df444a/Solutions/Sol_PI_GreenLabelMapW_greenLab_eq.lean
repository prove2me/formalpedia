-- Prove2me | solution 1 for PI.GreenLabelMapW.greenLab_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:26:55.440132+00:00
-- url     : https://prove2.me/submissions/0fc6c46b-ea7a-4dcc-85bf-8a1f69acbf65

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
import Theorems.Thm_PI_GreenLabelMapW_greenLab_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES
noncomputable section
open PI PI.GreenLabelMapW
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
namespace PI.GreenLabelMapW
theorem _root_.solution (Cv : LabelConv K) (hC : CuspParam K Cv) {d : ℕ} (hd : 1 ≤ d)
    {τ : FDRep ℂ (GL (Fin d) K)} (hs : Simple τ) (hc : IsCuspidal K τ) {P : K[X]}
    (hP : HasCuspLabel Cv τ P) : greenLab Cv d τ = P := by
  exact ((hC d hd).1 τ hs hc).1.unique (greenLab_spec Cv hC hd hs hc) hP
end PI.GreenLabelMapW
