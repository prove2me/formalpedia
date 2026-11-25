-- Prove2me | solution 1 for PI.GreenLabelMapW.greenLab_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:42.561792+00:00
-- url     : https://prove2.me/submissions/d13062ce-bf9f-4045-9f22-b632deb3ba26

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv
import Theorems.Thm_PI_GreenLabelMapW_hasCuspLabel_of_trace
import Theorems.Thm_PI_GreenLabelMapW_trace_of_iso

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
theorem _root_.solution (Cv : LabelConv K) (d : ℕ) (τ τ' : FDRep ℂ (GL (Fin d) K))
    (h : Nonempty (τ ≅ τ')) : greenLab Cv d τ = greenLab Cv d τ' := by
  obtain ⟨e⟩ := h
  unfold greenLab
  congr 1
  funext P
  exact propext ⟨hasCuspLabel_of_trace Cv (trace_of_iso e),
    hasCuspLabel_of_trace Cv (fun γ => (trace_of_iso e γ).symm)⟩
end PI.GreenLabelMapW
