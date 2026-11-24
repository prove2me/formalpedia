-- Prove2me | solution 1 for PI.GreenLabelMapW.isCuspidal_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:54.304267+00:00
-- url     : https://prove2.me/submissions/934be329-ad94-4659-9509-ee4c5e27240c

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_RootPowCard
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GreenLabelCharpoly_IrreducibleCharpolyInv

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
theorem _root_.solution (τ : FDRep ℂ (GL (Fin 1) K)) : IsCuspidal K τ := by
  intro s b hb hs
  exfalso
  have h := Fintype.card_le_of_surjective b hb
  simp only [Fintype.card_fin] at h
  omega
end PI.GreenLabelMapW
