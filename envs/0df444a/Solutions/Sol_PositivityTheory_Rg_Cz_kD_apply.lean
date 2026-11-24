-- Prove2me | solution 1 for PositivityTheory.Rg.Cz.kD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:19.988025+00:00
-- url     : https://prove2.me/submissions/a71204c9-3172-4fd1-8f6d-1b069cd2aee4

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_CasimirAlgebra_KugaCoordinates_KugaAbsoluteValues_KSumApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Fin Function
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Cz
variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M]
namespace PositivityTheory.Rg.Cz
theorem _root_.solution (T : P →ₗ[ℝ] Module.End ℂ M) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (v : Fin (m + 1) → P) :
    kD T η v = ∑ i : Fin (m + 1), (-1 : ℤ) ^ (i : ℕ) • T (v i) (η (i.removeNth v)) := by
  simp [kD, AlternatingMap.alternatizeUncurryFin_apply, kPre, kLop]
end PositivityTheory.Rg.Cz
