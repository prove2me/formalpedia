-- Prove2me | solution 1 for PI.VolSemiDirect.W.heisenberg_le_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:43.483481+00:00
-- url     : https://prove2.me/submissions/12b677d7-0d28-4cec-a39d-1df5a184474b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_SemiDefs
import Theorems.Thm_Formalism_L2_SG_Sub_mem_stabT


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
namespace PI.VolSemiDirect.W
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ}
    (P : Frame E M r) : Hsub R σ J P ≤ S0 R σ J P := by
  intro g hg
  rw [Hsub, mem_stabT] at hg
  rw [S0, mem_stabT]
  intro b
  have := hg (Fin.castAdd r b)
  simpa [tupH, Fin.append_left] using this
end PI.VolSemiDirect.W
