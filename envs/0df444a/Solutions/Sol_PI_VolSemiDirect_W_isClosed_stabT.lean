-- Prove2me | solution 1 for PI.VolSemiDirect.W.isClosed_stabT
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:50:43.377091+00:00
-- url     : https://prove2.me/submissions/788c7465-6ebd-4a33-963a-e451f1608fc2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_Closed
import Theorems.Thm_PI_VolSemiDirect_W_continuous_lin
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
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  [TopologicalSpace R] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R}
variable (R)
namespace PI.VolSemiDirect.W
theorem _root_.solution [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] {a : ℕ}
    (X : Fin a → Fin n → E) : IsClosed (stabT R σ J X : Set (HA R σ J)) := by
  have hset : (stabT R σ J X : Set (HA R σ J)) =
      ⋂ b, {g | lin R σ J g (ratV (F := F) R (X b)) = ratV (F := F) R (X b)} := by
    ext g
    simp [mem_stabT]
  rw [hset]
  exact isClosed_iInter fun b => isClosed_eq (continuous_lin R σ J _) continuous_const
end PI.VolSemiDirect.W
