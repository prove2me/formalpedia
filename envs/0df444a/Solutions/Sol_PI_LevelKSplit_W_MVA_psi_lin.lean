-- Prove2me | solution 1 for PI.LevelKSplit.W.MVA.psi_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:51:37.52539+00:00
-- url     : https://prove2.me/submissions/01cbbca6-a5e6-4b53-87d3-f42f4d1db5e4

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ConjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_CjDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TopoAF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MapFstConjTranspose

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.MVA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]
variable (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
namespace PI.LevelKSplit.W.MVA
theorem _root_.solution (g : HA R2 σ J) (x : Fin M → (R1 × R2) ⊗[F] E) :
    psiE R1 R2 (lin (R1 × R2) σ J (lift R1 R2 σ J g) x) =
      ((psiE R1 R2 x).1, lin R2 σ J g (psiE R1 R2 x).2) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show p1 R1 R2 (Matrix.mulVec (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) x i) = p1 R1 R2 (x i)
    rw [RingHom.map_mulVec, matrix_lift_fst, Matrix.one_mulVec]
    rfl
  · show p2 R1 R2 (Matrix.mulVec (mlift R1 R2 (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E))) x i) =
      Matrix.mulVec (HA.mat R2 σ J g : Matrix (Fin M) (Fin M) (R2 ⊗[F] E)) (fun k => p2 R1 R2 (x k)) i
    rw [RingHom.map_mulVec, matrix_lift_snd]
    rfl
end PI.LevelKSplit.W.MVA
