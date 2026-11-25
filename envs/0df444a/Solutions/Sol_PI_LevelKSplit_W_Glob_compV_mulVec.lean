-- Prove2me | solution 1 for PI.LevelKSplit.W.Glob.compV_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:48:43.949883+00:00
-- url     : https://prove2.me/submissions/7d4d1a44-2187-44c2-a877-aa869148bbc9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Glob
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
namespace PI.LevelKSplit.W.Glob
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (g : HA (Af F) σ J) (x : Fin n → Af F ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (fun i => phiV v (x i)) =
      fun i => phiV v (lin (Af F) σ J g x i) := by
  funext i
  exact (RingHom.map_mulVec (phiV v)
    (HA.mat (R := Af F) (σ := σ) (J := J) g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) x i).symm
end PI.LevelKSplit.W.Glob
