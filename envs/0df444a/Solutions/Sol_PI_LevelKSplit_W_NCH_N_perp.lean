-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.N_perp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:37:01.536079+00:00
-- url     : https://prove2.me/submissions/3ea0c100-8374-4191-9375-3b7337a76aa7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
import Theorems.Thm_PI_LevelKSplit_W_NCH_spanR_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution {g : HA R σ J} (hg : g ∈ Nsub R σ J P) (v : Fin M → R ⊗[F] E)
    (hv : Xp (datR R σ J P T) v) :
    lin R σ J g v - v ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  have hg' : UniC R σ J P.e g ∧ ∀ v, InXperp R σ J P v →
      lin R σ J g v - v ∈ spanR (F := F) R P.e Set.univ := hg
  rw [← spanR_eq]
  exact hg'.2 v hv
end PI.LevelKSplit.W.NCH
