-- Prove2me | solution 1 for PI.LevelKSplit.W.Glob.H_fix_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:16:48.445066+00:00
-- url     : https://prove2.me/submissions/b59f7f8a-f6fa-4c9a-b5a5-6af273621e2c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
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
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.Glob
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
variable {R σ J}
namespace PI.LevelKSplit.W.Glob
theorem _root_.solution {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J k (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [Hsub, mem_stabT] at hk
  simpa [tupH, F0, Fin.append_left, Fin.snoc_castSucc] using hk (Fin.castAdd r (Fin.castSucc a))
end PI.LevelKSplit.W.Glob
