-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.H_fix_e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:13.363271+00:00
-- url     : https://prove2.me/submissions/2693c56b-41cf-4e00-b58a-5207c4ad1a0c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Theorems.Thm_PI_LevelKSplit_W_SemiA_F0_castSucc
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
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiA
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r) (T : F)
variable {R σ J P T}
namespace PI.LevelKSplit.W.SemiA
theorem _root_.solution {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  have h1 := (mem_stabT (R := R) (σ := σ) (J := J) (tupH P) h).1 hh (Fin.castAdd r (Fin.castSucc a))
  simp only [tupH, Fin.append_left, F0_castSucc] at h1
  exact h1
end PI.LevelKSplit.W.SemiA
