-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiA.mapX_S
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:45.752823+00:00
-- url     : https://prove2.me/submissions/5711cd9e-fc11-4914-bdf9-8ea452d5236d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiAlg
import Theorems.Thm_PI_LevelKSplit_W_SemiA_spanR_le
import Theorems.Thm_PI_LevelKSplit_W_SemiA_S_e

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
theorem _root_.solution {g : HA R σ J} (hg : g ∈ Ssub R σ J P) : (datR R σ J P T).MapX (lin R σ J g) := by
  intro a
  show lin R σ J g (ratV (F := F) R (P.e a)) ∈ _
  have h1 := spanR_le (σ := σ) (J := J) (T := T) _ (S_e hg a)
  have h2 : ratV (F := F) R (P.e a) ∈ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) :=
    Submodule.subset_span ⟨a, rfl⟩
  have h3 := Submodule.add_mem _ h1 h2
  rw [sub_add_cancel] at h3
  exact h3
end PI.LevelKSplit.W.SemiA
