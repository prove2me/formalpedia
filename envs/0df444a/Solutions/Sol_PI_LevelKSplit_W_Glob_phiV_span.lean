-- Prove2me | solution 1 for PI.LevelKSplit.W.Glob.phiV_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:48:42.934046+00:00
-- url     : https://prove2.me/submissions/8e68f658-d098-467c-8e38-6172cccfc7fa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevelSAllOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulVecSpanStable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_RatVMemSpan
import Theorems.Thm_PI_LevelKSplit_W_Glob_spanR_univ
import Theorems.Thm_PI_LevelKSplit_W_Glob_phiV_ratV

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
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (Y : Fin m → Fin n → E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ spanR (F := F) (Af F) Y Set.univ) :
    (fun i => phiV v (y i)) ∈
      Submodule.span (Fv F v ⊗[F] E) (Set.range fun a => ratV (F := F) (Fv F v) (Y a)) := by
  rw [spanR_univ] at hy
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    rw [phiV_ratV]
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero =>
    have h0 : (fun i => phiV v ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := by
      funext i; simp
    rw [h0]; exact Submodule.zero_mem _
  | add w w' _ _ hw hw' =>
    have h1 : (fun i => phiV v ((w + w') i)) = (fun i => phiV v (w i)) + fun i => phiV v (w' i) := by
      funext i; simp
    rw [h1]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw =>
    have h1 : (fun i => phiV v ((c • w) i)) = phiV v c • fun i => phiV v (w i) := by
      funext i; simp
    rw [h1]; exact Submodule.smul_mem _ _ hw
end PI.LevelKSplit.W.Glob
