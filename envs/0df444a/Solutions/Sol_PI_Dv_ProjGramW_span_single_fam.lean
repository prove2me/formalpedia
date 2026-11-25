-- Prove2me | solution 1 for PI.Dv.ProjGramW.span_single_fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:36:13.418696+00:00
-- url     : https://prove2.me/submissions/9daa009b-15b5-4a64-99a5-8e274ac4962b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_AlgebraMapNeZeroOfNotMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionGramMatrices_IdxDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjGramW
open NumberField IsDedekindDomain Formalism.BasicNotions
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace PI.Dv.ProjGramW
theorem _root_.solution {d : ℕ} (j0 : Fin d) (u : Fin d → K) (hu : ∀ k, k ≠ j0 → u k = 0) :
    Submodule.span (𝓞 K) (Set.range u) = Submodule.span (𝓞 K) {u j0} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = j0
    · rw [hk]; exact Submodule.subset_span rfl
    · rw [hu k hk]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ rfl
    exact Submodule.subset_span ⟨j0, rfl⟩
end PI.Dv.ProjGramW
