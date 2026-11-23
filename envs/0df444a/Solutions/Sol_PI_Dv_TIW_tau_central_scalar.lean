-- Prove2me | solution 1 for PI.Dv.TIW.tau_central_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:30.752866+00:00
-- url     : https://prove2.me/submissions/0f105385-421e-4965-a9e4-f87049890683

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TransferIndices_TauCentralScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.TIW
open PI.Dv
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G] (T : GoodSet K G) (s : T.S)
namespace PI.Dv.TIW
theorem _root_.solution (c : MonoidAlgebra K G) (hc : ∀ z, c * z = z * c) :
    ∃ μ : K, (T.tau s).asAlgebraHom c = μ • 1 := by
  have hmem : (T.tau s).asAlgebraHom c ∈ Subalgebra.center K (Module.End K (T.W s)) := by
    rw [Subalgebra.mem_center_iff]
    intro M
    obtain ⟨z, rfl⟩ := T.irr s M
    rw [← map_mul, ← map_mul, hc z]
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hmem
  obtain ⟨μ, hμ⟩ := hmem
  exact ⟨μ, by rw [← hμ, Algebra.algebraMap_eq_smul_one]⟩
end PI.Dv.TIW
