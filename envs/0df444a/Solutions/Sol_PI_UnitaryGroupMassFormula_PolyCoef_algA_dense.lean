-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PolyCoef.algA_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:22.317626+00:00
-- url     : https://prove2.me/submissions/b55ba774-6914-491c-94ff-76eec62cb2f4

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EvalDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGroupIntegrability_InstCompactUG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PolyCoef
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.PolyCoef
theorem _root_.solution (N : ℕ) (F : C(UG N, ℂ)) {ε : ℝ} (hε : 0 < ε) : ∃ f ∈ algA N, ‖F - f‖ < ε := by
  have hsep : (algA N).SeparatesPoints := by
    intro x y hxy
    have hne : (x : Matrix (Fin N) (Fin N) ℂ) ≠ y := fun h => hxy (Subtype.ext h)
    obtain ⟨i, j, hij⟩ : ∃ i j, (x : Matrix (Fin N) (Fin N) ℂ) i j ≠ (y : Matrix (Fin N) (Fin N) ℂ) i j := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      exact hne (Matrix.ext hcon)
    refine ⟨coordC i j, ⟨coordC i j, StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩, rfl⟩, hij⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints (algA N) hsep
  have hF : F ∈ closure ((algA N : Set C(UG N, ℂ))) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]; trivial
  obtain ⟨f, hf, hd⟩ := Metric.mem_closure_iff.mp hF ε hε
  exact ⟨f, hf, by rwa [dist_eq_norm] at hd⟩
end PI.UnitaryGroupMassFormula.PolyCoef
