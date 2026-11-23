-- Prove2me | solution 1 for PI.UnfoldEquiv.UnitaryGroupMassFormula.Q_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:28.410112+00:00
-- url     : https://prove2.me/submissions/f9693c4a-e8c0-41a0-9466-0fbd1dc2e43d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_ExtractFreeFillMatrix
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnfoldingEquivalence_Points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.UnfoldEquiv PI.UnfoldEquiv.Loc
noncomputable section
open PI PI.UnfoldEquiv PI.UnfoldEquiv.UnitaryGroupMassFormula
variable {k : Type} [CommRing k]
namespace PI.UnfoldEquiv.UnitaryGroupMassFormula
theorem _root_.solution {n' n c : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} {g : (Fin n → k) ≃ₗ[k] (Fin n → k)}
    (hr : R1cond k n c r) (hg : ∀ x, r (inX k n c x) = inX k n c (g x)) {xj : (Fin n' → k) →ₗ[k] (Fin n → k)}
    {x : (Fin (n' + (c + 1)) → k) →ₗ[k] (Fin (n + c) → k)} (h : Q xj x) :
    Q (g.toLinearMap ∘ₗ xj) (r.toLinearMap ∘ₗ x) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun v => ?_, fun hc => ?_, fun j hj1 hjc => ?_⟩
  · show r (x (inX k n' (c + 1) v)) = inX k n c (g (xj v))
    rw [h1, hg]
  · show r (x (eN k (n' + (c + 1)) n')) = eN k (n + c) n
    rw [h2 hc, hr.2.1]
  · show r (x (eN k (n' + (c + 1)) (n' + j))) - eN k (n + c) (n + j) ∈ Ufl k n c j
    have e : r (x (eN k (n' + (c + 1)) (n' + j))) - eN k (n + c) (n + j) =
        r (x (eN k (n' + (c + 1)) (n' + j)) - eN k (n + c) (n + j)) +
          (r (eN k (n + c) (n + j)) - eN k (n + c) (n + j)) := by
      rw [map_sub]
      abel
    rw [e]
    exact Submodule.add_mem _ (hr.1 j _ (h3 j hj1 hjc)) (hr.2.2 j)
end PI.UnfoldEquiv.UnitaryGroupMassFormula
