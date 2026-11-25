-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.DLm.mainTerm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:38.745547+00:00
-- url     : https://prove2.me/submissions/87bb0ed5-f364-4592-aad1-9558040bfd41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_DensLemmaOfCut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DensityLemma_PDownTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.DLm
attribute [instance] TopModel.ng TopModel.ns TopModel.cs
namespace PI.UnitaryGroupMassFormula.DLm
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (β : ℂ) (m : ℕ)
    (Φ : G.Mat (m + 1 + 1) → V) (D' x : ℂ) :
    G.mainTerm β m (fun _ => 1) Φ x⁻¹ D' =
      ∑ j : Fin (G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).card,
        G.psi β ((((m : ℂ) + 2) * ((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)) * x) •
          ((((m : ℂ) + 2)⁻¹ * ((‖((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)‖ ^
              ((m + 1) ^ 2) : ℝ) : ℂ)) •
            G.OmLong β (m + 1) Φ ((G.rootSet (m + 2) ((-1) ^ (m + 3) * D')).equivFin.symm j : ℂ)) := by
  set S := G.rootSet (m + 2) ((-1) ^ (m + 3) * D')
  unfold G.mainTerm
  rw [Finset.smul_sum, ← Finset.sum_coe_sort S,
    ← Equiv.sum_comp S.equivFin.symm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_smul, smul_smul, div_inv_eq_mul]
  congr 1
  ring
end PI.UnitaryGroupMassFormula.DLm
