-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.FlagGramNonneg.form_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:40:20.21554+00:00
-- url     : https://prove2.me/submissions/760622ff-fa98-4078-ab21-fc185b60b6df

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_HasSignatureExistsNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg
namespace PI.UnitaryGroupMassFormula.FlagGramNonneg
theorem _root_.solution {n m : Type} [Fintype n] [Fintype m] (e : n ≃ m) (J : Matrix n n ℂ)
    (x : n → ℂ) :
    star (fun i => x (e.symm i)) ⬝ᵥ ((J.reindex e e) *ᵥ (fun i => x (e.symm i))) =
      star x ⬝ᵥ (J *ᵥ x) := by
  have h : (J.reindex e e) *ᵥ (fun i => x (e.symm i)) = fun i => (J *ᵥ x) (e.symm i) := by
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    funext i
    simp [Function.comp_def]
  rw [h]
  simp only [dotProduct, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (x i) * (J *ᵥ x) i)
end PI.UnitaryGroupMassFormula.FlagGramNonneg
