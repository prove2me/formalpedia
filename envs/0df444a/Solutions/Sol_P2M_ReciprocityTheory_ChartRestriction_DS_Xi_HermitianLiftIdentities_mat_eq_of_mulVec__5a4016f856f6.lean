-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_HermitianLiftIdentities_mat_eq_of_mulVec__5a4016f856f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:36.130449+00:00
-- url     : https://prove2.me/submissions/4d8af7ff-223b-4758-9481-e1e99c140c44

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ProdIicCastLE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HpkMulVecMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
namespace ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
theorem _root_.solution [DecidableEq ι] {A B : Matrix ι ι ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  exact Matrix.toLin'.injective (LinearMap.ext fun v => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h v])
end ReciprocityTheory.ChartRestriction.DS.Xi.HermitianLiftIdentities
