-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_Xi_BL_gram_mat__78f14edbfb72
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:01:57.207127+00:00
-- url     : https://prove2.me/submissions/28ac0b3d-d9eb-4b57-8324-31149129dfc6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_MatExtBvec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InvSqrtTwoMulSelf

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
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
open ReciprocityTheory.ChartRestriction.DS.Xi.BL
namespace ReciprocityTheory.ChartRestriction.DS.Xi.BL
theorem _root_.solution {N L : ℕ} (X : Fin L → Fin N → ℂ) (Xm : Matrix (Fin N) (Fin L) ℂ) (hX : ∀ p a, Xm p a = X a p) :
    (Matrix.of fun a b => star (X a) ⬝ᵥ X b) = Xmᴴ * Xm := by
  ext a b; simp [Matrix.mul_apply, dotProduct, conjTranspose_apply, hX]
end ReciprocityTheory.ChartRestriction.DS.Xi.BL
