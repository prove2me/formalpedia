-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.ga_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:36:34.652835+00:00
-- url     : https://prove2.me/submissions/999ce3f8-7bc7-4208-8ae9-5becf598a8ce

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_InductiveHeisenbergInputs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_gs_fac
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_det_gram_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_ga_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_linInd_toLp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {n m : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (k r : ℕ) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (hY : LinearIndependent ℂ Y)
    (l : Fin (r + 1)) : 0 < Ga k r l Y := by
  rw [ga_eq]
  have hw := (linInd_toLp Y hY).comp _ (Fin.castLE_injective (show l.val + 1 ≤ r + 1 by omega))
  obtain ⟨u, τ, hu, hτ, hd, hwe, -⟩ := gs_fac (fun a : Fin (l.val + 1) =>
    (WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) hw
  rw [det_gram_of _ u τ hu hτ hwe, Complex.ofReal_re]
  exact Finset.prod_pos fun j _ => pow_pos (norm_pos_iff.2 (hd j)) 2
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
