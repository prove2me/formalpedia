-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.DetB.hermForm_phi_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:18:28.792021+00:00
-- url     : https://prove2.me/submissions/798fd762-b7a1-4e53-a5f9-80eccc91c420

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_HermitianLiftIdentities
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_DetB_cst_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.DetB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB
theorem _root_.solution (k r : ℕ) (a b : Fin (r + 1)) :
    cst (Hpk k r) (phiV' k r b) (phiV' k r a) ≤ K0 k r := by
  unfold K0
  calc cst (Hpk k r) (phiV' k r b) (phiV' k r a) ≤ ∑ b', cst (Hpk k r) (phiV' k r b') (phiV' k r a) :=
        Finset.single_le_sum (f := fun b' => cst (Hpk k r) (phiV' k r b') (phiV' k r a))
          (fun _ _ => cst_nonneg _ _ _) (Finset.mem_univ b)
    _ ≤ _ := Finset.single_le_sum (f := fun a' => ∑ b', cst (Hpk k r) (phiV' k r b') (phiV' k r a'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => cst_nonneg _ _ _) (Finset.mem_univ a)
end ReciprocityTheory.ChartRestriction.DS.Xi.DetB
