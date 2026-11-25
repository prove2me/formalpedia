-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.StepA.ea_yx_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:37.671915+00:00
-- url     : https://prove2.me/submissions/3a97c075-907d-4f0b-a3ba-7484d872a677

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_Phi2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LastBasisZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_gv_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_rankOne_mem_unitary
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_phiV__herm_394ba4fdb226
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_yx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_StepA_ea_hinv_gv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
private theorem herm_mulVec_mulVec_of_mem_GV {k r : ℕ} {M : Mat k r} (hM : M ∈ GV k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (M *ᵥ v) (M *ᵥ w) = herm (Hpk k r) v w := by
  have h : Mᴴ * Hpk k r * M = Hpk k r := hM
  rw [herm, herm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, h]
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
end
end

set_option autoImplicit false
noncomputable section
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate ComplexOrder
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.StepA
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace ReciprocityTheory.ChartRestriction.DS.Xi.StepA
theorem _root_.solution {k r' : ℕ} (hk : 1 ≤ k) (hHI : HeisInv) (hHM : HeisMem) (hOSM : OneStepMem) (x : HPar k r')
    (a b : Fin (1 + r' + 1)) : herm (Hpk k (1 + r')) (Yx k r' x a) (Yx k r' x b) = 0 := by
  rw [ea_yx, ea_yx,
    herm_mulVec_mulVec_of_mem_GV (ea_gv_mul (ea_hinv_gv hHI hHM x) (rankOne_mem_unitary hOSM (one_ne_zero : (1 : ℂ) ≠ 0)))]
  exact ea_phiV'_herm (r := 1 + r') hk a b
end ReciprocityTheory.ChartRestriction.DS.Xi.StepA
