-- Prove2me | solution 1 for PI.DvRows.val_star_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:36:50.673683+00:00
-- url     : https://prove2.me/submissions/7e5e7854-188b-41ec-a3dc-a56ce1967d6b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DivisionRowsRationalLattice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProjectionRows_ValLeOneOfMemRange
import Theorems.Thm_PI_DvRows_val_eq_one_of_not_mem
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.DvRows
open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace PI.DvRows
theorem _root_.solution (w w' : HeightOneSpectrum (𝓞 K)) (hww : IsConjPlK w w') (s : 𝓞 K)
    (hs : s ∉ w'.asIdeal) : w.valuation K (star (algebraMap (𝓞 K) K s)) = 1 := by
  have h1 := val_eq_one_of_not_mem w' s hs
  have hv : vAdd w' (algebraMap (𝓞 K) K s) = 0 := by
    unfold vAdd; rw [h1, WithZero.log_one, neg_zero]
  rw [hww] at hv
  have hne : star (algebraMap (𝓞 K) K s) ≠ 0 := by
    intro h0
    have : algebraMap (𝓞 K) K s = 0 := by simpa using congrArg star h0
    rw [this, map_zero] at h1
    exact zero_ne_one h1
  have hv0 : w.valuation K (star (algebraMap (𝓞 K) K s)) ≠ 0 := by simpa using hne
  unfold vAdd at hv
  have : WithZero.log (w.valuation K (star (algebraMap (𝓞 K) K s))) = 0 := by linarith
  rw [← WithZero.exp_log hv0, this, WithZero.exp_zero]
end PI.DvRows
