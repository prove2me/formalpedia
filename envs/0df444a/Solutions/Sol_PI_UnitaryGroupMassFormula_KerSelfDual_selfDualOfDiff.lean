-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.KerSelfDual.selfDualOfDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:56:09.821703+00:00
-- url     : https://prove2.me/submissions/62278955-91e9-467e-a302-b298e127390b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualDifferent_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualDifferent_SelfDualOfDiff
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSelfDual_inv_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.KerSelfDual
namespace PI.UnitaryGroupMassFormula.KerSelfDual
theorem _root_.solution : PI.KerIso.SelfDualOfDiff := by
  intro K E _ _ _ _ _ cj 𝔟 𝔟c hconj hc hd
  have hD : ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      (FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ :=
    coeIdeal_differentIdeal (𝓞 K) K E (𝓞 E)
  have hdual1 : FractionalIdeal.dual (𝓞 K) K (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero (𝓞 K) K one_ne_zero
  have hD0 : differentIdeal (𝓞 K) (𝓞 E) ≠ ⊥ := by
    intro h
    rw [h, FractionalIdeal.coeIdeal_bot] at hD
    exact inv_ne_zero hdual1 hD.symm
  have hb : 𝔟 ≠ ⊥ := by
    rintro rfl
    exact hD0 (by rw [hd, Ideal.bot_mul])
  have hbc : 𝔟c ≠ ⊥ := by
    rintro rfl
    exact hD0 (by rw [hd, Ideal.mul_bot])
  have hb0 : ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb
  have hbc0 : ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hbc
  have hdual : FractionalIdeal.dual (𝓞 K) K ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ =
      ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
    rw [FractionalIdeal.dual_inv, ← inv_inv (FractionalIdeal.dual (𝓞 K) K 1), ← hD, hd,
      FractionalIdeal.coeIdeal_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
  intro y
  rw [inv_map cj hconj.1 𝔟 𝔟c hc hb hbc y, ← hdual,
    FractionalIdeal.mem_dual (inv_ne_zero hb0)]
  refine forall₂_congr fun x _ => ?_
  rw [Algebra.traceForm_apply, mul_comm]
end PI.UnitaryGroupMassFormula.KerSelfDual
