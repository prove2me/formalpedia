-- Prove2me | solution 1 for PI.LocJacOrd.W.arithO_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:07:41.376824+00:00
-- url     : https://prove2.me/submissions/1a4402a6-00bd-4d6c-9f76-5d0ca1fa4822

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalJacobianOrder_AbsVNeZero
import Theorems.Thm_PI_LocJacOrd_W_Ar_absV_ne_zero
import Theorems.Thm_PI_LocJacOrd_W_Ar_absV_prod_sq
import Theorems.Thm_PI_LocJacOrd_W_Ar_alp_ne_zero
import Theorems.Thm_PI_LocJacOrd_W_Ar_arith_real

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LocJacOrd PI.LocJacOrd.W
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacOrd
namespace PI.LocJacOrd.W
theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ArithO (F := F) v := by
  intro typed g r m ht
  have hJ : jacS v typed g r = ∏ l : Fin r, ((∏ i ∈ Finset.univ.filter
      (fun i : Fin (r + 1) => (i : ℕ) ≤ (l : ℕ)), absV v (alp v r i) ^ 2) ^ 2) ^ 2 := by
    rw [jacS]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [if_neg ht, mul_one, Ar.absV_prod_sq]
  rw [hJ]
  exact Ar.arith_real r m (fun i => absV v (alp v r i)) (fun i => Ar.absV_ne_zero v (Ar.alp_ne_zero v r i))
end PI.LocJacOrd.W
