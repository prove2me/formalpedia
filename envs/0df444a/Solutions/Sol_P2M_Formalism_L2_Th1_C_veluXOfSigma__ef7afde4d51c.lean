-- Prove2me | solution 1 for P2M_Formalism_L2_Th1_C_veluXOfSigma__ef7afde4d51c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:31:14.743822+00:00
-- url     : https://prove2.me/submissions/6df254de-4546-4f6e-989d-63ade4edb19e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA
import Theorems.Thm_Formalism_L2_Th1_C_USideA_hs_of
import Theorems.Thm_Formalism_L2_Th1_C_USideA_cc_mulBy
import Theorems.Thm_Formalism_L2_Th1_C_USideA_subst_mulBy_l
import Theorems.Thm_Formalism_L2_Th1_C_USideA_subst_rescale
import Theorems.Thm_Formalism_L2_Th1_C_USideA_l_ne_zero
import Theorems.Thm_P2M_Formalism_L2_Th1_C_USideA_subst_C__a942db7ebe55
import Theorems.Thm_Formalism_L2_Th1_C_USideA_subst_wpShift_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open USideA
namespace Formalism.L2.Th1.C
theorem _root_.solution : VeluXFromZ := by
  intro K _ _ e l linv A c0 ι _ neg xP w xs al h hXW hE hw
  have hl : PowerSeries.HasSubst l := hs_of h.1
  have hm : PowerSeries.HasSubst (mulBy l linv al) := hs_of (cc_mulBy h al)
  have hal : PowerSeries.HasSubst (PowerSeries.C al * l) := hs_of (by simp [h.1])
  have F0 : (A + PowerSeries.C c0 * PowerSeries.X ^ 2) * l ^ 2 =
      PowerSeries.X ^ 2 * PowerSeries.subst l (wpShift e 0) := hXW
  have F1 := F0
  rw [subst_wpShift_zero hl] at F1
  have F2 := congrArg (PowerSeries.subst (mulBy l linv al)) F0
  rw [← PowerSeries.coe_substAlgHom hm] at F2
  simp only [map_add, map_mul, map_pow, PowerSeries.coe_substAlgHom] at F2
  rw [subst_C', PowerSeries.subst_X hm, subst_mulBy_l h, PowerSeries.subst_comp_subst_apply hl hm,
    subst_mulBy_l h, subst_wpShift_zero hal] at F2
  have hZr : PowerSeries.subst (PowerSeries.C al * l) e = PowerSeries.subst l (PowerSeries.rescale al e) := by
    rw [subst_rescale h, PowerSeries.subst_comp_subst_apply hl hm, subst_mulBy_l h]
  have F3 := congrArg (PowerSeries.subst l) hE.2.2
  rw [← PowerSeries.coe_substAlgHom hl] at F3
  simp only [map_add, map_mul, map_sum, map_sub, PowerSeries.coe_substAlgHom] at F3
  simp only [subst_C'] at F3
  simp only [hw, ← hZr, map_pow, map_add] at F3
  have hsum : ∑ P, (xs P + PowerSeries.C c0 - (PowerSeries.C (xP P) + PowerSeries.C c0)) =
      ∑ P, (xs P - PowerSeries.C (xP P)) := Finset.sum_congr rfl (fun P _ => by ring)
  rw [hsum] at F3
  unfold veluXs
  simp only [map_pow, map_mul, map_sub, map_one]
  have key : l ^ 2 * (PowerSeries.C al ^ 2 * PowerSeries.subst (mulBy l linv al) A * PowerSeries.X ^ 2 -
      mulBy l linv al ^ 2 * (A + PowerSeries.X ^ 2 * (∑ P, (xs P - PowerSeries.C (xP P)) -
        (PowerSeries.C al ^ 2 - 1) * PowerSeries.C c0))) = 0 := by
    linear_combination PowerSeries.X ^ 2 * F2 + mulBy l linv al ^ 2 * PowerSeries.X ^ 2 * l ^ 2 * F3 -
      mulBy l linv al ^ 2 * F1
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left (pow_ne_zero 2 (l_ne_zero h)))
end Formalism.L2.Th1.C
