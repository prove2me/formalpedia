-- Prove2me | solution 1 for ReciprocityTheory.CA.IsCM.localization_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:57:06.109609+00:00
-- url     : https://prove2.me/submissions/fe3dac76-d65b-478d-9b22-00bc136f8db4

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ExistsIsRegularOfLeHeight
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_LocDim
import Theorems.Thm_ReciprocityTheory_CA_IsCM_depthGE_localization_of_le_height

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
namespace IsCM
theorem _root_.solution (h : IsCM R) (P : Ideal R) [P.IsPrime] :
    IsCM (Localization.AtPrime P) := by
  haveI : IsNoetherianRing R := h.1
  have hfin : P.height ≠ ⊤ := by
    first
    | exact Ideal.height_ne_top (Ideal.IsPrime.ne_top ‹_›)
    | exact (Ideal.height_lt_top (Ideal.IsPrime.ne_top ‹_›)).ne
    | exact Ideal.height_ne_top ‹_›
    | (rw [Ideal.IsPrime.height_eq_primeHeight]; exact (Ideal.primeHeight_lt_top P).ne)
    | (rw [Ideal.height_eq_primeHeight P]; exact (Ideal.primeHeight_lt_top P).ne)
    | exact (Ideal.primeHeight_lt_top P).ne
  refine ⟨inferInstance, P.height.toNat, ?_,
    h.depthGE_localization_of_le_height P (by rw [ENat.coe_toNat hfin])⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
  conv_lhs => rw [← ENat.coe_toNat hfin]
  rfl
end IsCM
end ReciprocityTheory.CA
