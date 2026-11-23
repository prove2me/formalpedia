-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.fourier_conv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:31:57.321636+00:00
-- url     : https://prove2.me/submissions/4bbe49a8-dd97-4903-a5ae-d50500ae100f

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution {H : Type} (χ : H → AddChar N C) (u w : N → C) (h : H) :
    fourier (R := R) (fun h a => χ h a) (conv u w) h =
      fourier (R := R) (fun h a => χ h a) u h * fourier (R := R) (fun h a => χ h a) w h := by
  rw [fourier_apply' (R := R), fourier_apply' (R := R), fourier_apply' (R := R),
    Finset.sum_mul_sum]
  simp only [conv, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.subRight a) _ _ fun c => ?_
  simp only [Equiv.subRight_apply]
  have hc : χ h c = χ h a * χ h (c - a) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    abel
  rw [hc]
  ring
end ReciprocityTheory.PGsh.L2
