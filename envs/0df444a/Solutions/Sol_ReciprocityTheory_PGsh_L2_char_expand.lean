-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.char_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:21:05.61548+00:00
-- url     : https://prove2.me/submissions/cb62cf5a-43a9-4c6a-8274-daca0f05d4e5

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (e : H ≃ AddChar N C) (B : Matrix N N C) (hB : IsUnit B.det) (h : H) (a : N) :
    e h a = ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) h * B a i := by
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  symm
  calc ∑ i, fourier (R := R) (fun h a => e h a) (fun x => B⁻¹ i x) h * B a i
      = ∑ i, ∑ x, B a i * B⁻¹ i x * e h x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [fourier_apply', Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = ∑ x, ∑ i, B a i * B⁻¹ i x * e h x := Finset.sum_comm
    _ = ∑ x, (B * B⁻¹) a x * e h x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Matrix.mul_apply, Finset.sum_mul]
    _ = e h a := by simp [hBB, Matrix.one_apply]
end ReciprocityTheory.PGsh.L2
