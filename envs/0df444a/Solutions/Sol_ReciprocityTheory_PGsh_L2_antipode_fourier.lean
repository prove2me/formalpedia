-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.antipode_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:12:21.22088+00:00
-- url     : https://prove2.me/submissions/133db221-5d1f-45a1-886c-a3055cb0402d

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
import Theorems.Thm_ReciprocityTheory_PGsh_L2_e_neg_apply
import Theorems.Thm_P2M_ReciprocityTheory_PGsh_L2_fourier_apply__9ba6b889acde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset Matrix
namespace ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
private theorem mem_dualLat_iff_pairing_integral {X : Type} [Fintype X] {M : Submodule R (X → C)} {u : X → C} :
    u ∈ dualLat M ↔ ∀ f ∈ M, ∃ r : R, algebraMap R C r = ∑ a, u a * f a := Iff.rfl
end ReciprocityTheory.PGsh.L2
end
end

set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace ReciprocityTheory.PGsh.L2
theorem _root_.solution (e : H ≃ AddChar N C) (he : ∀ h h', e (h + h') = e h * e h')
    (AA : HopfOrder (C := C) R N) (u : N → C) (hu : u ∈ dualLat AA.carrier) :
    (fun x => fourier (R := R) (fun h a => e h a) u (-x)) ∈
      (dualLat AA.carrier).map (fourier (R := R) fun h a => e h a) := by
  rw [Submodule.mem_map]
  refine ⟨fun a => u (-a), ?_, ?_⟩
  · rw [mem_dualLat_iff_pairing_integral]
    intro f hf
    obtain ⟨r, hr⟩ := (mem_dualLat_iff_pairing_integral.1 hu) (fun x => f (-x)) (AA.antipode f hf)
    refine ⟨r, hr.trans ?_⟩
    exact Fintype.sum_equiv (Equiv.neg N) _ _ (fun a => by simp)
  · funext x
    simp only [fourier_apply']
    exact Fintype.sum_equiv (Equiv.neg N) _ _ (fun a => by simp [e_neg_apply e he])
end ReciprocityTheory.PGsh.L2
