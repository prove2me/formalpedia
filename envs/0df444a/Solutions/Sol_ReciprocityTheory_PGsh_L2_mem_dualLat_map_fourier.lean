-- Prove2me | solution 1 for ReciprocityTheory.PGsh.L2.mem_dualLat_map_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:57:29.096386+00:00
-- url     : https://prove2.me/submissions/79ac0adc-e7ea-41ca-bd41-f8e1474003f9

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationFourierLeOne
import Definitions.Def_ReciprocityTheory_DualLattices_CharTableIsUnit
import Definitions.Def_ReciprocityTheory_DualLattices_TransposeMulSelf
import Definitions.Def_ReciprocityTheory_DualLattices_MemDualLatMapFourier
import Theorems.Thm_ReciprocityTheory_PGsh_L2_pairing_fourier
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
theorem _root_.solution (e : H ≃ AddChar N C) (M : Submodule R (N → C)) (w : H → C) :
    w ∈ dualLat (M.map (fourier (R := R) fun h a => e h a)) ↔
      fourier (R := R) (fun a h => e h a) w ∈ dualLat M := by
  rw [mem_dualLat_iff_pairing_integral, mem_dualLat_iff_pairing_integral]
  constructor
  · intro hw f hf
    obtain ⟨r, hr⟩ := hw _ (Submodule.mem_map_of_mem hf)
    exact ⟨r, hr.trans (pairing_fourier (R := R) e w f)⟩
  · intro hw g hg
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.1 hg
    obtain ⟨r, hr⟩ := hw f hf
    exact ⟨r, hr.trans (pairing_fourier (R := R) e w f).symm⟩
end ReciprocityTheory.PGsh.L2
