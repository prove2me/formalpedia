-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Ainf.local_of_surj_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:32.322227+00:00
-- url     : https://prove2.me/submissions/35479e03-6f55-4ea2-ac39-ba89533047cb

import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_ATowerInh
import Definitions.Def_ReciprocityTheory_DualLattices_AinfFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
open ReciprocityTheory ReciprocityTheory.PGsh
open ReciprocityTheory.PGsh.Ainf
variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
namespace ReciprocityTheory.PGsh.Ainf
theorem _root_.solution {S T : Type} [CommRing S] [CommRing T] [IsLocalRing T] (f : S →+* T)
    (hf : Function.Surjective f) (hk : ∀ k ∈ RingHom.ker f, k * k = 0) : IsLocalRing S := by
  haveI : Nontrivial S := hf.nontrivial
  have key : ∀ y : S, IsUnit (f y) → IsUnit y := by
    intro y hy
    obtain ⟨u, hu⟩ := hy
    obtain ⟨z, hz⟩ := hf (↑u⁻¹ : T)
    have hker : y * z - 1 ∈ RingHom.ker f := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_one, hz, ← hu, Units.mul_inv, sub_self]
    have hsq := hk _ hker
    have h1 : y * (z * (1 - (y * z - 1))) = 1 := by linear_combination -hsq
    exact ⟨⟨y, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (f x) with h | h
  · exact Or.inl (key x h)
  · exact Or.inr (key (1 - x) (by rwa [map_sub, map_one]))
end ReciprocityTheory.PGsh.Ainf
