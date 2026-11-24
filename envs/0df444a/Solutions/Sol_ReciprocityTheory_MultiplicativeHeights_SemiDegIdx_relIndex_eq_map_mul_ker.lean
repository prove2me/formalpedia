-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.relIndex_eq_map_mul_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:12:59.397472+00:00
-- url     : https://prove2.me/submissions/85e6684b-0470-4e4f-9f65-519f2b267a22

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
open NumberField
open scoped nonZeroDivisors
namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
theorem _root_.solution {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) {A B : AddSubgroup G} (hAB : A ≤ B) :
    A.relIndex B = (A.map f).relIndex (B.map f) * (A ⊓ f.ker).relIndex (B ⊓ f.ker) := by
  have hN : A ⊓ (B ⊓ f.ker) = A ⊓ f.ker := by
    rw [← inf_assoc, inf_eq_left.mpr hAB]
  have hC : (A ⊔ f.ker) ⊓ B = A ⊔ (B ⊓ f.ker) := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hx⟩
      refine ⟨y, hy, z, ⟨?_, hz⟩, rfl⟩
      have := B.sub_mem hx (hAB hy)
      simpa using this
    · rintro ⟨y, hy, z, ⟨hzB, hz⟩, rfl⟩
      exact ⟨⟨y, hy, z, hz, rfl⟩, B.add_mem (hAB hy) hzB⟩
  have h1 : (A.map f).relIndex (B.map f) = (A ⊔ (B ⊓ f.ker)).relIndex B := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq,
      ← AddSubgroup.inf_relIndex_right, hC]
  have h2 : (A ⊓ f.ker).relIndex (B ⊓ f.ker) = A.relIndex (A ⊔ (B ⊓ f.ker)) := by
    rw [sup_comm A, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right A (B ⊓ f.ker),
      hN]
  rw [h1, h2, mul_comm]
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hAB inf_le_left)).symm
end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
