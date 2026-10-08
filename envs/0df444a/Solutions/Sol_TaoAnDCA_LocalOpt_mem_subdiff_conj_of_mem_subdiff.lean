-- Prove2me | solution 1 for TaoAnDCA.LocalOpt.mem_subdiff_conj_of_mem_subdiff
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:18:36.60084+00:00
-- url     : https://prove2.me/submissions/bdec2276-12cc-4ba3-87dd-4dff17c087a0

import Mathlib
import Definitions.Def_TaoAnDCA_LocalOpt_Setting

open InnerProductSpace TaoAnDCA.GlobalOpt

namespace Round35

lemma invert_subgradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : ∀ x, f x ≠ ⊥) (x y : EuclideanSpace ℝ (Fin n))
    (hy : InertialFB.IFB.IsSubgradient f x y) :
    InertialFB.IFB.IsSubgradient (CondatPD.FinDim.conj f) y x := by
  obtain ⟨hx, hs⟩ := hy
  lift f x to ℝ using ⟨hx, hf x⟩ with a ha
  have he : CondatPD.FinDim.conj f y = ((inner ℝ y x - a : ℝ) : EReal) := by
    apply le_antisymm
    · apply iSup_le
      intro z
      by_cases hz : f z = ⊤
      · simp [hz]
      lift f z to ℝ using ⟨hz, hf z⟩ with b hb
      have ht := hs z
      rw [← hb, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right] at ht
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith
    · have ht := le_iSup (fun z => ((inner ℝ y z : ℝ) : EReal) - f z) x
      simpa only [← ha, ← EReal.coe_sub, CondatPD.FinDim.conj] using ht
  refine ⟨by rw [he]; exact EReal.coe_ne_top _, ?_⟩
  intro v
  have ht := le_iSup (fun z => ((inner ℝ v z : ℝ) : EReal) - f z) x
  rw [← ha, ← EReal.coe_sub] at ht
  rw [he, ← EReal.coe_add]
  convert ht using 1
  · congr 1
    rw [inner_sub_right, real_inner_comm v x, real_inner_comm y x]
    ring
  · rfl

end Round35

theorem solution {n : ℕ} (g h : EuclideanSpace ℝ (Fin n) → EReal)
    (hgh : TaoAnDCA.GlobalOpt.DCStanding g h) (xs ys : EuclideanSpace ℝ (Fin n))
    (hy : ys ∈ TaoAnDCA.GlobalOpt.subdiff h xs) (hyg : ys ∈ TaoAnDCA.GlobalOpt.subdiff g xs) :
    xs ∈ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj g) ys ∩ TaoAnDCA.GlobalOpt.subdiff (CondatPD.FinDim.conj h) ys := by
  exact ⟨Round35.invert_subgradient g hgh.g_mem.1 xs ys hyg,
    Round35.invert_subgradient h hgh.h_mem.1 xs ys hy⟩

#print axioms solution
