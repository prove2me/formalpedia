-- Prove2me | solution 1 for ShiSpread.sum_spread_reindex_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-11T09:43:20.180174+00:00
-- url     : https://prove2.me/submissions/e1e05793-5dbf-41ff-845c-3611904a5917

import Definitions.Def_ShiSpread_Core
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Filter

set_option autoImplicit false

open ShiSpread ShiShallow

theorem solution {m n : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) (χ : QState m)
    (H : Bits m → ℂ → ℝ) (hH : ∀ z : Bits m, H z 0 = 0) :
    ∑ y : Bits n, H (restrict e y) (spread e χ y) = ∑ z : Bits m, H z (χ z) := by
  classical
  obtain ⟨extd, hextd⟩ :
      ∃ f : Bits m → Bits n,
        ∀ (z : Bits m) (k : Fin n), f z k = if h : ∃ i, e i = k then z h.choose else false :=
    ⟨fun z k => if h : ∃ i, e i = k then z h.choose else false, fun _ _ => rfl⟩
  have hzero : ∀ y : Bits n, ¬ (∀ k : Fin n, OffImage e k → y k = false) →
      spread e χ y = 0 := by
    intro y hy
    simp only [spread]
    rw [if_neg hy]
  have hpos : ∀ y : Bits n, (∀ k : Fin n, OffImage e k → y k = false) →
      spread e χ y = χ (restrict e y) := by
    intro y hy
    simp only [spread]
    rw [if_pos hy]
  have hres : ∀ z : Bits m, restrict e (extd z) = z := by
    intro z
    funext i
    have hex : ∃ i', e i' = e i := ⟨i, rfl⟩
    have h1 : restrict e (extd z) i = extd z (e i) := rfl
    rw [h1, hextd, dif_pos hex, he hex.choose_spec]
  have hoff : ∀ (z : Bits m) (k : Fin n), OffImage e k → extd z k = false := by
    intro z k hk
    have hne : ¬ ∃ i, e i = k := fun hi => hk hi.choose hi.choose_spec
    rw [hextd, dif_neg hne]
  have hleft : ∀ y : Bits n, (∀ k : Fin n, OffImage e k → y k = false) →
      extd (restrict e y) = y := by
    intro y hy
    funext k
    rw [hextd]
    by_cases hk : ∃ i, e i = k
    · rw [dif_pos hk]
      have h2 : restrict e y hk.choose = y (e hk.choose) := rfl
      rw [h2, hk.choose_spec]
    · rw [dif_neg hk]
      exact (hy k (fun i hi => hk ⟨i, hi⟩)).symm
  have hsum : ∑ y ∈ Finset.univ.filter
        (fun y : Bits n => ∀ k : Fin n, OffImage e k → y k = false),
        H (restrict e y) (spread e χ y)
      = ∑ y : Bits n, H (restrict e y) (spread e χ y) := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro y _ hy
    have hy' : ¬ (∀ k : Fin n, OffImage e k → y k = false) := by
      simpa [Finset.mem_filter] using hy
    rw [hzero y hy']
    exact hH _
  rw [← hsum]
  exact Finset.sum_nbij' (restrict e) extd (fun y _ => Finset.mem_univ _)
    (fun z _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoff z⟩)
    (fun y hy => hleft y (Finset.mem_filter.mp hy).2)
    (fun z _ => hres z)
    (fun y hy => congrArg (H (restrict e y)) (hpos y (Finset.mem_filter.mp hy).2))
