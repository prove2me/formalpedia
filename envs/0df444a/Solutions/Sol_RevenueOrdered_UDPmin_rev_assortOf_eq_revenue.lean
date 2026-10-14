-- Prove2me | solution 1 for RevenueOrdered.UDPmin.rev_assortOf_eq_revenue
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T04:06:13.293822+00:00
-- url     : https://prove2.me/submissions/755fda6c-edcd-48be-aad5-e3ba5dbbfbd3

import Mathlib
import Definitions.Def_RevenueOrdered_UDPmin_Reduction
import Theorems.Thm_RevenueOrdered_UDPmin_rev_eq_revenue_priceOf

open RevenueOrdered.UDPmin

theorem solution {X M : Type*} [Fintype X] [DecidableEq X] [Fintype M] [Nonempty M]
    (I : Instance X M) (p : X → ℝ) (hp : ∀ x, ∃ i, p x = I.v i) :
    RevenueOrdered.Tightness.rev (redP I) (redRev I) (assortOf I p) = revenue I p := by
  classical
  rw [rev_eq_revenue_priceOf]
  have he : priceOf I (assortOf I p) = p := by
    funext x
    obtain ⟨i,hi⟩ := hp x
    let y : RedProd I := (x,⟨I.v i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)
    have hy : y ∈ assortOf I p := by simp [assortOf,y,hi]
    have hm : p x ∈ ((assortOf I p).filter (fun z => z.1=x)).image (fun z => (z.2 : ℝ)) := by
      exact Finset.mem_image.mpr ⟨y,by simp [hy,y],hi.symm⟩
    rw [priceOf,dif_pos ⟨_,hm⟩]
    apply le_antisymm (Finset.min'_le _ _ hm)
    apply Finset.le_min'
    intro w hw
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hz,hzx⟩ := Finset.mem_filter.mp hz
    have hpz := (Finset.mem_filter.mp hz).2
    simpa only [hzx] using hpz
  rw [he]
