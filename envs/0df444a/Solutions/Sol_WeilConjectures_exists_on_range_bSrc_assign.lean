-- Prove2me | solution 1 for WeilConjectures.exists_on_range_bSrc_assign
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:23:35.331892+00:00
-- url     : https://prove2.me/submissions/4d45ee35-0249-4492-acd2-7b0dfe4eeb24

import Mathlib

/-!
A48/A59: 0-child dite on-range assign.
On-range via Classical.choose + e.injective; off-range via 0 ∈ ker.
Map eqs via hv / hoff + zero_smul. (bKer unused — zeros suffice for mem_ker.)
-/

open Classical

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial K))
    (d : ι → Polynomial K)
    {n : ℕ} (e : Fin n ↪ ι)
    (bTgt : Module.Basis ι (Polynomial K) (ι → Polynomial K))
    (v : Fin n → (ι → Polynomial K))
    (hv : ∀ j, Matrix.toLin' M (v j) = d (e j) • bTgt (e j))
    (hoff : ∀ i, (∀ j : Fin n, e j ≠ i) → d i = 0)
    {m : ℕ}
    (bKer : Module.Basis (Fin m) (Polynomial K)
      (LinearMap.ker (Matrix.toLin' M))) :
    ∃ (f : ι → (ι → Polynomial K)),
      (∀ i, Matrix.toLin' M (f i) = d i • bTgt i) ∧
        (∀ j, f (e j) = v j) ∧
          (∀ i, (∀ j : Fin n, e j ≠ i) →
            f i ∈ LinearMap.ker (Matrix.toLin' M)) := by
  let _ := bKer
  let f : ι → (ι → Polynomial K) := fun i =>
    if h : ∃ j : Fin n, e j = i then v (Classical.choose h) else 0
  refine ⟨f, ?hmap, ?hon, ?hker⟩
  · intro i
    by_cases h : ∃ j : Fin n, e j = i
    · simp only [f, dif_pos h]
      have hce : e (Classical.choose h) = i := Classical.choose_spec h
      rw [hv, hce]
    · simp only [f, dif_neg h, map_zero]
      have hoffi : d i = 0 := hoff i (fun j hj => h ⟨j, hj⟩)
      rw [hoffi, zero_smul]
  · intro j
    have h : ∃ j' : Fin n, e j' = e j := ⟨j, rfl⟩
    simp only [f, dif_pos h]
    have : Classical.choose h = j := e.injective (Classical.choose_spec h)
    rw [this]
  · intro i hoffi
    have h : ¬∃ j : Fin n, e j = i := fun ⟨j, hj⟩ => hoffi j hj
    simp only [f, dif_neg h, Submodule.zero_mem]
