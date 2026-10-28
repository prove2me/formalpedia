-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support50.P46.local_divergence_cancellation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T08:58:37.664561+00:00
-- url     : https://prove2.me/submissions/a154d319-f96b-4896-9634-eb20a24f8ec1

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P46

open QAlgorithms.Papers.Independent.Support50.P46

theorem solution (n m D : ℕ) (hD : m < D)
    (hn : m + 1 < n) (incident : Finset (Fin n))
    (hincident : incident.card ≤ m + 1) (f : Finset (Fin n) → ℝ)
    (hempty : f ∅ = 0) :
    alternatingInformation n (localDivergence incident f) = 0 := by
  classical
  have hne : incident ≠ Finset.univ := by
    intro h; rw [h, Finset.card_univ, Fintype.card_fin] at hincident; omega
  obtain ⟨i, -, hi⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
  unfold alternatingInformation localDivergence
  refine Finset.sum_involution (fun s _ => symmDiff s {i}) ?_ ?_ (by simp) (by simp)
  · intro s _
    have hint : symmDiff s {i} ∩ incident = s ∩ incident := by
      ext x; by_cases hx : x = i
      · subst hx; simp [hi]
      · simp [Finset.mem_symmDiff, hx]
    rw [hint]
    by_cases hs : i ∈ s
    · have : symmDiff s {i} = s.erase i := by
        ext x; by_cases hx : x = i <;> simp [Finset.mem_symmDiff, hx, hs]
      rw [this, ← Finset.card_erase_add_one hs, pow_succ]; ring
    · have : symmDiff s {i} = insert i s := by
        ext x; by_cases hx : x = i <;> simp [Finset.mem_symmDiff, hx, hs]
      rw [this, Finset.card_insert_of_notMem hs, pow_succ]; ring
  · intro s _ _ h
    have := congrArg (i ∈ ·) h
    by_cases hs : i ∈ s <;> simp [Finset.mem_symmDiff, hs] at this
