-- Prove2me | solution 1 for ValTrackRM.Public.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T05:26:57.808834+00:00
-- url     : https://prove2.me/submissions/96b4c8a0-c42e-4ed3-b824-ef8adb696830

import Mathlib
import Definitions.Def_ValTrackRM_Public_Model
import Theorems.Thm_ValTrackRM_Public_theorem_1_exact

open ValTrackRM.Public

theorem solution {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hr : ∀ j, j < m → r j < r (j + 1))
    (sel : (Fin k → Fin (m + 1)) → Fin k) (hsel : ∀ (L : Fin k → Fin (m + 1)) (i : Fin k), L (sel L) ≤ L i)
    (V : List (Fin (m + 1))) :
    cStar r m * opt r k V ≤ expRevenue r sel V := by
  obtain ⟨h1, h2⟩ := theorem_1_exact hm hk r hr0 hr sel hsel V
  have hpos : 0 < qSum r m := by
    have hq : ∀ p ∈ Finset.Icc 1 m, 0 < qj r p := by
      intro p hp
      simp only [Finset.mem_Icc] at hp
      have hs : ∀ a b, a < b → b ≤ m → r a < r b := by
        intro a b
        induction b with
        | zero => intro h; omega
        | succ b ih =>
          intro h hb
          rcases Nat.lt_succ_iff_lt_or_eq.mp h with h1 | h1
          · exact (ih h1 (by omega)).trans (hr b (by omega))
          · subst h1; exact hr a (by omega)
      have hp0 : 0 < r p := by have := hs 0 p (by omega) hp.2; rwa [hr0] at this
      have hlt := hs (p - 1) p (by omega) hp.2
      have : r (p - 1) / r p < 1 := (div_lt_one hp0).mpr hlt
      unfold qj; linarith
    exact Finset.sum_pos hq ⟨m, by simp; omega⟩
  unfold cStar
  rw [h1, h2]
  field_simp
  rfl
