-- Prove2me | solution 1 for Rudin.sSup_image_stable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T00:03:30.535197+00:00
-- url     : https://prove2.me/submissions/501aefd0-364f-4a19-bc06-30c3e24dc98a

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Set

theorem solution {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (f g : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ s, |f x - g x| ≤ ε) :
    |sSup (f '' s) - sSup (g '' s)| ≤ ε := by
  have hba : BddAbove (f '' s) ↔ BddAbove (g '' s) := by
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨M + ε, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have h := (abs_le.mp (hfg x hx)).1
      have hfx : f x ≤ M := hM ⟨x, hx, rfl⟩
      linarith
    · rintro ⟨M, hM⟩
      refine ⟨M + ε, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have h := (abs_le.mp (hfg x hx)).2
      have hgx : g x ≤ M := hM ⟨x, hx, rfl⟩
      linarith
  by_cases hf : BddAbove (f '' s)
  · have hg : BddAbove (g '' s) := hba.mp hf
    have hfne : (f '' s).Nonempty := hs.image f
    have hgne : (g '' s).Nonempty := hs.image g
    rw [abs_le]
    constructor
    · have hle : sSup (g '' s) ≤ sSup (f '' s) + ε := by
        apply csSup_le hgne
        rintro y ⟨x, hx, rfl⟩
        have h := (abs_le.mp (hfg x hx)).1
        have hsup : f x ≤ sSup (f '' s) := le_csSup hf ⟨x, hx, rfl⟩
        linarith
      linarith
    · have hle : sSup (f '' s) ≤ sSup (g '' s) + ε := by
        apply csSup_le hfne
        rintro y ⟨x, hx, rfl⟩
        have h := (abs_le.mp (hfg x hx)).2
        have hsup : g x ≤ sSup (g '' s) := le_csSup hg ⟨x, hx, rfl⟩
        linarith
      linarith
  · have hg : ¬ BddAbove (g '' s) := by simpa [hba] using hf
    rw [csSup_of_not_bddAbove hf, csSup_of_not_bddAbove hg]
    simpa using hε
