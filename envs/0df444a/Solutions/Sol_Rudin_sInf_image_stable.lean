-- Prove2me | solution 1 for Rudin.sInf_image_stable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-14T00:03:31.203748+00:00
-- url     : https://prove2.me/submissions/64d3cc9b-8824-49d3-8615-708b8ebda023

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Set

theorem solution {ι : Type*} (s : Set ι) (hs : s.Nonempty)
    (f g : ι → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hfg : ∀ x ∈ s, |f x - g x| ≤ ε) :
    |sInf (f '' s) - sInf (g '' s)| ≤ ε := by
  have hbb : BddBelow (f '' s) ↔ BddBelow (g '' s) := by
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨M - ε, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have h := (abs_le.mp (hfg x hx)).2
      have hfx : M ≤ f x := hM ⟨x, hx, rfl⟩
      linarith
    · rintro ⟨M, hM⟩
      refine ⟨M - ε, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have h := (abs_le.mp (hfg x hx)).1
      have hgx : M ≤ g x := hM ⟨x, hx, rfl⟩
      linarith
  by_cases hf : BddBelow (f '' s)
  · have hg : BddBelow (g '' s) := hbb.mp hf
    have hfne : (f '' s).Nonempty := hs.image f
    have hgne : (g '' s).Nonempty := hs.image g
    rw [abs_le]
    constructor
    · have hle : sInf (g '' s) - ε ≤ sInf (f '' s) := by
        apply le_csInf hfne
        rintro y ⟨x, hx, rfl⟩
        have h := (abs_le.mp (hfg x hx)).1
        have hinf : sInf (g '' s) ≤ g x := csInf_le hg ⟨x, hx, rfl⟩
        linarith
      linarith
    · have hle : sInf (f '' s) - ε ≤ sInf (g '' s) := by
        apply le_csInf hgne
        rintro y ⟨x, hx, rfl⟩
        have h := (abs_le.mp (hfg x hx)).2
        have hinf : sInf (f '' s) ≤ f x := csInf_le hf ⟨x, hx, rfl⟩
        linarith
      linarith
  · have hg : ¬ BddBelow (g '' s) := by simpa [hbb] using hf
    rw [csInf_of_not_bddBelow hf, csInf_of_not_bddBelow hg]
    simpa using hε
