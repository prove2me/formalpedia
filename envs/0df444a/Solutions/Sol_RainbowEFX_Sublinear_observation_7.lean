-- Prove2me | solution 1 for RainbowEFX.Sublinear.observation_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:48:26.417077+00:00
-- url     : https://prove2.me/submissions/12f4210d-6061-46e4-9127-f6846e4d8b5a

import Mathlib
import Definitions.Def_RainbowEFX_Sublinear_Setting

open LittleCharity.EFX RainbowEFX.Sublinear

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (hv : LittleCharity.MMS.IsAdditive v) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (X : Fin n → Finset (Fin m)) (S : Finset (Fin m)) :
    ((∃ i, HeavilyEnvies ε v X i S) → ∃ t Z, IsMEAWitnessPair ε v X S t Z) ∧
    ((∃ i, StronglyEnvies ε v X i S) →
      ∀ t, IsMostEnviousAgent ε v X S t → StronglyEnvies ε v X t S) := by
  classical
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    set F := S.powerset.filter (fun Z => ∃ j, HeavilyEnvies ε v X j Z) with hF
    have hSF : S ∈ F := by simp [hF]; exact ⟨i, hi⟩
    obtain ⟨Z, hZF, hZmin⟩ := Finset.exists_min_image F Finset.card ⟨S, hSF⟩
    simp only [hF, Finset.mem_filter, Finset.mem_powerset] at hZF
    obtain ⟨hZS, t, ht⟩ := hZF
    refine ⟨t, Z, hZS, ht, ?_⟩
    rintro j ⟨T, hTZ, hT⟩
    have hTF : T ∈ F := by
      simp only [hF, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hTZ.subset.trans hZS, j, hT⟩
    have h1 := hZmin T hTF
    have h2 := Finset.card_lt_card hTZ
    omega
  · rintro ⟨i, hi⟩ t ⟨Z, hZS, ht, hno⟩
    by_cases hZ : Z = S
    · subst hZ
      exact absurd hi (hno i)
    · exact ⟨Z, Finset.ssubset_iff_subset_ne.mpr ⟨hZS, hZ⟩, ht⟩
