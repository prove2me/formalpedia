-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P02.localizableBoolean_iso
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:35:46.46735+00:00
-- url     : https://prove2.me/submissions/187e0e71-92e6-4295-8acb-f0b202d8eaf7

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P02
noncomputable section

open MeasureTheory Set

open scoped ENNReal Topology CompactlySupported

open QAlgorithms.Papers.Independent.Renew46.P02

universe u v

lemma g64i_loc {B : Type u} {C : Type v}
    [BooleanAlgebra B] [BooleanAlgebra C] (mu : BooleanMeasure B) (nu : BooleanMeasure C)
    (e : B ≃o C) (hmeas : ∀ a : B, nu.value (e a) = mu.value a) :
    IsLocalizableBoolean mu → IsLocalizableBoolean nu := by
  rintro ⟨hsup, hsemi⟩
  refine ⟨fun S => ?_, fun p hp => ?_⟩
  · obtain ⟨a, ha⟩ := hsup (e.symm '' S)
    refine ⟨e a, ?_⟩
    have := e.symm.isLUB_image.mp ha
    simpa using this
  · have hp' : e.symm p ≠ ⊥ := by
      intro h; apply hp; rw [← e.apply_symm_apply p, h, e.map_bot]
    obtain ⟨q, hq0, hqp, hqf⟩ := hsemi _ hp'
    refine ⟨e q, ?_, ?_, ?_⟩
    · intro h; apply hq0; rw [← e.symm_apply_apply q, h, e.symm.map_bot]
    · rw [← e.apply_symm_apply p]; exact e.monotone hqp
    · rw [hmeas]; exact hqf

theorem solution {B : Type u} {C : Type v}
    [BooleanAlgebra B] [BooleanAlgebra C] (mu : BooleanMeasure B) (nu : BooleanMeasure C)
    (e : B ≃o C) (hmeas : ∀ a : B, nu.value (e a) = mu.value a) :
    IsLocalizableBoolean mu ↔ IsLocalizableBoolean nu :=
  ⟨g64i_loc mu nu e hmeas, g64i_loc nu mu e.symm fun c => by
    rw [← hmeas (e.symm c), e.apply_symm_apply]⟩

end
