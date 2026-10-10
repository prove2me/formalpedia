-- Prove2me | solution 1 for WeatherallGauge.essSurj_iff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T10:51:26.643692+00:00
-- url     : https://prove2.me/submissions/a4e23dc9-4861-419b-b341-8b8cf971f2f3

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

theorem es_main (X : CellComplex2) (K : Type) [AddCommGroup K] :
    fieldStrength (X := X) (K := K).EssSurj ↔ H2Vanishes X K := by
  constructor
  · intro hE F
    obtain ⟨A, ⟨e⟩⟩ := hE.mem_essImage (Discrete.mk F)
    exact ⟨A.pot, Discrete.eq_of_hom e.hom⟩
  · intro hH
    refine ⟨fun F => ?_⟩
    obtain ⟨A, hA⟩ := hH F.as
    exact ⟨⟨A⟩, ⟨eqToIso (by
      show Discrete.mk (delta1 A) = F
      rw [hA])⟩⟩

end WeatherallGauge

open WeatherallGauge in
theorem solution (X : CellComplex2) (K : Type) [AddCommGroup K] :
    fieldStrength (X := X) (K := K).EssSurj ↔ H2Vanishes X K :=
  es_main X K
