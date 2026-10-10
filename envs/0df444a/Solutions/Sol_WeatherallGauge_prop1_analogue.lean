-- Prove2me | solution 1 for WeatherallGauge.prop1_analogue
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T10:07:20.247458+00:00
-- url     : https://prove2.me/submissions/3e709ec1-5a30-4bb0-ac27-74b238b47056

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

theorem p1a_main (X : CellComplex2) (K : Type) [AddCommGroup K]
    (h : ∃ lam : C0 X K, delta0 lam ≠ 0) :
    (fieldStrength0 (X := X) (K := K)).Faithful ∧ ¬ (fieldStrength0 (X := X) (K := K)).Full ∧
    ((fieldStrength0 (X := X) (K := K)).EssSurj ↔ H2Vanishes X K) := by
  refine ⟨⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩, ?_, ?_⟩
  · intro hF
    obtain ⟨lam, hlam⟩ := h
    have e : (fieldStrength0 (X := X) (K := K)).obj (Discrete.mk 0) ⟶
        (fieldStrength0 (X := X) (K := K)).obj (Discrete.mk (delta0 lam)) :=
      eqToHom (by
        change Discrete.mk (delta1 (0 : C1 X K)) = Discrete.mk (delta1 (delta0 lam))
        rw [delta1_delta0]
        congr 1
        funext p; simp [delta1])
    have hpre := (fieldStrength0 (X := X) (K := K)).preimage e
    exact hlam (Discrete.eq_of_hom hpre).symm
  · constructor
    · intro hE F
      obtain ⟨A, ⟨i⟩⟩ := hE.mem_essImage (Discrete.mk F)
      obtain ⟨A⟩ := A
      exact ⟨A, Discrete.eq_of_hom i.hom⟩
    · intro hH
      refine ⟨fun F => ?_⟩
      obtain ⟨A, hA⟩ := hH F.as
      exact ⟨Discrete.mk A, ⟨eqToIso (by
        change Discrete.mk (delta1 A) = F
        rw [hA])⟩⟩

end WeatherallGauge

open WeatherallGauge in
theorem solution (X : CellComplex2) (K : Type) [AddCommGroup K]
    (h : ∃ lam : C0 X K, delta0 lam ≠ 0) :
    (fieldStrength0 (X := X) (K := K)).Faithful ∧ ¬ (fieldStrength0 (X := X) (K := K)).Full ∧
    ((fieldStrength0 (X := X) (K := K)).EssSurj ↔ H2Vanishes X K) :=
  p1a_main X K h
