-- Prove2me | solution 1 for WeatherallGauge.aharonov_bohm
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T11:02:20.721652+00:00
-- url     : https://prove2.me/submissions/a17a7471-8fac-41f9-b358-34df5eba3f11

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

theorem ab_main :
    delta1 (Pi.single 0 1 : C1 circle3 ℤ) = delta1 0 ∧
    IsEmpty ((⟨Pi.single 0 1⟩ : PotG circle3 ℤ) ⟶ ⟨0⟩) ∧
    ¬ (fieldStrength (X := circle3) (K := ℤ)).Full := by
  have h1 : delta1 (Pi.single 0 1 : C1 circle3 ℤ) = delta1 0 := funext fun p => p.elim0
  have h2 : IsEmpty ((⟨Pi.single 0 1⟩ : PotG circle3 ℤ) ⟶ ⟨0⟩) := by
    refine ⟨fun g => ?_⟩
    have e := g.eq
    have e0 := congrFun e 0
    have e1 := congrFun e 1
    have e2 := congrFun e 2
    simp [delta0, Fin.sum_univ_three] at e0 e1 e2
    omega
  refine ⟨h1, h2, fun hF => ?_⟩
  let f : (fieldStrength (X := circle3) (K := ℤ)).obj ⟨Pi.single 0 1⟩ ⟶
      (fieldStrength (X := circle3) (K := ℤ)).obj ⟨0⟩ := eqToHom (by
    show Discrete.mk (delta1 _) = Discrete.mk (delta1 _)
    rw [h1])
  obtain ⟨g, -⟩ := (fieldStrength (X := circle3) (K := ℤ)).map_surjective f
  exact h2.false g

end WeatherallGauge

open WeatherallGauge in
theorem solution :
    delta1 (Pi.single 0 1 : C1 circle3 ℤ) = delta1 0 ∧
    IsEmpty ((⟨Pi.single 0 1⟩ : PotG circle3 ℤ) ⟶ ⟨0⟩) ∧
    ¬ (fieldStrength (X := circle3) (K := ℤ)).Full :=
  ab_main
