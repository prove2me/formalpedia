-- Prove2me | solution 1 for WeatherallGauge.full_iff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T10:51:08.075043+00:00
-- url     : https://prove2.me/submissions/37f88c24-fbe5-4116-8945-07302a225887

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

theorem fu_main (X : CellComplex2) (K : Type) [AddCommGroup K] :
    fieldStrength (X := X) (K := K).Full ↔ H1Vanishes X K := by
  constructor
  · intro hF A hA
    let P : PotG X K := ⟨0⟩
    let Q : PotG X K := ⟨A⟩
    have hPQ : delta1 P.pot = delta1 Q.pot := by
      have h0 := delta1_add (X := X) (0 : C1 X K) 0
      simp only [add_zero] at h0
      have h00 : delta1 (0 : C1 X K) = 0 := by
        have := congrArg (· - delta1 (0 : C1 X K)) h0
        simpa using this.symm
      simp [P, Q, h00, hA]
    let f : (fieldStrength (X := X) (K := K)).obj P ⟶
        (fieldStrength (X := X) (K := K)).obj Q := eqToHom (by
      show Discrete.mk (delta1 P.pot) = Discrete.mk (delta1 Q.pot)
      rw [hPQ])
    obtain ⟨g, -⟩ := (fieldStrength (X := X) (K := K)).map_surjective f
    refine ⟨g.lam, ?_⟩
    have := g.eq
    simpa [P, Q] using this
  · intro hH
    refine ⟨fun {A A'} f => ?_⟩
    have hf : delta1 A.pot = delta1 A'.pot := Discrete.eq_of_hom f
    have hd : delta1 (A'.pot - A.pot) = 0 := by
      have := delta1_add (A'.pot - A.pot) A.pot
      rw [sub_add_cancel, ← hf] at this
      have h2 := congrArg (· - delta1 A.pot) this
      simpa using h2.symm
    obtain ⟨lam, hlam⟩ := hH _ hd
    exact ⟨⟨lam, by rw [hlam]; abel⟩, Subsingleton.elim _ _⟩

end WeatherallGauge

open WeatherallGauge in
theorem solution (X : CellComplex2) (K : Type) [AddCommGroup K] :
    fieldStrength (X := X) (K := K).Full ↔ H1Vanishes X K :=
  fu_main X K
