-- Prove2me | solution 1 for WeatherallGauge.faithful_iff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T10:07:30.141986+00:00
-- url     : https://prove2.me/submissions/894eca12-deba-40b4-a776-6c2881a75f47

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

theorem fi_main (X : CellComplex2) (K : Type) [AddCommGroup K] :
    (fieldStrength (X := X) (K := K)).Faithful ↔ H0Vanishes X K := by
  constructor
  · intro hF lam hlam
    let A : PotG X K := ⟨0⟩
    let f : A ⟶ A := ⟨lam, by simp [A, hlam]⟩
    have h := (fieldStrength (X := X) (K := K)).map_injective
      (X := A) (Y := A) (a₁ := f) (a₂ := 𝟙 A) (Subsingleton.elim _ _)
    exact congrArg GaugeHom.lam h
  · intro hH
    refine ⟨fun {A A'} f g _ => ?_⟩
    apply GaugeHom.ext
    have hf := f.eq
    have hg := g.eq
    have hd : delta0 (f.lam - g.lam) = 0 := by
      have := delta0_add (f.lam - g.lam) g.lam
      rw [sub_add_cancel] at this
      have h2 : A.pot + delta0 f.lam = A.pot + delta0 g.lam := hf.trans hg.symm
      have h3 : delta0 f.lam = delta0 g.lam := add_left_cancel h2
      rw [h3] at this
      simpa using this.symm
    exact sub_eq_zero.mp (hH _ hd)

end WeatherallGauge

open WeatherallGauge in
theorem solution (X : CellComplex2) (K : Type) [AddCommGroup K] :
    (fieldStrength (X := X) (K := K)).Faithful ↔ H0Vanishes X K :=
  fi_main X K
