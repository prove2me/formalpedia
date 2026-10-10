-- Prove2me | solution 1 for WeatherallGauge.classification
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T11:13:26.121521+00:00
-- url     : https://prove2.me/submissions/d336e1ee-62a6-43e4-89d2-dad631340553

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

namespace WeatherallGauge

theorem cls_main (X : CellComplex2) (K : Type) [AddCommGroup K] :
    (fieldStrength (X := X) (K := K).Faithful ↔ H0Vanishes X K) ∧ (fieldStrength (X := X) (K := K).Full ↔ H1Vanishes X K) ∧
    (fieldStrength (X := X) (K := K).EssSurj ↔ H2Vanishes X K) :=
  ⟨fi_main X K, fu_main X K, es_main X K⟩

end WeatherallGauge

open WeatherallGauge in
theorem solution (X : CellComplex2) (K : Type) [AddCommGroup K] :
    (fieldStrength (X := X) (K := K).Faithful ↔ H0Vanishes X K) ∧ (fieldStrength (X := X) (K := K).Full ↔ H1Vanishes X K) ∧
    (fieldStrength (X := X) (K := K).EssSurj ↔ H2Vanishes X K) :=
  cls_main X K
