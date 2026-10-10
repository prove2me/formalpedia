-- Prove2me | solution 1 for WeatherallGauge.filledTriangle_forgets_only_stuff
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-10T11:03:14.795305+00:00
-- url     : https://prove2.me/submissions/f19a3610-efb9-4973-8261-0674fdf28111

import Mathlib
import Definitions.Def_WeatherallGauge_defs

open CategoryTheory

namespace WeatherallGauge

theorem ft_full (X : CellComplex2) (K : Type) [AddCommGroup K] (hH : H1Vanishes X K) :
    (fieldStrength (X := X) (K := K)).Full := by
  refine ⟨fun {A A'} f => ?_⟩
  have hf : delta1 A.pot = delta1 A'.pot := Discrete.eq_of_hom f
  have hd : delta1 (A'.pot - A.pot) = 0 := by
    have := delta1_add (A'.pot - A.pot) A.pot
    rw [sub_add_cancel, ← hf] at this
    have h2 := congrArg (· - delta1 A.pot) this
    simpa using h2.symm
  obtain ⟨lam, hlam⟩ := hH _ hd
  exact ⟨⟨lam, by rw [hlam]; abel⟩, Subsingleton.elim _ _⟩

theorem ft_es (X : CellComplex2) (K : Type) [AddCommGroup K] (hH : H2Vanishes X K) :
    (fieldStrength (X := X) (K := K)).EssSurj := by
  refine ⟨fun F => ?_⟩
  obtain ⟨A, hA⟩ := hH F.as
  exact ⟨⟨A⟩, ⟨eqToIso (by
    show Discrete.mk (delta1 A) = F
    rw [hA])⟩⟩

theorem ft_h0 (X : CellComplex2) (K : Type) [AddCommGroup K]
    (hF : (fieldStrength (X := X) (K := K)).Faithful) : H0Vanishes X K := by
  intro lam hlam
  let A : PotG X K := ⟨0⟩
  let f : A ⟶ A := ⟨lam, by simp [A, hlam]⟩
  have h := (fieldStrength (X := X) (K := K)).map_injective
    (X := A) (Y := A) (a₁ := f) (a₂ := 𝟙 A) (Subsingleton.elim _ _)
  exact congrArg GaugeHom.lam h

theorem ft_H1 : H1Vanishes filledTriangle ℤ := by
  intro A hA
  have h := congrFun hA 0
  simp [delta1, Fin.sum_univ_three] at h
  refine ⟨![0, A 0, A 0 + A 1], ?_⟩
  funext e
  fin_cases e <;> simp [delta0, Fin.sum_univ_three] <;> omega

theorem ft_H2 : H2Vanishes filledTriangle ℤ := by
  intro F
  refine ⟨![F 0, 0, 0], ?_⟩
  funext p
  fin_cases p
  simp [delta1, Fin.sum_univ_three]

theorem ft_not_H0 : ¬ H0Vanishes filledTriangle ℤ := by
  intro h
  have h1 := congrFun (h (fun _ => 1) (by
    funext e; fin_cases e <;> simp [delta0, Fin.sum_univ_three])) 0
  simp at h1

theorem ft_main :
    (fieldStrength (X := filledTriangle) (K := ℤ)).Full ∧
    (fieldStrength (X := filledTriangle) (K := ℤ)).EssSurj ∧
    ¬ (fieldStrength (X := filledTriangle) (K := ℤ)).Faithful :=
  ⟨ft_full _ _ ft_H1, ft_es _ _ ft_H2, fun hF => ft_not_H0 (ft_h0 _ _ hF)⟩

end WeatherallGauge

open WeatherallGauge CategoryTheory

theorem solution :
    (fieldStrength (X := filledTriangle) (K := ℤ)).Full ∧
    (fieldStrength (X := filledTriangle) (K := ℤ)).EssSurj ∧
    ¬ (fieldStrength (X := filledTriangle) (K := ℤ)).Faithful := ft_main
