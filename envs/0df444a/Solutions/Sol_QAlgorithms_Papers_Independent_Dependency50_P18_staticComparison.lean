-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.staticComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:59:21.832136+00:00
-- url     : https://prove2.me/submissions/470e2a1b-f6f7-400e-8094-9bb44e55307b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P18

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P18

open scoped BigOperators ComplexOrder

attribute [local instance] Classical.propDecidable

variable {A B C E X : Type}
  [Fintype A] [Fintype B] [Fintype C] [Fintype E] [Fintype X]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq E] [DecidableEq X]
  [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty E] [Nonempty X]


lemma h54d_gauge_le_betaA {A B : Type} [Fintype A] [Fintype B]
    (sigma : Matrix (A × B) (A × B) ℂ) (a : Matrix A A ℂ) :
    correlationGauge sigma ≤ betaA sigma a := by
  unfold correlationGauge betaA
  apply sInf_le_sInf
  rintro r ⟨l, v, hf, rfl⟩
  exact ⟨a, l, v, hf, rfl⟩

lemma h54d_gauge_le_betaB {A B : Type} [Fintype A] [Fintype B]
    (sigma : Matrix (A × B) (A × B) ℂ) (b : Matrix B B ℂ) :
    correlationGauge sigma ≤ betaB sigma b := by
  unfold correlationGauge betaB
  apply sInf_le_sInf
  rintro r ⟨k, v, hf, rfl⟩
  exact ⟨k, b, v, hf, rfl⟩

theorem solution (D : Divergence) (hD : IsGeneralizedDivergence D) :
    (∀ sigma : Matrix (A × B) (A × B) ℂ, sigma.PosSemidef → correlationGauge sigma ≤ staticBeta sigma) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho ≤ staticUpsilon D rho) := by
  refine ⟨fun sigma _ => h54d_gauge_le_betaA _ _, fun rho _ => ?_⟩
  unfold capitalGamma staticUpsilon
  apply sInf_le_sInf
  rintro r ⟨sigma, hs, hb, rfl⟩
  exact ⟨sigma, hs, (h54d_gauge_le_betaA _ _).trans hb, rfl⟩

end
