-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P18.fixedMarginalComparison
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:59:28.328224+00:00
-- url     : https://prove2.me/submissions/78440a10-5299-4fb2-a0fc-90e546b68cf2

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
    (∀ (sigma : Matrix (A × B) (A × B) ℂ) (a : Matrix A A ℂ),
      sigma.PosSemidef → QAlgorithms.IsDensityMatrix a → correlationGauge sigma ≤ betaA sigma a) ∧
    (∀ (sigma : Matrix (A × B) (A × B) ℂ) (b : Matrix B B ℂ),
      sigma.PosSemidef → QAlgorithms.IsDensityMatrix b → correlationGauge sigma ≤ betaB sigma b) ∧
    (∀ rho : Matrix (A × B) (A × B) ℂ, QAlgorithms.IsDensityMatrix rho →
      capitalGamma D rho ≤ min (upsilonA D rho) (upsilonB D rho)) := by
  refine ⟨fun sigma a _ _ => h54d_gauge_le_betaA _ _, fun sigma b _ _ => h54d_gauge_le_betaB _ _,
    fun rho _ => le_min ?_ ?_⟩
  · unfold capitalGamma upsilonA
    apply sInf_le_sInf
    rintro r ⟨sigma, hs, hb, rfl⟩
    exact ⟨sigma, hs, (h54d_gauge_le_betaA _ _).trans hb, rfl⟩
  · unfold capitalGamma upsilonB
    apply sInf_le_sInf
    rintro r ⟨sigma, hs, hb, rfl⟩
    exact ⟨sigma, hs, (h54d_gauge_le_betaB _ _).trans hb, rfl⟩

end
