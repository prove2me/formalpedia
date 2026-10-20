-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.collinearityOrthogonalityObstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:34:11.050965+00:00
-- url     : https://prove2.me/submissions/d143ec53-acae-4358-b2be-30d01bf4a311

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_collinear_orth {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U W : V) (hU : U ≠ 0) (hW : W ≠ 0) (hc : Collinear U W) (ho : inner ℂ W U = 0) : False := by
  obtain ⟨a, b, hab, h⟩ := hc
  have h1 := congrArg (fun x => inner ℂ W x) h
  simp only [inner_add_right, inner_smul_right, ho, mul_zero, zero_add, inner_zero_right] at h1
  have hWW : inner ℂ W W ≠ 0 := inner_self_ne_zero.mpr hW
  have hb : b = 0 := by
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 hWW
  subst hb
  have ha : a ≠ 0 := by tauto
  rw [zero_smul, add_zero] at h
  exact hU ((smul_eq_zero.mp h).resolve_left ha)

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution {d : ℕ} (hd : 0 < d)
    (E : Fin d → ℝ) (beta : ℝ) (rho : Mat d) (hrho : IsDensityMatrix rho)
    (pf : ℝ → ℝ) (P : Matrix (Fin d) (Fin d) ℝ) (edges : TransferEdges d)
    (u v : Fin d × Fin d)
    (hrequires : ∀ (b : ℕ) (D : ThermalDilation E beta b),
      PopulationTask E rho pf (thermalApply D) →
      (∀ r i, population (thermalApply D) r i = P r i) →
      JointElementary (thermalApply D) edges →
      shellVector D u.1 u.2 ≠ 0 ∧ shellVector D v.1 v.2 ≠ 0 ∧
      Collinear (shellVector D u.1 u.2) (shellVector D v.1 v.2))
    (horthogonal : ∀ (b : ℕ) (D : ThermalDilation E beta b),
      PopulationTask E rho pf (thermalApply D) →
      (∀ r i, population (thermalApply D) r i = P r i) →
      inner ℂ (shellVector D v.1 v.2) (shellVector D u.1 u.2) = 0) :
    ¬ ∃ Phi : Map d, IsFiniteThermal E beta Phi ∧ PopulationTask E rho pf Phi ∧
      (∀ r i, population Phi r i = P r i) ∧ JointElementary Phi edges := by
  rintro ⟨Phi, ⟨b, D, hD⟩, hT, hP, hJ⟩
  have hPhi : Phi = thermalApply D := funext hD
  subst hPhi
  obtain ⟨hu, hv, hc⟩ := hrequires b D hT hP hJ
  exact g52c_collinear_orth _ _ hu hv hc (horthogonal b D hT hP)
