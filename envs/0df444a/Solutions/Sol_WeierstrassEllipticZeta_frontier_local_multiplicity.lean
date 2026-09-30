-- Prove2me | solution 1 for WeierstrassEllipticZeta.frontier_local_multiplicity
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-12T22:38:18.304165+00:00
-- url     : https://prove2.me/submissions/8d42d4c9-b641-4f92-82e3-72aef8100c78

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.Analysis.Analytic.Polynomial
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

theorem solution
    (G : Frontier.Geometry) (m n U : ℕ) (X : Finset ℂ)
    (Q : MvPolynomial (Fin 7) ℂ)
    (hcharts : Frontier.HasChartCertificates G m n U X Q)
    (c : Fin 2) (z : ℂ)
    (hz : G.S (extensionChartDenominator c) z ≠ 0)
    (hupper : analyticOrderAt
      (fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
        (extensionChartNormalize c Q)) z < G.B (m + 2 * n)) :
    let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
      (extensionChartNormalize c Q)
    ∃! k : ℕ, k < G.B (m + 2 * n) ∧
      (z ∈ X + X + X → 3 * U + 1 ≤ k) ∧
      (∀ j < k, iteratedDeriv j f z = 0) ∧ iteratedDeriv k f z ≠ 0 ∧
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧
        f =ᶠ[𝓝 z] (fun w => (w - z) ^ k * g w) := by
  let f := fun w => MvPolynomial.eval (extensionChartCoordinates G.S c w)
    (extensionChartNormalize c Q)
  have ha (i : Fin 4) :
      AnalyticAt ℂ (fun w => extensionChartCoordinates G.S c w i) z := by
    fin_cases c <;> fin_cases i <;> simp [extensionChartCoordinates]
    all_goals first | exact analyticAt_id |
      exact (G.hS _ z (Set.mem_univ _)).div (G.hS _ z (Set.mem_univ _)) hz
  have hf : AnalyticAt ℂ f z :=
    AnalyticAt.aeval_mvPolynomial ha (extensionChartNormalize c Q)
  have hfinite : analyticOrderAt f z ≠ ⊤ := ne_top_of_lt hupper
  let k := analyticOrderNatAt f z
  have hkeq : analyticOrderAt f z = (k : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hfinite).symm
  have hklt : k < G.B (m + 2 * n) := by
    exact_mod_cast (hkeq ▸ hupper)
  have hderiv := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp hkeq
  refine ⟨k, ⟨hklt, ?_, hderiv.1, hderiv.2, ?_⟩, ?_⟩
  · intro hX
    let Z := (X + X + X).filter
      (fun z => G.S (extensionChartDenominator c) z ≠ 0)
    let V := Z.image (extensionChartCoordinates G.S c)
    have hzZ : z ∈ Z := Finset.mem_filter.mpr ⟨hX, hz⟩
    have hv : extensionChartCoordinates G.S c z ∈ V :=
      Finset.mem_image.mpr ⟨z, hzZ, rfl⟩
    have hc := hcharts c
    have hmem := (Submodule.mem_iInf _).mp hc.vanishing
      (⟨extensionChartCoordinates G.S c z, hv⟩ : V)
    have hcontact := G.hcontact.1 c (extensionChartCoordinates G.S c z)
      (3 * U + 1) (extensionChartNormalize c Q)
    have hjets := (G.hjets.2 c (extensionChartNormalize c Q) (3 * U + 1)).2 z hz
    have hlow : (3 * U + 1 : ℕ) ≤ analyticOrderAt f z :=
      hjets.2.mpr (hcontact.mp hmem)
    rw [hkeq] at hlow
    exact_mod_cast hlow
  · simpa only [smul_eq_mul, Filter.EventuallyEq, f] using
      hf.analyticOrderAt_eq_natCast.mp hkeq
  · intro l hl
    have hleq := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mpr
      ⟨hl.2.2.1, hl.2.2.2.1⟩
    exact_mod_cast hleq.symm.trans hkeq
