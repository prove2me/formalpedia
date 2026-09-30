-- Prove2me | solution 1 for WeierstrassEllipticZeta.admissible_contact_weight
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T00:45:44.619676+00:00
-- url     : https://prove2.me/submissions/0b57eab1-7ae7-40ac-b0a7-677d14ed2ecb

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry

noncomputable section
open WeierstrassEllipticZeta TranscendenceTheory
open scoped Pointwise Classical

private lemma weight_chart_cover (G : Frontier.Geometry) (z : ℂ) :
    ∃ c : Fin 2, G.S (extensionChartDenominator c) z ≠ 0 := by
  obtain ⟨hv, hp⟩ := G.hP z 0
  have hc := (G.P ((extensionPeriodGraph G.L.lattice G.η).mkQ (z, 0))).property
  rw [hp] at hc
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ _ hv
  rw [← ha] at hc
  rcases hc with h0 | h2
  · refine ⟨0, ?_⟩
    intro hs
    have hz : G.S 0 z = 0 := by simpa [extensionChartDenominator] using hs
    simp [hz] at h0
  · refine ⟨1, ?_⟩
    intro hs
    have hz : G.S 2 z = 0 := by simpa [extensionChartDenominator] using hs
    simp [hz] at h2

theorem solution
    (G : Frontier.Geometry) (m n U : ℕ) (X : Finset ℂ) (hX : 0 ∈ X)
    (Q : MvPolynomial (Fin 7) ℂ) (hcharts : Frontier.HasChartCertificates G m n U X Q) :
    3 * U + 1 < G.B (m + 2 * n) ∧ U ≤ (G.B (m + 2 * n) - 2) / 3 := by
  classical
  obtain ⟨c, hc⟩ := weight_chart_cover G 0
  have hzero : (0 : ℂ) ∈ X + X + X := by
    simpa using Finset.add_mem_add (Finset.add_mem_add hX hX) hX
  let Z := (X + X + X).filter (fun z => G.S (extensionChartDenominator c) z ≠ 0)
  let V := Z.image (extensionChartCoordinates G.S c)
  have hpoint : extensionChartCoordinates G.S c 0 ∈ V :=
    Finset.mem_image.mpr ⟨0, Finset.mem_filter.mpr ⟨hzero, hc⟩, rfl⟩
  have hcert := hcharts c
  obtain ⟨r, hr⟩ := hcert.polynomial.triangular
  obtain ⟨t, ht, _⟩ := hr.orders
  have h := ht ⟨extensionChartCoordinates G.S c 0, hpoint⟩
  have hbound : 3 * U + 1 < G.B (m + 2 * n) := lt_of_le_of_lt h.1 h.2.1
  exact ⟨hbound, by omega⟩
