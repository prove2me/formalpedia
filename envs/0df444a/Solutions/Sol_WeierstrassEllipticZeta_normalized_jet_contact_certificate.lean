-- Prove2me | solution 1 for WeierstrassEllipticZeta.normalized_jet_contact_certificate
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T21:59:12.205333+00:00
-- url     : https://prove2.me/submissions/2d6c13ab-a2cc-473f-bc91-e2fce76a92ce

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry

open WeierstrassEllipticZeta
open scoped Pointwise Classical

theorem solution
    (G : Frontier.Geometry) (m n U : ℕ) (X : Finset ℂ) (hX : 0 ∈ X)
    (Q : MvPolynomial (Fin 7) ℂ)
    (hcharts : Frontier.HasChartCertificates G m n U X Q)
    (c : Fin 2) (k : ℕ) (hk : k ≤ 2 * U) :
    (∀ z ∈ X, G.S (extensionChartDenominator c) z ≠ 0 →
      (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k] (extensionChartNormalize c Q) ∈
        extensionChartContactIdeal G.L.g₂ G.L.g₃ c
          (extensionChartCoordinates G.S c z) (U + 1)) ∧
    ((∃ z ∈ X, G.S (extensionChartDenominator c) z ≠ 0) →
      (extensionChartDerivation G.L.g₂ G.L.g₃ c)^[k]
        (extensionChartNormalize c Q) ≠ 0) := by
  classical
  let D := extensionChartDerivation G.L.g₂ G.L.g₃ c
  let q := extensionChartNormalize c Q
  have horder (z : ℂ) (hzX : z ∈ X)
      (hz : G.S (extensionChartDenominator c) z ≠ 0) :
      ∃ t : ℕ, 3 * U + 1 ≤ t ∧
        MvPolynomial.eval (extensionChartCoordinates G.S c z) (D^[t] q) ≠ 0 ∧
        ∀ j < t, MvPolynomial.eval (extensionChartCoordinates G.S c z) (D^[j] q) = 0 := by
    have htriple : z ∈ X + X + X := by
      simpa using Finset.add_mem_add (Finset.add_mem_add hzX hX) hX
    let Z := (X + X + X).filter
      (fun z => G.S (extensionChartDenominator c) z ≠ 0)
    let V := Z.image (extensionChartCoordinates G.S c)
    have hv : extensionChartCoordinates G.S c z ∈ V :=
      Finset.mem_image.mpr ⟨z, Finset.mem_filter.mpr ⟨htriple, hz⟩, rfl⟩
    obtain ⟨r, hr⟩ := (hcharts c).polynomial.triangular
    obtain ⟨t, ht, _⟩ := hr.orders
    let v : V := ⟨extensionChartCoordinates G.S c z, hv⟩
    have hvorder := ht v
    exact ⟨t v, hvorder.1, hvorder.2.2.1, hvorder.2.2.2⟩
  constructor
  · intro z hzX hz
    obtain ⟨t, ht, _, hzero⟩ := horder z hzX hz
    apply (G.hcontact.1 c (extensionChartCoordinates G.S c z) (U + 1) (D^[k] q)).mpr
    intro j hj
    rw [← Function.iterate_add_apply]
    exact hzero (j + k) (by omega)
  · rintro ⟨z, hzX, hz⟩ hzero
    obtain ⟨t, ht, hnonzero, _⟩ := horder z hzX hz
    have hkt : k ≤ t := by omega
    have hiterzero (r : ℕ) : D^[r] (0 : MvPolynomial (Fin 4) ℂ) = 0 := by
      induction r with
      | zero => rfl
      | succ r ih => rw [Function.iterate_succ_apply', ih, map_zero]
    apply hnonzero
    rw [← Nat.sub_add_cancel hkt, Function.iterate_add_apply]
    rw [hzero, hiterzero, map_zero]
