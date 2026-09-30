-- Prove2me | solution 1 for WeierstrassEllipticZeta.wp_contact_minpoly_generator
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T02:43:19.422355+00:00
-- url     : https://prove2.me/submissions/71d7330d-09a2-4c11-85f0-f44e510c9eb1

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Analysis.Analytic.Polynomial

noncomputable section
open WeierstrassEllipticZeta
open scoped Pointwise Classical Topology

private lemma sigma_nonzero (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) :
    G.D.sigma z ≠ 0 := by
  intro hzero
  obtain ⟨j, hj⟩ := G.hS_ne z
  rw [G.hS_value z hz j, hzero, zero_pow (by decide), zero_mul] at hj
  exact hj rfl

private lemma chart_zero_nonzero (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) :
    G.S (extensionChartDenominator 0) z ≠ 0 := by
  simp only [extensionChartDenominator, ↓reduceIte]
  rw [G.hS_value z hz 0]
  simpa using pow_ne_zero 3 (sigma_nonzero G z hz)

private lemma chart_wp_value (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) :
    extensionChartCoordinates G.S 0 z 1 = G.L.weierstrassP z := by
  simp only [extensionChartCoordinates, ↓reduceIte, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  rw [G.hS_value z hz 1, G.hS_value z hz 0]
  simp [sigma_nonzero G z hz]

private lemma wp_contact_iff (G : Frontier.Geometry) (Y : Finset ℂ) (N : ℕ)
    (q : Polynomial ℂ) :
    let Z := Y.filter (fun z => z ∉ G.L.lattice)
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
        (extensionChartCoordinates G.S 0 z.val) N
    Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) q ∈ I ↔
      ∀ z ∈ Y, z ∉ G.L.lattice → ∀ j < N,
        iteratedDeriv j (fun w => q.eval (G.L.weierstrassP w)) z = 0 := by
  dsimp only
  rw [Ideal.mem_iInf]
  have hjets (z : ℂ) (hz : z ∉ G.L.lattice) (j : ℕ) :
      MvPolynomial.eval (extensionChartCoordinates G.S 0 z)
          ((extensionChartDerivation G.L.g₂ G.L.g₃ 0)^[j]
            (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) q)) =
        iteratedDeriv j (fun w => q.eval (G.L.weierstrassP w)) z := by
    rw [← ((G.hjets.2 0 (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) q) j).2
      z (chart_zero_nonzero G z hz)).1]
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [G.L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    calc
      _ = Polynomial.aeval
          ((MvPolynomial.aeval (extensionChartCoordinates G.S 0 w))
            (MvPolynomial.X (1 : Fin 4))) q :=
        (Polynomial.aeval_algHom_apply
          (MvPolynomial.aeval (extensionChartCoordinates G.S 0 w)) _ q).symm
      _ = _ := by simp [chart_wp_value G w hw]
  constructor
  · intro h z hz hzl j hj
    have hv := (G.hcontact.1 0 (extensionChartCoordinates G.S 0 z) N
      (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) q)).mp
        (h ⟨z, Finset.mem_filter.mpr ⟨hz, hzl⟩⟩) j hj
    rwa [hjets z hzl j] at hv
  · intro h z
    apply (G.hcontact.1 0 (extensionChartCoordinates G.S 0 z.val) N
      (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) q)).mpr
    intro j hj
    have hz := Finset.mem_filter.mp z.property
    rw [hjets z.val hz.2 j]
    exact h z.val hz.1 hz.2 j hj

private lemma subset_contact_finite (G : Frontier.Geometry) (m n U : ℕ)
    (X : Finset ℂ) (Q : MvPolynomial (Fin 7) ℂ) (hX : 0 ∈ X)
    (hcharts : Frontier.HasChartCertificates G m n U X Q)
    (Y : Finset ℂ) (hYX : Y ⊆ X) :
    let Z := Y.filter (fun z => z ∉ G.L.lattice)
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
        (extensionChartCoordinates G.S 0 z.val) (3 * U + 1)
    FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) := by
  let Z := Y.filter (fun z => z ∉ G.L.lattice)
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
      (extensionChartCoordinates G.S 0 z.val) (3 * U + 1)
  let W := (X + X + X).filter (fun z => G.S (extensionChartDenominator 0) z ≠ 0)
  let V := W.image (extensionChartCoordinates G.S 0)
  let J : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ v : V, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0 v.val (3 * U + 1)
  have hJI : J ≤ I := by
    intro f hf
    apply Ideal.mem_iInf.mpr
    intro z
    have hz := Finset.mem_filter.mp z.property
    have hz3 : z.val ∈ X + X + X := by
      simpa using Finset.add_mem_add (Finset.add_mem_add (hYX hz.1) hX) hX
    have hzW : z.val ∈ W := Finset.mem_filter.mpr
      ⟨hz3, chart_zero_nonzero G z.val hz.2⟩
    have hzV : extensionChartCoordinates G.S 0 z.val ∈ V :=
      Finset.mem_image.mpr ⟨z.val, hzW, rfl⟩
    exact Ideal.mem_iInf.mp hf ⟨_, hzV⟩
  let : FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) := (hcharts 0).finite
  let f := Ideal.quotientMapₐ I (AlgHom.id ℂ (MvPolynomial (Fin 4) ℂ))
    (show J ≤ I.comap (AlgHom.id ℂ (MvPolynomial (Fin 4) ℂ)) from hJI)
  exact FiniteDimensional.of_surjective f.toLinearMap
    (Ideal.quotientMap_surjective (H := hJI) Function.surjective_id)

/-- The contact conditions on elliptic values form a principal polynomial ideal;
its monic generator has degree equal to the dimension of the coordinate subalgebra. -/
theorem solution
    (G : Frontier.Geometry) (m n U : ℕ) (X : Finset ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (hX : 0 ∈ X)
    (hcharts : Frontier.HasChartCertificates G m n U X Q)
    (Y : Finset ℂ) (hYX : Y ⊆ X) :
    let Z := Y.filter (fun z => z ∉ G.L.lattice)
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
        (extensionChartCoordinates G.S 0 z.val) (3 * U + 1)
    let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
    ∃ p : Polynomial ℂ, p.Monic ∧
      p.natDegree = Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set _)) ∧
      ∀ q : Polynomial ℂ, p ∣ q ↔ ∀ z ∈ Y, z ∉ G.L.lattice → ∀ j < 3 * U + 1,
        iteratedDeriv j (fun w => q.eval (G.L.weierstrassP w)) z = 0 := by
  let Z := Y.filter (fun z => z ∉ G.L.lattice)
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
      (extensionChartCoordinates G.S 0 z.val) (3 * U + 1)
  let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
  let := subset_contact_finite G m n U X Q hX hcharts Y hYX
  have hx : IsIntegral ℂ x := IsIntegral.of_finite ℂ x
  refine ⟨minpoly ℂ x, minpoly.monic hx, ?_, ?_⟩
  · exact (Algebra.adjoin.powerBasis hx).finrank.symm
  · intro q
    rw [minpoly.dvd_iff]
    have heval : Polynomial.aeval x q =
        Ideal.Quotient.mk I (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) q) :=
      Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ ℂ I) _ q
    rw [heval, Ideal.Quotient.eq_zero_iff_mem]
    exact wp_contact_iff G Y (3 * U + 1) q
