-- Prove2me | solution 1 for WeierstrassEllipticZeta.wp_contact_dimension_bound
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T20:54:53.844891+00:00
-- url     : https://prove2.me/submissions/2ee34878-578d-40be-9905-b9d8ac38ce13

import Definitions.Def_WeierstrassEllipticZeta_InterfaceGeometry
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

noncomputable section
open WeierstrassEllipticZeta
open scoped Classical

private lemma sigma_nonzero (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) :
    G.D.sigma z ≠ 0 := by
  intro hzero
  obtain ⟨j, hj⟩ := G.hS_ne z
  rw [G.hS_value z hz j, hzero, zero_pow (by decide), zero_mul] at hj
  exact hj rfl

private lemma chart_wp_value (G : Frontier.Geometry) (z : ℂ) (hz : z ∉ G.L.lattice) :
    extensionChartCoordinates G.S 0 z 1 = G.L.weierstrassP z := by
  simp only [extensionChartCoordinates, ↓reduceIte, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  rw [G.hS_value z hz 1, G.hS_value z hz 0]
  simp [sigma_nonzero G z hz]

private lemma wp_eq_of_period_class_eq (G : Frontier.Geometry) (z w : ℂ)
    (h : G.L.lattice.mkQ z = G.L.lattice.mkQ w) :
    G.L.weierstrassP z = G.L.weierstrassP w := by
  have hmem : z - w ∈ G.L.lattice := (Submodule.Quotient.eq G.L.lattice).mp h
  simpa using G.L.weierstrassP_add_coe w ⟨z - w, hmem⟩

private lemma wp_image_card_le (G : Frontier.Geometry) (Y : Finset ℂ) :
    (Y.image G.L.weierstrassP).card ≤ (G.L.lattice.mkQ '' (Y : Set ℂ)).ncard := by
  let T := Y.image G.L.lattice.mkQ
  have hrep (a : T) : ∃ z ∈ Y, G.L.lattice.mkQ z = a.val :=
    Finset.mem_image.mp a.property
  choose r hrY hr using hrep
  have hsub : Y.image G.L.weierstrassP ⊆
      Finset.univ.image (fun a : T => G.L.weierstrassP (r a)) := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hv
    let a : T := ⟨G.L.lattice.mkQ z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _,
      wp_eq_of_period_class_eq G (r a) z (hr a)⟩
  calc
    _ ≤ (Finset.univ.image (fun a : T => G.L.weierstrassP (r a))).card :=
      Finset.card_le_card hsub
    _ ≤ T.card := by
      simpa using Finset.card_image_le
        (s := Finset.univ) (f := fun a : T => G.L.weierstrassP (r a))
    _ = _ := by rw [← Finset.coe_image, Set.ncard_coe_finset]

/-- Repeated elliptic values share one factor in an annihilating polynomial for
the elliptic coordinate in a finite contact quotient. -/
theorem solution
    (G : Frontier.Geometry) (Y : Finset ℂ) (N : ℕ) :
    let Z := Y.filter (fun z => z ∉ G.L.lattice)
    let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
      ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
        (extensionChartCoordinates G.S 0 z.val) N
    let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
    IsIntegral ℂ x ∧
      Module.finrank ℂ (Algebra.adjoin ℂ ({x} : Set _)) ≤
        N * (Z.image G.L.weierstrassP).card ∧
      N * (Z.image G.L.weierstrassP).card ≤
        N * (G.L.lattice.mkQ '' (Y : Set ℂ)).ncard := by
  let Z := Y.filter (fun z => z ∉ G.L.lattice)
  let I : Ideal (MvPolynomial (Fin 4) ℂ) :=
    ⨅ z : Z, extensionChartContactIdeal G.L.g₂ G.L.g₃ 0
      (extensionChartCoordinates G.S 0 z.val) N
  let x := Ideal.Quotient.mk I (MvPolynomial.X (1 : Fin 4))
  let V := Z.image G.L.weierstrassP
  let q : Polynomial ℂ := ∏ a ∈ V, (Polynomial.X - Polynomial.C a)
  have hq : q.Monic := Polynomial.monic_prod_of_monic _ _
    (fun a _ => Polynomial.monic_X_sub_C a)
  have hdegree : (q ^ N).natDegree = N * V.card := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_prod_of_monic _ _
      (fun a _ => Polynomial.monic_X_sub_C a)]
    simp
  have hmem : Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) (q ^ N) ∈ I := by
    apply Ideal.mem_iInf.mpr
    intro z
    have hz := Finset.mem_filter.mp z.property
    have hroot : Polynomial.aeval
        (extensionChartCoordinates G.S 0 z.val 1) q = 0 := by
      rw [chart_wp_value G z.val hz.2]
      simp only [q, map_prod, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply]
      exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩)
        (sub_self _)
    have hk : Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) q ∈
        RingHom.ker (MvPolynomial.eval (extensionChartCoordinates G.S 0 z.val)) := by
      rw [RingHom.mem_ker]
      change (MvPolynomial.aeval (extensionChartCoordinates G.S 0 z.val))
        (Polynomial.aeval (MvPolynomial.X (1 : Fin 4)) q) = 0
      rw [← Polynomial.aeval_algHom_apply]
      simpa using hroot
    rw [map_pow]
    exact G.hcontact.2.2.1 0 (extensionChartCoordinates G.S 0 z.val) N
      (Ideal.pow_mem_pow hk N)
  have hzero : Polynomial.aeval x (q ^ N) = 0 := by
    change Polynomial.aeval ((Ideal.Quotient.mkₐ ℂ I)
      (MvPolynomial.X (1 : Fin 4))) (q ^ N) = 0
    rw [Polynomial.aeval_algHom_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hx : IsIntegral ℂ x := ⟨q ^ N, hq.pow N, hzero⟩
  refine ⟨hx, ?_, ?_⟩
  · calc
      _ = (minpoly ℂ x).natDegree := (Algebra.adjoin.powerBasis hx).finrank
      _ ≤ (q ^ N).natDegree := Polynomial.natDegree_le_of_dvd
        (minpoly.dvd_iff.mpr hzero) (hq.pow N).ne_zero
      _ = _ := hdegree
  · apply Nat.mul_le_mul_left
    exact (Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))).trans
      (wp_image_card_le G Y)
