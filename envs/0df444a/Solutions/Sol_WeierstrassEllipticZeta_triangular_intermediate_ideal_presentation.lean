-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_intermediate_ideal_presentation
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T12:39:28.806658+00:00
-- url     : https://prove2.me/submissions/db2bb664-82c3-4b43-99e5-ccd36765ba29

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.MonicSpan
import Mathlib.RingTheory.AdjoinRoot

noncomputable section


theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ J : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ J →
      ∃ g : Polynomial ℂ,
        g.Monic ∧ g ∣ M ∧ g.natDegree ≤ M.natDegree ∧
        J = I ⊔ Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) g} ∧
        (∀ f : MvPolynomial (Fin 4) ℂ,
          f ∈ J ↔ g ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
        FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = g.natDegree ∧
        (∀ h : Polynomial ℂ, h.Monic →
          (∀ f : MvPolynomial (Fin 4) ℂ,
            f ∈ J ↔ h ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) → h = g) := by
  classical
  intro J hIJ
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hsection : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hE (q : Polynomial ℂ) : φ (E q) = q := AlgHom.congr_fun hsection q
  have hsurj : Function.Surjective φ := fun q => ⟨E q, hE q⟩
  have hcomapI : I = Ideal.comap φ.toRingHom (Ideal.span {M}) := by
    ext f
    simpa only [Ideal.mem_comap, Ideal.mem_span_singleton, φ] using! hI f
  have hmapI : Ideal.map φ.toRingHom I = Ideal.span {M} := by
    rw [hcomapI]
    exact Ideal.map_comap_of_surjective _ hsurj _
  have hker : RingHom.ker φ.toRingHom ≤ I := by
    rw [hcomapI]
    exact Ideal.ker_le_comap _
  let K := Ideal.map φ.toRingHom J
  have hMK : M ∈ K := by
    apply Ideal.map_mono hIJ
    rw [hmapI]
    exact Ideal.subset_span (Set.mem_singleton M)
  have hK : K ≠ ⊥ := by
    intro h
    exact hM (by simpa only [h, Ideal.mem_bot] using hMK)
  obtain ⟨g, hg, hKg⟩ := Polynomial.exists_monic_span K hK
  have hgdvd : g ∣ M := Ideal.mem_span_singleton.mp (hKg ▸ hMK)
  have hcomapJ : J = Ideal.comap φ.toRingHom (Ideal.span {g}) := by
    rw [← hKg]
    exact ((Ideal.comap_map_of_surjective' φ.toRingHom hsurj J).trans
      (sup_of_le_left (hker.trans hIJ))).symm
  have hmem : ∀ f : MvPolynomial (Fin 4) ℂ, f ∈ J ↔ g ∣ φ f := by
    intro f
    rw [hcomapJ, Ideal.mem_comap, Ideal.mem_span_singleton]
    rfl
  have hgen : J = I ⊔ Ideal.span {E g} := by
    apply le_antisymm
    · intro f hf
      obtain ⟨s, hs⟩ := (hmem f).mp hf
      have hrem : f - E g * E s ∈ I := by
        apply (hI _).mpr
        change M ∣ φ (f - E g * E s)
        rw [map_sub, map_mul, hE, hE, hs, sub_self]
        exact dvd_zero M
      have hIle : I ≤ I ⊔ Ideal.span {E g} := le_sup_left
      have hgle : Ideal.span {E g} ≤ I ⊔ Ideal.span {E g} := le_sup_right
      have hmul : E g * E s ∈ I ⊔ Ideal.span {E g} :=
        hgle (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton (E g))))
      simpa only [sub_add_cancel] using (I ⊔ Ideal.span {E g}).add_mem (hIle hrem) hmul
    · apply sup_le hIJ
      apply Ideal.span_le.mpr
      intro f hf
      obtain rfl := Set.mem_singleton_iff.mp hf
      exact (hmem _).mpr (by rw [hE])
  let ψ := (Ideal.Quotient.mkₐ ℂ (Ideal.span {g})).comp φ
  have hsurjψ : Function.Surjective ψ := (Ideal.Quotient.mkₐ_surjective ℂ _).comp hsurj
  have hkerψ : RingHom.ker ψ.toRingHom = J := by
    ext f
    change Ideal.Quotient.mk (Ideal.span {g}) (φ f) = 0 ↔ f ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact (hmem f).symm
  let e : (MvPolynomial (Fin 4) ℂ ⧸ J) ≃ₐ[ℂ] (Polynomial ℂ ⧸ Ideal.span {g}) :=
    (Ideal.quotientEquivAlgOfEq ℂ hkerψ.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective hsurjψ)
  have : FiniteDimensional ℂ (Polynomial ℂ ⧸ Ideal.span {g}) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hg.ne_zero).basis
  refine ⟨g, hg, hgdvd, Polynomial.natDegree_le_of_dvd hgdvd hM, hgen, hmem,
    FiniteDimensional.of_injective e.toLinearMap e.injective, ?_, ?_⟩
  · rw [e.toLinearEquiv.finrank_eq, finrank_quotient_span_eq_natDegree]
  · intro h hh hother
    have hhmem : ∀ f : MvPolynomial (Fin 4) ℂ, f ∈ J ↔ h ∣ φ f := hother
    have hhg : h ∣ g := by
      have := (hhmem (E g)).mp ((hmem _).mpr (by rw [hE]))
      simpa only [hE] using this
    have hgh : g ∣ h := by
      have := (hmem (E h)).mp ((hhmem _).mpr (by rw [hE]))
      simpa only [hE] using this
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hg hh hgh
      (Polynomial.natDegree_le_of_dvd hhg hg.ne_zero)

