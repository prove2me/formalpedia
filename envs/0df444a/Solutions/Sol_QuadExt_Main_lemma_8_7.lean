-- Prove2me | solution 1 for QuadExt.Main.lemma_8_7
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T14:16:14.686326+00:00
-- url     : https://prove2.me/submissions/fe24b275-a9c5-4d8e-bd08-821263afe2c0

import Mathlib

open Polynomial

/-- If an element `p` divides every entry of the rows indexed by `S`, then `p ^ S.card`
divides the determinant. -/
lemma quadext_pow_card_dvd_det {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : R} {A : Matrix ι ι R} (S : Finset ι) (h : ∀ i ∈ S, ∀ j, p ∣ A i j) :
    p ^ S.card ∣ A.det := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply']
  simp only [Matrix.transpose_apply]
  refine Finset.dvd_sum fun σ _ => ?_
  refine dvd_mul_of_dvd_right ?_ _
  have h1 : p ^ S.card ∣ ∏ i ∈ S, A i (σ i) := by
    rw [← Finset.prod_const (s := S) (b := p)]
    refine Finset.prod_dvd_prod_of_dvd (s := S) (f := fun _ => p) (g := fun i => A i (σ i)) ?_
    intro i hi
    exact h i hi (σ i)
  refine h1.trans (Finset.prod_dvd_prod_of_subset S Finset.univ (fun i => A i (σ i)) ?_)
  exact Finset.subset_univ S

/-- If evaluating a polynomial matrix `P` at `β` drops the rank to `s`, then
`(X - β) ^ (k - s)` divides `det P`.  No hypothesis on `det P` is needed: if `det P = 0`
the claim is trivial. -/
lemma quadext_pow_dvd_det {F : Type*} [Field F] (k : ℕ)
    (P : Matrix (Fin k) (Fin k) F[X]) (β : F) :
    (X - C β) ^ (k - (P.map (fun q => q.eval β)).rank) ∣ P.det := by
  classical
  set M : Matrix (Fin k) (Fin k) F := P.map (fun q => q.eval β) with hM
  obtain ⟨V, U, e, hV, hU, hVU⟩ := Matrix.exists_rank_normal_form M
  set Q : Matrix (Fin k) (Fin k) F[X] := (V.map C) * P * (U.map C) with hQ
  have hQmap1 : Q.map (fun q => q.eval β) = V * M * U := by
    rw [hQ]
    simp only [hM]
    ext i j
    simp [Matrix.mul_apply, Matrix.map_apply, Polynomial.eval_finsetSum]
  have hQmap : Q.map (fun q => q.eval β) = (Matrix.fromBlocks 1 0 0 0).submatrix e e :=
    hQmap1.trans hVU
  set Q' : Matrix (Fin M.rank ⊕ Fin (Fintype.card (Fin k) - M.rank))
      (Fin M.rank ⊕ Fin (Fintype.card (Fin k) - M.rank)) F[X] :=
    Q.submatrix e.symm e.symm with hQ'
  have hQ'map : Q'.map (fun q => q.eval β) = Matrix.fromBlocks 1 0 0 0 := by
    rw [hQ', ← Matrix.submatrix_map, hQmap, Matrix.submatrix_submatrix]
    simp
  have hdetQ' : Q'.det = Q.det := by
    rw [hQ']
    exact Matrix.det_submatrix_equiv_self e.symm Q
  have hdivQ' : (X - C β) ^ (Fintype.card (Fin k) - M.rank) ∣ Q'.det := by
    let S : Finset (Fin M.rank ⊕ Fin (Fintype.card (Fin k) - M.rank)) :=
      Finset.univ.image (Sum.inr : Fin (Fintype.card (Fin k) - M.rank) →
        Fin M.rank ⊕ Fin (Fintype.card (Fin k) - M.rank))
    have hS : (X - C β) ^ S.card ∣ Q'.det := by
      refine quadext_pow_card_dvd_det S ?_
      intro i hi j
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hi
      rw [← ha]
      have hzero : (Q' (Sum.inr a) j).eval β = 0 := by
        have h1 := congr_fun (congr_fun hQ'map (Sum.inr a)) j
        cases j with
        | inl j => simpa using h1
        | inr j => simpa using h1
      exact Polynomial.dvd_iff_isRoot.mpr (Polynomial.IsRoot.def.mpr hzero)
    have hcard : S.card = Fintype.card (Fin k) - M.rank := by
      simp only [S]
      rw [Finset.card_image_of_injective _ Sum.inr_injective]
      simp
    rwa [hcard] at hS
  have hdivQ : (X - C β) ^ (Fintype.card (Fin k) - M.rank) ∣ Q.det := by
    rwa [hdetQ'] at hdivQ'
  have hdetV : (V.map C).det = Polynomial.C V.det :=
    (RingHom.map_det (Polynomial.C : F →+* F[X]) V).symm
  have hdetU : (U.map C).det = Polynomial.C U.det :=
    (RingHom.map_det (Polynomial.C : F →+* F[X]) U).symm
  have hdetQ : Q.det = Polynomial.C (V.det * U.det) * P.det := by
    rw [hQ, Matrix.det_mul, Matrix.det_mul, hdetV, hdetU, Polynomial.C_mul]
    ring
  have hVne : V.det ≠ 0 := by
    have h1 : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
    rwa [isUnit_iff_ne_zero] at h1
  have hUne : U.det ≠ 0 := by
    have h1 : IsUnit U.det := (Matrix.isUnit_iff_isUnit_det U).mp hU
    rwa [isUnit_iff_ne_zero] at h1
  have hCunit : IsUnit (Polynomial.C (V.det * U.det) : F[X]) := by
    rw [Polynomial.isUnit_C]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero hVne hUne)
  have hdivP : (X - C β) ^ (Fintype.card (Fin k) - M.rank) ∣ P.det := by
    rw [hdetQ] at hdivQ
    obtain ⟨w, hw⟩ := hdivQ
    obtain ⟨u, hu⟩ := hCunit
    refine ⟨(↑u⁻¹ : F[X]) * w, ?_⟩
    rw [← hu] at hw
    calc P.det = (↑u⁻¹ : F[X]) * ((u : F[X]) * P.det) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = (↑u⁻¹ : F[X]) * ((X - C β) ^ (Fintype.card (Fin k) - M.rank) * w) := by rw [hw]
      _ = (X - C β) ^ (Fintype.card (Fin k) - M.rank) * ((↑u⁻¹ : F[X]) * w) := by ring
  simpa [hM] using hdivP

theorem solution {F : Type} [Field F] (k r : ℕ) (P : Matrix (Fin k) (Fin k) F[X])
    (hP : P.det ≠ 0) (β : F) (hrank : (P.map fun q => q.eval β).rank ≤ r) :
    (k : ℤ) - r ≤ (P.det.rootMultiplicity β : ℤ) := by
  classical
  by_cases hrk : r ≤ k
  · have hle : k - r ≤ k - (P.map (fun q => q.eval β)).rank :=
      Nat.sub_le_sub_left hrank k
    have hdvd : (X - C β) ^ (k - r) ∣ P.det :=
      (pow_dvd_pow (X - C β) hle).trans (quadext_pow_dvd_det k P β)
    have hrm : k - r ≤ P.det.rootMultiplicity β :=
      (Polynomial.le_rootMultiplicity_iff hP).mpr hdvd
    have hcast : ((k - r : ℕ) : ℤ) = (k : ℤ) - r := by omega
    rw [← hcast]
    exact_mod_cast hrm
  · have h1 : (k : ℤ) - r ≤ 0 := by omega
    have h2 : (0 : ℤ) ≤ (P.det.rootMultiplicity β : ℤ) := by exact_mod_cast Nat.zero_le _
    linarith
