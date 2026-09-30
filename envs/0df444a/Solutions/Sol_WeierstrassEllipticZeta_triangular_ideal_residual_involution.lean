-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_ideal_residual_involution
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T13:11:49.639748+00:00
-- url     : https://prove2.me/submissions/5249675b-339e-4a7f-8a50-c511b204a942

import Theorems.Thm_WeierstrassEllipticZeta_triangular_intermediate_ideal_presentation
import Theorems.Thm_WeierstrassEllipticZeta_triangular_residual_duality
import Theorems.Thm_WeierstrassEllipticZeta_triangular_residual_quotient_length

open scoped Classical

open WeierstrassEllipticZeta

theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M ≠ 0)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) :
    ∀ J : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ J →
      let R := I.colon (J : Set (MvPolynomial (Fin 4) ℂ))
      I ≤ R ∧
      I.colon (R : Set (MvPolynomial (Fin 4) ℂ)) = J ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ R) +
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree ∧
      (∀ K : Ideal (MvPolynomial (Fin 4) ℂ), I ≤ K →
        (J ≤ K ↔ I.colon (K : Set (MvPolynomial (Fin 4) ℂ)) ≤ R)) := by
  classical
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hsection : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hE (q : Polynomial ℂ) : φ (E q) = q := AlgHom.congr_fun hsection q
  have hdata (J : Ideal (MvPolynomial (Fin 4) ℂ)) (hIJ : I ≤ J) :
      I.colon ((I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) :
        Set (MvPolynomial (Fin 4) ℂ)) = J ∧
      FiniteDimensional ℂ
        (MvPolynomial (Fin 4) ℂ ⧸ I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) ∧
      Module.finrank ℂ
        (MvPolynomial (Fin 4) ℂ ⧸ I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) +
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = M.natDegree := by
    obtain ⟨g, hg, hgdvd, _, hgen, _, _, hlenJ, _⟩ :=
      triangular_intermediate_ideal_presentation I M r hM hI J hIJ
    obtain ⟨hinv, hcolon⟩ := triangular_residual_duality I M r hM hI (E g)
    have hR : I.colon (J : Set (MvPolynomial (Fin 4) ℂ)) = I.colon {E g} := by
      rw [hgen]
      exact hcolon
    obtain ⟨_, _, hfinR, _, hbalance⟩ :=
      triangular_residual_quotient_length I M r hM hI (E g)
    have hgcd : gcd M g = g := (gcd_eq_right_iff M g hg.normalize_eq_self).mpr hgdvd
    refine ⟨?_, ?_, ?_⟩
    · rw [hR]
      exact hinv.trans hgen.symm
    · rw [hR]
      exact hfinR
    · change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I.colon {E g}) +
          (gcd M (φ (E g))).natDegree = M.natDegree at hbalance
      rw [hE, hgcd] at hbalance
      rw [hR, hlenJ]
      exact hbalance
  intro J hIJ
  obtain ⟨hinv, hfin, hbalance⟩ := hdata J hIJ
  refine ⟨Ideal.le_colon, hinv, hfin, hbalance, ?_⟩
  intro K hIK
  constructor
  · intro hJK
    exact Submodule.colon_mono le_rfl hJK
  · intro hres
    calc
      J = I.colon ((I.colon (J : Set (MvPolynomial (Fin 4) ℂ))) :
          Set (MvPolynomial (Fin 4) ℂ)) := hinv.symm
      _ ≤ I.colon ((I.colon (K : Set (MvPolynomial (Fin 4) ℂ))) :
          Set (MvPolynomial (Fin 4) ℂ)) := Submodule.colon_mono le_rfl hres
      _ = K := (hdata K hIK).1

