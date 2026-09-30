-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_prefix_gcd_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T19:56:07.979234+00:00
-- url     : https://prove2.me/submissions/462550df-b16a-4afe-809e-672ed6a16a1e

import Theorems.Thm_WeierstrassEllipticZeta_triangular_canonical_polynomial_update
import Theorems.Thm_WeierstrassEllipticZeta_triangular_hypersurface_intersection_length
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section

open WeierstrassEllipticZeta

theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (r : Fin 3 → Polynomial ℂ) (hM : M.Monic)
    (hI : ∀ f : MvPolynomial (Fin 4) ℂ,
      f ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f)
    (p : ℕ → MvPolynomial (Fin 4) ℂ) :
    let G : ℕ → Polynomial ℂ := Nat.rec M (fun s g =>
      gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) (p s)))
    G 0 = M ∧
    (∀ s : ℕ, G (s + 1) = gcd (G s)
      (MvPolynomial.aeval (Fin.cons Polynomial.X r) (p s))) ∧
    ∀ s : ℕ,
      let J := I ⊔ Ideal.span (Set.range (fun i : Fin s => p i.val))
      (G s).Monic ∧ G s ∣ M ∧
      (∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ J ↔ G s ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f) ∧
      FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) = (G s).natDegree ∧
      G (s + 1) ∣ G s ∧ (G (s + 1)).natDegree ≤ (G s).natDegree ∧
      (G (s + 1) = G s ↔ p s ∈ J) ∧
      ((G (s + 1)).natDegree < (G s).natDegree ↔ p s ∉ J) ∧
      (Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸
          (I ⊔ Ideal.span (Set.range (fun i : Fin (s + 1) => p i.val)))) <
        Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J) ↔ p s ∉ J) := by
  classical
  let G : ℕ → Polynomial ℂ := Nat.rec M (fun s g =>
    gcd g (MvPolynomial.aeval (Fin.cons Polynomial.X r) (p s)))
  let J (s : ℕ) := I ⊔ Ideal.span (Set.range (fun i : Fin s => p i.val))
  have hJzero : J 0 = I := by simp [J]
  have hJsucc (s : ℕ) : J (s + 1) = J s ⊔ Ideal.span {p s} := by
    have hfun : (fun i : Fin (s + 1) => p i.val) =
        Fin.snoc (fun i : Fin s => p i.val) (p s) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
    dsimp only [J]
    rw [hfun, Fin.range_snoc, Ideal.span_insert]
    ac_rfl
  have hdata (s : ℕ) : (G s).Monic ∧ G s ∣ M ∧
      ∀ f : MvPolynomial (Fin 4) ℂ,
        f ∈ J s ↔ G s ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) f := by
    induction s with
    | zero =>
      refine ⟨hM, dvd_rfl, ?_⟩
      intro f
      rw [hJzero]
      exact hI f
    | succ s ih =>
      obtain ⟨hmonic, hdiv, hmem⟩ := ih
      obtain ⟨hmonic', hdiv', hmem', _⟩ :=
        triangular_canonical_polynomial_update (J s) (G s) r hmonic hmem (p s)
      refine ⟨hmonic', hdiv'.trans hdiv, ?_⟩
      intro f
      rw [hJsucc]
      exact hmem' f
  refine ⟨rfl, fun _ => rfl, ?_⟩
  intro s
  obtain ⟨hmonic, hdiv, hmem⟩ := hdata s
  obtain ⟨_, hfinite, hlength, _, _⟩ :=
    triangular_hypersurface_intersection_length (J s) (G s) r hmonic.ne_zero hmem 0
  change FiniteDimensional ℂ (MvPolynomial (Fin 4) ℂ ⧸ J s ⊔ Ideal.span {0}) at hfinite
  change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J s ⊔ Ideal.span {0}) =
    (gcd (G s) (MvPolynomial.aeval (Fin.cons Polynomial.X r) 0)).natDegree at hlength
  rw [Ideal.span_singleton_zero, sup_bot_eq] at hfinite hlength
  simp only [map_zero, gcd_zero_right, hmonic.normalize_eq_self] at hlength
  obtain ⟨_, hnextdiv, _, _, _, hnextdegree, hsame, hstrict, hdimension, _⟩ :=
    triangular_canonical_polynomial_update (J s) (G s) r hmonic hmem (p s)
  refine ⟨hmonic, hdiv, hmem, hfinite, hlength,
    hnextdiv, hnextdegree, hsame, hstrict, ?_⟩
  change Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J (s + 1)) <
    Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ J s) ↔ p s ∉ J s
  rw [hJsucc]
  exact hdimension

