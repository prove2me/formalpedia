-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_degree_uniform_jet_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T20:38:12.978298+00:00
-- url     : https://prove2.me/submissions/32949132-0906-4ad7-bd65-26d802554182

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic.FinCases

noncomputable section
open MvPolynomial
open WeierstrassEllipticZeta

private lemma finite_polynomial_family_test {σ : Type*} [Finite σ]
    (p : ℕ → MvPolynomial σ ℂ) :
    ∃ N : ℕ, 0 < N ∧ ∀ v : σ → ℂ,
      (∀ k < N, eval v (p k) = 0) → ∀ k, eval v (p k) = 0 := by
  let J : ℕ →o Ideal (MvPolynomial σ ℂ) :=
    ⟨fun n => Ideal.span (p '' Set.Iio n), fun _ _ h =>
      Ideal.span_mono (Set.image_mono (fun _ hi => lt_of_lt_of_le hi h))⟩
  obtain ⟨N, hN⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) J
  refine ⟨N + 1, by omega, ?_⟩
  intro v hv k
  have hle : J (N + 1) ≤ RingHom.ker (eval v) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    exact hv i hi
  apply hle
  rw [← hN (N + 1) (by omega), hN (max (N + 1) (k + 1)) (by omega)]
  exact Ideal.subset_span ⟨k, by simp only [Set.mem_Iio]; omega, rfl⟩

private lemma linear_sequence_uniform_degree_test
    (T : ℕ → Module.End ℂ (MvPolynomial (Fin 4) ℂ)) (d : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∀ p : MvPolynomial (Fin 4) ℂ, p.totalDegree ≤ d →
      ∀ v : Fin 4 → ℂ, (∀ k < N, eval v (T k p) = 0) → ∀ k, eval v (T k p) = 0 := by
  classical
  let V := restrictTotalDegree (Fin 4) ℂ d
  let ι := Fin (Module.finrank ℂ V)
  let b : Module.Basis ι ℂ V := Module.finBasis ℂ V
  let q (k : ℕ) : MvPolynomial (ι ⊕ Fin 4) ℂ :=
    ∑ i : ι, X (Sum.inl i) * rename Sum.inr (T k (b i).val)
  obtain ⟨N, hNpos, hN⟩ := finite_polynomial_family_test q
  refine ⟨N, hNpos, ?_⟩
  intro p hp v hv
  let pV : V := ⟨p, (mem_restrictTotalDegree (Fin 4) d p).mpr hp⟩
  let a : ι → ℂ := fun i => b.repr pV i
  have hrepr : ∑ i : ι, a i • (b i).val = p := by
    simpa only [map_sum, map_smul, Submodule.subtype_apply] using
      congrArg V.subtype (b.sum_repr pV)
  have heval (k : ℕ) : eval (Sum.elim a v) (q k) = eval v (T k p) := by
    calc
      _ = ∑ i : ι, a i * eval v (T k (b i).val) := by
        simp [q, eval_rename, Function.comp_def]
      _ = eval v (T k (∑ i : ι, a i • (b i).val)) := by
        simp only [map_sum, map_smul]
        simp [smul_eq_C_mul]
      _ = eval v (T k p) := by rw [hrepr]
  intro k
  rw [← heval]
  exact hN (Sum.elim a v) (fun i hi => (heval i).trans (hv i hi)) k

theorem solution (g₂ g₃ : ℂ) :
    ∃ B : ℕ → ℕ, Monotone B ∧ (∀ d : ℕ, 0 < B d) ∧
      ∀ (d : ℕ) (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ), p.totalDegree ≤ d →
        ∀ v : Fin 4 → ℂ,
          ((∀ k < B d, eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0) ↔
            ∀ k : ℕ, eval v ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0) := by
  choose N hNpos hN using fun (c : Fin 2) (d : ℕ) =>
    linear_sequence_uniform_degree_test (fun k => (extensionChartDerivation g₂ g₃ c).toLinearMap ^ k) d
  let B (d : ℕ) := (Finset.range (d + 1)).sup (fun e => max (N 0 e) (N 1 e))
  have hNB (c : Fin 2) (d : ℕ) : N c d ≤ B d := by
    apply le_trans (b := max (N 0 d) (N 1 d))
    · fin_cases c <;> simp
    · exact Finset.le_sup (f := fun e => max (N 0 e) (N 1 e))
        (by simp : d ∈ Finset.range (d + 1))
  have hmono : Monotone B := fun _ _ h =>
    Finset.sup_mono (Finset.range_mono (Nat.add_le_add_right h 1))
  refine ⟨B, hmono, fun d => lt_of_lt_of_le (hNpos 0 d) (hNB 0 d), ?_⟩
  intro d c p hp v
  constructor
  · intro h k
    have htest := hN c d p hp v (fun i hi => ?_) k
    · simpa only [Module.End.pow_apply] using! htest
    · simpa only [Module.End.pow_apply] using! h i (lt_of_lt_of_le hi (hNB c d))
  · intro h k _
    exact h k

