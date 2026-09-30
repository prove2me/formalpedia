-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_anchor_fundamental_domain
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T15:03:29.46559+00:00
-- url     : https://prove2.me/submissions/ea461b77-946b-4f5c-97d9-4bd7d2af2a9b

import Definitions.Def_WeierstrassEllipticZeta_FiniteAnchorCandidates
import Theorems.Thm_WeierstrassEllipticZeta_finite_elementary_locus_vanishing
import Theorems.Thm_WeierstrassEllipticZeta_elliptic_extension_projective_descent
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Tactic

noncomputable section
open scoped Classical
open TranscendenceTheory
namespace WeierstrassEllipticZeta

private def restrictionPoly (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![1, T, Polynomial.C (S 0 b), Polynomial.C (S 1 b), Polynomial.C (S 2 b),
      Polynomial.C (S 3 b) + U * Polynomial.C (S 0 b),
      Polynomial.C (S 4 b) + U * Polynomial.C (S 2 b)] Q

private lemma restriction_eval (S : Fin 5 → ℂ → ℂ) (b : ℂ)
    (T U : Polynomial ℂ) (Q : MvPolynomial (Fin 7) ℂ) (s : ℂ) :
    (restrictionPoly S b T U Q).eval s =
      MvPolynomial.eval ![1, T.eval s, S 0 b, S 1 b, S 2 b,
        S 3 b + U.eval s * S 0 b, S 4 b + U.eval s * S 2 b] Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [restrictionPoly]
  | add P Q hP hQ => simp_all [restrictionPoly, map_add]
  | mul_X P i hP =>
    simp only [restrictionPoly, map_mul, MvPolynomial.eval₂Hom_X] at *
    rw [Polynomial.eval_mul, hP]
    congr 1
    fin_cases i <;> simp

private def locusValue (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (w : Fin 3 → ℂ) : ℂ :=
  MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
    S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q

private lemma anchor_slice_eval (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (b α t β : ℂ) :
    (anchorSlice S Q b α t).eval β = locusValue S Q ![t, b, α * t + β] := by
  change (restrictionPoly S b (Polynomial.C t)
    (Polynomial.C (α * t) + Polynomial.X) Q).eval β = _
  rw [restriction_eval]
  simp only [Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X]
  rfl

private lemma line_anchor_of_vanishing (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b α β : ℂ)
    (hp : anchorObstruction S Q m b α ≠ 0)
    (hz : ∀ t : ℂ, locusValue S Q ![t, b, α * t + β] = 0) :
    β ∈ lineAnchorRoots S Q m n b α := by
  refine Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots hp).mpr ?_), ?_⟩
  · change (anchorObstruction S Q m b α).eval β = 0
    unfold anchorObstruction
    split_ifs with h
    · rw [anchor_slice_eval]
      exact hz _
    · simp
  · rintro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    simpa [locusValue, add_comm] using hz j

private lemma fibre_values_of_samples (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ)
    (hz : ∀ w ∈ elementaryLocusSamples .fibre r m n, locusValue S Q w = 0) :
    ∀ t u : ℂ, locusValue S Q ![t, r 1, u] = 0 := by
  have hall := ((finite_elementary_locus_vanishing S Q m n hQ .fibre r).2.2).mpr hz
  intro t u
  have hv := hall (r + ![t - r 0, 0, u - r 2])
    ⟨![t - r 0, 0, u - r 2], by simp [elementaryDirections], rfl⟩
  simpa [locusValue] using hv

private lemma line_values_of_samples (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ) (α : ℂ)
    (hz : ∀ w ∈ elementaryLocusSamples (.line α) r m n, locusValue S Q w = 0) :
    ∀ t : ℂ, locusValue S Q ![t, r 1, α * t + (r 2 - α * r 0)] = 0 := by
  have hall := ((finite_elementary_locus_vanishing S Q m n hQ (.line α) r).2.2).mpr hz
  intro t
  have heq : r + ![t - r 0, 0, α * (t - r 0)] =
      ![t, r 1, α * t + (r 2 - α * r 0)] := by
    ext i
    fin_cases i <;> simp <;> ring
  exact heq ▸ hall (r + ![t - r 0, 0, α * (t - r 0)])
    ⟨![t - r 0, 0, α * (t - r 0)], by simp [elementaryDirections], rfl⟩

private lemma fibre_choice_of_values (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ) (b : ℂ)
    (hz : ∀ t u : ℂ, locusValue S Q ![t, b, u] = 0) :
    () ∈ fibreAnchorChoices S Q m n b := by
  refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
  rintro w hw
  obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hw
  simpa [locusValue] using hz ij.1 ij.2


private lemma obstruction_zero_iff (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m : ℕ) (b α : ℂ) :
    anchorObstruction S Q m b α = 0 ↔
      ∀ j : ℕ, j ≤ m → anchorSlice S Q b α j = 0 := by
  unfold anchorObstruction
  split_ifs with h
  · constructor
    · intro hz
      exact False.elim ((Nat.find_spec h).2 hz)
    · intro hz
      exact False.elim ((Nat.find_spec h).2 (hz _ (Nat.find_spec h).1))
  · simp only [true_iff]
    intro j hj
    by_contra hn
    exact h ⟨j, hj, hn⟩

private lemma last_block_scaling (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (x : Fin 7 → ℂ) (r : ℂ) :
    MvPolynomial.eval ![x 0, x 1, r*x 2, r*x 3, r*x 4, r*x 5, r*x 6] Q =
      r^n * MvPolynomial.eval x Q := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

private def extVector (S : Fin 5 → ℂ → ℂ) (b u : ℂ) : Fin 5 → ℂ :=
  ![S 0 b, S 1 b, S 2 b, S 3 b + u * S 0 b, S 4 b + u * S 2 b]

private lemma value_period_zero (L : PeriodPair) (S : Fin 5 → ℂ → ℂ)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (P : GraphQuotientExtension L.lattice η → Projectivization ℂ (Fin 5 → ℂ))
    (hP : ∀ b u : ℂ, ∃ hv : extVector S b u ≠ 0,
      P ((extensionPeriodGraph L.lattice η).mkQ (b, u)) =
        Projectivization.mk ℂ (extVector S b u) hv)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (t b u : ℂ) (ω : L.lattice) :
    locusValue S Q ![t, b - ω, u + η ω] = 0 ↔
      locusValue S Q ![t, b, u] = 0 := by
  have heq : (extensionPeriodGraph L.lattice η).mkQ (b, u) =
      (extensionPeriodGraph L.lattice η).mkQ (b - ω, u + η ω) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    refine ⟨ω, ?_⟩
    ext <;> simp
  obtain ⟨hv, hvP⟩ := hP b u
  obtain ⟨hw, hwP⟩ := hP (b - ω) (u + η ω)
  have hproj := hwP.symm.trans ((congrArg P heq.symm).trans hvP)
  obtain ⟨r, hr⟩ := (Projectivization.mk_eq_mk_iff ℂ _ _ hw hv).mp hproj
  have hcoords (i : Fin 5) := congrFun hr i
  simp only [extVector, Pi.smul_apply, Units.smul_def, smul_eq_mul] at hcoords
  have hvec :
      ![1, t, S 0 (b - ω), S 1 (b - ω), S 2 (b - ω),
        S 3 (b - ω) + (u + η ω) * S 0 (b - ω),
        S 4 (b - ω) + (u + η ω) * S 2 (b - ω)] =
      ![1, t, (r:ℂ)*S 0 b, (r:ℂ)*S 1 b, (r:ℂ)*S 2 b,
        (r:ℂ)*(S 3 b + u * S 0 b), (r:ℂ)*(S 4 b + u * S 2 b)] := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact (hcoords 0).symm
    · exact (hcoords 1).symm
    · exact (hcoords 2).symm
    · exact (hcoords 3).symm
    · exact (hcoords 4).symm
  change MvPolynomial.eval
    ![1, t, S 0 (b - ω), S 1 (b - ω), S 2 (b - ω),
      S 3 (b - ω) + (u + η ω) * S 0 (b - ω),
      S 4 (b - ω) + (u + η ω) * S 2 (b - ω)] Q = 0 ↔
    MvPolynomial.eval ![1, t, S 0 b, S 1 b, S 2 b,
      S 3 b + u * S 0 b, S 4 b + u * S 2 b] Q = 0
  rw [hvec]
  have hs := last_block_scaling Q n hQ
    ![1, t, S 0 b, S 1 b, S 2 b, S 3 b + u * S 0 b, S 4 b + u * S 2 b] (r:ℂ)
  change MvPolynomial.eval ![1, t, (r:ℂ)*S 0 b, (r:ℂ)*S 1 b, (r:ℂ)*S 2 b,
    (r:ℂ)*(S 3 b + u * S 0 b), (r:ℂ)*(S 4 b + u * S 2 b)] Q =
    (r:ℂ)^n * MvPolynomial.eval
      ![1, t, S 0 b, S 1 b, S 2 b, S 3 b + u * S 0 b, S 4 b + u * S 2 b] Q at hs
  rw [hs]
  simp [Units.ne_zero r]

private lemma transport_anchor (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ)
    (X : Finset ℂ) (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (b b' ξ : ℂ)
    (hcov : ∀ t u : ℂ, locusValue S Q ![t, b', u + ξ] = 0 ↔
      locusValue S Q ![t, b, u] = 0)
    (a : FiniteAnchorCandidate Λ η X S Q m n b) :
    ∃ a' : FiniteAnchorCandidate Λ η X S Q m n b',
      anchorCandidateLocus Λ η X S Q m n b' a' =
        anchorCandidateLocus Λ η X S Q m n b a := by
  rcases a with a | a
  · exact ⟨.inl (), rfl⟩
  rcases a with a | ⟨p, β⟩
  · have hv := fibre_values_of_samples S Q m n hQ ![0, b, 0]
      (Finset.mem_filter.mp a.property).2
    have hn : () ∈ fibreAnchorChoices S Q m n b' := by
      apply fibre_choice_of_values
      intro t u
      have he := (hcov t (u - ξ)).mpr (hv t (u - ξ))
      simpa using he
    exact ⟨.inr (.inl ⟨(), hn⟩), rfl⟩
  · let α := periodPairSlope Λ η X p
    have hb := Finset.mem_filter.mp β.property
    have hv := line_values_of_samples S Q m n hQ ![0, b, β.val] α hb.2
    have hold : anchorObstruction S Q m b α ≠ 0 :=
      Polynomial.ne_zero_of_mem_roots (Multiset.mem_toFinset.mp hb.1)
    have hn : anchorObstruction S Q m b' α ≠ 0 := by
      intro hz
      apply hold
      apply (obstruction_zero_iff S Q m b α).mpr
      intro j hj
      apply Polynomial.funext
      intro γ
      have hslice := (obstruction_zero_iff S Q m b' α).mp hz j hj
      have he := congrArg (fun f : Polynomial ℂ => f.eval (γ + ξ)) hslice
      rw [anchor_slice_eval] at he
      simp only [Polynomial.eval_zero] at he
      have he' : locusValue S Q ![(j:ℂ), b', (α * j + γ) + ξ] = 0 := by
        simpa only [add_assoc] using he
      simpa only [anchor_slice_eval, Polynomial.eval_zero] using
        (hcov j (α * j + γ)).mp he'
    have hroot : β.val + ξ ∈ lineAnchorRoots S Q m n b' α := by
      apply line_anchor_of_vanishing S Q m n b' α (β.val + ξ) hn
      intro t
      have he := (hcov t (α * t + β.val)).mpr (by simpa using hv t)
      simpa only [add_assoc] using he
    exact ⟨.inr (.inr ⟨p, ⟨β.val + ξ, hroot⟩⟩), rfl⟩


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair) (D : EllipticSigmaDifferentialData L)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hS_value : ∀ z : ℂ, z ∉ L.lattice → ∀ j : Fin 5,
      S j z = D.sigma z ^ 3 * ![1, L.weierstrassP z, L.derivWeierstrassP z,
        weierstrassZeta L z,
        L.derivWeierstrassP z * weierstrassZeta L z + 2 * L.weierstrassP z ^ 2] j)
    (hS_ne : ∀ z : ℂ, ∃ j : Fin 5, S j z ≠ 0)
    (η : L.lattice →ₗ[ℤ] ℂ)
    (hη : ∀ ω : L.lattice, η ω = zetaQuasiPeriod L ω)
    (X : Finset ℂ) (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) :
    IsCompact (L.basis.parallelepiped : Set ℂ) ∧
      ∀ P : FiniteLocusCandidate L.lattice X → Prop,
        (∃ (b : ℂ) (a : FiniteAnchorCandidate L.lattice η X S Q m n b),
          P (anchorCandidateLocus L.lattice η X S Q m n b a)) ↔
        (∃ b : ℂ, b ∈ L.basis.parallelepiped ∧ ‖b‖ ≤ ‖L.ω₁‖ + ‖L.ω₂‖ ∧
          ∃ a : FiniteAnchorCandidate L.lattice η X S Q m n b,
            P (anchorCandidateLocus L.lattice η X S Q m n b a)) := by
  classical
  refine ⟨L.basis.parallelepiped.isCompact, ?_⟩
  intro H
  constructor
  · rintro ⟨b, a, ha⟩
    let ω : L.lattice := ⟨ZSpan.floor L.basis b, by
      rw [L.lattice_eq_span_range_basis]
      exact (ZSpan.floor L.basis b).property⟩
    let b' := ZSpan.fract L.basis b
    obtain ⟨P, hP, _⟩ := elliptic_extension_projective_descent L D S
      hS hS_value hS_ne η hη
    have hcov (t u : ℂ) : locusValue S Q ![t, b', u + η ω] = 0 ↔
        locusValue S Q ![t, b, u] = 0 :=
      value_period_zero L S η P hP Q n (fun d hd => (hQ d hd).2) t b u ω
    obtain ⟨a', heq⟩ := transport_anchor L.lattice η X S Q m n hQ b b' (η ω) hcov a
    refine ⟨b', ?_, ?_, a', ?_⟩
    · exact ZSpan.fundamentalDomain_subset_parallelepiped L.basis
        (ZSpan.fract_mem_fundamentalDomain L.basis b)
    · simpa [Fin.sum_univ_two] using ZSpan.norm_fract_le L.basis b
    · rw [heq]
      exact ha
  · rintro ⟨b, _, _, a, ha⟩
    exact ⟨b, a, ha⟩
