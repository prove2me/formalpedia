-- Prove2me | solution 1 for Polynomial.Monic.eq_of_forall_norm_resultant_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:46:28.037506+00:00
-- url     : https://prove2.me/submissions/c3dc1207-7277-4776-a4f0-0409c9686a69

import Mathlib

/-!
# Monic polynomials over an ultrametric field are determined by their resultant norms

Over a nontrivially normed field `K` with an ultrametric norm, monic `P, Q` with `‖Res(P, G)‖ = ‖Res(Q, G)‖`
for every `G ∈ K[X]` are equal. For a monic irreducible `φ` with `P = φ^d P₁`, `φ ∤ P₁`, one has
`‖Res(P, φ + c)‖ = ‖c‖^(d deg φ) · ‖Res(P₁, φ)‖` for all small `c` (the factor `Res(P₁, φ + c)` is a polynomial
in `c`, nonzero at `0`, so its norm is locally constant by the ultrametric inequality). Comparing `c` and `c²`
reads off `d`, so `P` and `Q` have the same normalized factors, hence are associated, hence equal.
-/

set_option autoImplicit false

namespace RamanujanPetersson.JacAlgResSol

open Polynomial UniqueFactorizationMonoid

/-- For monic `P` the resultant `Res(P, G, deg P, n)` does not depend on `n ≥ deg G`. -/
lemma resultant_monic_eq {R : Type*} [CommRing R] {P G : R[X]} (hP : P.Monic) {n : ℕ} (hn : G.natDegree ≤ n) :
    resultant P G P.natDegree n = resultant P G := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg P G P.natDegree G.natDegree k le_rfl, hP.coeff_natDegree, one_pow,
    one_mul]

section Field

variable {K : Type*} [Field K]

/-- `Res(φ, φ + c) = c ^ deg φ` for monic `φ`. -/
lemma resultant_self_add_C {φ : K[X]} (hφ : φ.Monic) (c : K) :
    resultant φ (φ + C c) φ.natDegree φ.natDegree = c ^ φ.natDegree := by
  have h := resultant_add_mul_right φ (C c) 1 φ.natDegree φ.natDegree (by simp) le_rfl
  rw [mul_one, add_comm] at h
  rw [h, resultant_C_right, hφ.coeff_natDegree, one_pow, one_mul]

lemma count_normalizedFactors_of_decomp [DecidableEq K] {φ P c : K[X]} {d : ℕ} (hirr : Irreducible φ)
    (hnorm : normalize φ = φ) (hP : P = φ ^ d * c) (hc : ¬ φ ∣ c) :
    (normalizedFactors P).count φ = d := by
  refine count_normalizedFactors_eq hirr hnorm (hP ▸ dvd_mul_right _ _) ?_
  intro h
  rw [hP, pow_succ] at h
  exact hc ((mul_dvd_mul_iff_left (pow_ne_zero _ hirr.ne_zero)).mp h)

end Field

section Ultra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Near `c = 0`: `‖Res(P, φ + c)‖ = ‖c‖ ^ (deg φ · d) · A` with `A > 0`, when `P = φ^d P₁` and `φ ∤ P₁`. -/
lemma exists_norm_resultant_add_C {P φ P₁ : K[X]} {d : ℕ} (hP : P.Monic) (hφ : φ.Monic)
    (hirr : Irreducible φ) (hdec : P = φ ^ d * P₁) (hnd : ¬ φ ∣ P₁) :
    ∃ A > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ c : K, ‖c‖ < δ →
      ‖resultant P (φ + C c)‖ = ‖c‖ ^ (φ.natDegree * d) * A := by
  have hP₁ : P₁.Monic := (hφ.pow d).of_mul_monic_left (hdec ▸ hP)
  -- the resultant `Res(P₁, φ + c)` as a polynomial in `c`
  obtain ⟨R, hR⟩ : ∃ R : K[X], R = resultant (P₁.map C) (φ.map C + C X) P₁.natDegree φ.natDegree :=
    ⟨_, rfl⟩
  have hev : ∀ c : K, R.eval c = resultant P₁ (φ + C c) P₁.natDegree φ.natDegree := by
    intro c
    rw [hR, ← coe_evalRingHom, ← resultant_map_map]
    congr 1
    · ext i; simp [coeff_map]
    · ext i; simp [coeff_map, Polynomial.map_map]
  have hR0 : R.eval 0 ≠ 0 := by
    rw [hev, map_zero, add_zero]
    exact resultant_ne_zero P₁ φ ((hirr.coprime_iff_not_dvd).mpr hnd).symm
  have hA : 0 < ‖R.eval 0‖ := norm_pos_iff.mpr hR0
  obtain ⟨δ, hδ, hcont⟩ :=
    Metric.continuousAt_iff.mp (R.continuous.continuousAt : ContinuousAt (fun x => R.eval x) 0) _ hA
  refine ⟨‖R.eval 0‖, hA, δ, hδ, fun c hc => ?_⟩
  have hnear : ‖R.eval c‖ = ‖R.eval 0‖ := by
    have h1 : ‖R.eval c - R.eval 0‖ < ‖R.eval 0‖ := by
      rw [← dist_eq_norm]; exact hcont (by rwa [dist_zero_right])
    have h2 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h1.ne
    rw [sub_add_cancel] at h2
    rw [h2, max_eq_right h1.le]
  have hdeg : P.natDegree = (φ ^ d).natDegree + P₁.natDegree := by
    rw [hdec, (hφ.pow d).natDegree_mul hP₁]
  have hG : (φ + C c).natDegree ≤ φ.natDegree := by rw [natDegree_add_C]
  have hsplit : resultant P (φ + C c) = (c ^ φ.natDegree) ^ d * R.eval c := by
    rw [← resultant_monic_eq hP hG, hdeg]
    conv_lhs => rw [hdec]
    rw [resultant_mul_left _ _ _ _ hG,
      resultant_pow_left φ (φ + C c) d φ.natDegree (by simp [hφ.leadingCoeff]) hG,
      resultant_self_add_C hφ, ← hev]
  rw [hsplit, norm_mul, hnear, norm_pow, norm_pow, ← pow_mul]

/-- **Milne Lemma 10.21 (resultant form).** Monic polynomials over an ultrametric nontrivially normed field
with `‖Res(P, G)‖ = ‖Res(Q, G)‖` for all `G` are equal. -/
theorem eq_of_norm_resultant_eq {P Q : K[X]} (hP : P.Monic) (hQ : Q.Monic)
    (H : ∀ G : K[X], ‖resultant P G‖ = ‖resultant Q G‖) : P = Q := by
  classical
  -- equal multiplicity of every monic irreducible factor
  have key : ∀ φ : K[X], φ.Monic → Irreducible φ → ∀ (d e : ℕ) (P₁ Q₁ : K[X]), P = φ ^ d * P₁ →
      ¬ φ ∣ P₁ → Q = φ ^ e * Q₁ → ¬ φ ∣ Q₁ → d = e := by
    intro φ hφ hirr d e P₁ Q₁ hPd hP₁ hQe hQ₁
    obtain ⟨A, hA, δ, hδ, hPn⟩ := exists_norm_resultant_add_C hP hφ hirr hPd hP₁
    obtain ⟨B, hB, δ', hδ', hQn⟩ := exists_norm_resultant_add_C hQ hφ hirr hQe hQ₁
    obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt K (lt_min (lt_min hδ hδ') one_pos)
    have hc1 : ‖c‖ < 1 := hc.trans_le (min_le_right _ _)
    have hcδ : ‖c‖ < δ := hc.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hcδ' : ‖c‖ < δ' := hc.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hc2 : ‖c ^ 2‖ ≤ ‖c‖ := by
      rw [norm_pow, sq]; exact mul_le_of_le_one_left hc0.le hc1.le
    have h1 := H (φ + C c)
    rw [hPn c hcδ, hQn c hcδ'] at h1
    have h2 := H (φ + C (c ^ 2))
    rw [hPn _ (hc2.trans_lt hcδ), hQn _ (hc2.trans_lt hcδ'), norm_pow, ← pow_mul, ← pow_mul] at h2
    set x := ‖c‖
    set a := φ.natDegree * d
    set b := φ.natDegree * e
    -- h1 : x^a A = x^b B,  h2 : x^(2a) A = x^(2b) B
    have h3 : x ^ (2 * b) * B = x ^ (a + b) * B := by
      rw [← h2, two_mul, pow_add, mul_assoc, h1, ← mul_assoc, ← pow_add]
    have h4 : 2 * b = a + b := pow_right_injective₀ hc0 hc1.ne (mul_right_cancel₀ hB.ne' h3)
    have hab : a = b := by omega
    exact Nat.eq_of_mul_eq_mul_left (Irreducible.natDegree_pos hirr) hab
  -- equal normalized factors
  have hcount : ∀ φ ∈ normalizedFactors P ∪ normalizedFactors Q,
      (normalizedFactors P).count φ = (normalizedFactors Q).count φ := by
    intro φ hmem
    have hmem' : φ ∈ normalizedFactors P ∨ φ ∈ normalizedFactors Q := Multiset.mem_union.mp hmem
    have hirr : Irreducible φ := by
      rcases hmem' with h | h <;> exact irreducible_of_normalized_factor φ h
    have hnorm : normalize φ = φ := by
      rcases hmem' with h | h <;> exact normalize_normalized_factor φ h
    have hφ : φ.Monic := hnorm ▸ monic_normalize hirr.ne_zero
    have hfin : ∀ S : K[X], S ≠ 0 → FiniteMultiplicity φ S := fun S hS =>
      finiteMultiplicity_of_degree_pos_of_monic (degree_pos_of_irreducible hirr) hφ hS
    obtain ⟨P₁, hPd, hP₁⟩ := (hfin P hP.ne_zero).exists_eq_pow_mul_and_not_dvd
    obtain ⟨Q₁, hQe, hQ₁⟩ := (hfin Q hQ.ne_zero).exists_eq_pow_mul_and_not_dvd
    rw [count_normalizedFactors_of_decomp hirr hnorm hPd hP₁,
      count_normalizedFactors_of_decomp hirr hnorm hQe hQ₁]
    exact key φ hφ hirr _ _ P₁ Q₁ hPd hP₁ hQe hQ₁
  have hnf : normalizedFactors P = normalizedFactors Q := by
    ext φ
    by_cases hmem : φ ∈ normalizedFactors P ∪ normalizedFactors Q
    · exact hcount φ hmem
    · rw [Multiset.mem_union, not_or] at hmem
      rw [Multiset.count_eq_zero.mpr hmem.1, Multiset.count_eq_zero.mpr hmem.2]
  have hassoc : Associated P Q :=
    (prod_normalizedFactors hP.ne_zero).symm.trans (hnf ▸ prod_normalizedFactors hQ.ne_zero)
  exact eq_of_monic_of_associated hP hQ hassoc

end Ultra

end RamanujanPetersson.JacAlgResSol

theorem solution
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    {P Q : Polynomial K} (hP : P.Monic) (hQ : Q.Monic)
    (H : ∀ G : Polynomial K, ‖P.resultant G‖ = ‖Q.resultant G‖) : P = Q := by
  exact RamanujanPetersson.JacAlgResSol.eq_of_norm_resultant_eq hP hQ H
