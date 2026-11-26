-- Prove2me | solution 1 for Section5SignMoments.tensor_polynomial_mean_match
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:39:34.736797+00:00
-- url     : https://prove2.me/submissions/4aacb45c-febe-4dc3-8e3e-705783212c50

import Mathlib
section
set_option autoImplicit false

/-! Tensorization of exact weighted polynomial moments. The probability
weights need not be uniform, and no independence assertion is assumed in place
of the actual finite product law. -/

namespace Section5SignMoments

variable {ι J Ω Ξ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [Fintype Ω] [Fintype Ξ]

theorem tensor_monomial_factorization (a : Ω → ι → ℝ) (p : Ω → ℝ)
    (d : (J × ι) →₀ ℕ) :
    (∑ x : J → Ω, (∏ r, p (x r))*(∏ z, a (x z.1) z.2 ^ d z))=
      ∏ r, ∑ x : Ω, p x*(∏ i, a x i ^ d (r,i)) := by
  simp only [Fintype.prod_prod_type,← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun r : J => fun x : Ω =>
    p x*(∏ i, a x i ^ d (r,i)))).symm

theorem row_degree_le (d : (J × ι) →₀ ℕ) (r : J) :
    (∑ i, d (r,i)) ≤ d.sum (fun _ e => e) := by
  have he : d.sum (fun _ e => e)=∑ s : J, ∑ i : ι, d (s,i) := by
    rw [Finsupp.sum_fintype]
    · exact Fintype.sum_prod_type _
    · intro z
      rfl
  rw [he]
  exact Finset.single_le_sum (f := fun s : J => ∑ i : ι, d (s,i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ r)



end Section5SignMoments

end
set_option autoImplicit false
namespace Section5SignMoments
end Section5SignMoments
open Section5SignMoments
variable {ι J Ω Ξ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype J] [DecidableEq J] [Fintype Ω] [Fintype Ξ]
theorem solution (a : Ω → ι → ℝ) (b : Ξ → ι → ℝ)
    (pa : Ω → ℝ) (pb : Ξ → ℝ) (k : ℕ)
    (hm : ∀ d : ι →₀ ℕ, d.sum (fun _ e => e) ≤ k →
      (∑ x : Ω, pa x*(∏ i, a x i ^ d i))=
        ∑ y : Ξ, pb y*(∏ i, b y i ^ d i))
    (P : MvPolynomial (J × ι) ℝ) (hP : P.totalDegree ≤ k) :
    (∑ x : J → Ω, (∏ r, pa (x r))*MvPolynomial.eval (fun z => a (x z.1) z.2) P)=
      ∑ y : J → Ξ, (∏ r, pb (y r))*MvPolynomial.eval (fun z => b (y z.1) z.2) P := by
  have hexp (c : (J × ι) → ℝ) : MvPolynomial.eval c P=
      ∑ d ∈ P.support, P.coeff d*(∏ z, c z ^ d z) := by
    exact MvPolynomial.eval₂_eq' (RingHom.id ℝ) c P
  simp only [hexp,Finset.mul_sum]
  rw [Finset.sum_comm,Finset.sum_comm (s := Finset.univ)]
  apply Finset.sum_congr rfl
  intro d hd
  have hmono :
      (∑ x : J → Ω, (∏ r, pa (x r))*(∏ z, a (x z.1) z.2 ^ d z))=
        ∑ y : J → Ξ, (∏ r, pb (y r))*(∏ z, b (y z.1) z.2 ^ d z) := by
    rw [Section5SignMoments.tensor_monomial_factorization,Section5SignMoments.tensor_monomial_factorization]
    apply Finset.prod_congr rfl
    intro r _
    let dr : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => d (r,i))
    have hdr : dr.sum (fun _ e => e) ≤ k := by
      have he : dr.sum (fun _ e => e)=∑ i, d (r,i) := by
        rw [Finsupp.sum_fintype]
        · rfl
        · intro i
          rfl
      rw [he]
      exact (Section5SignMoments.row_degree_le d r).trans ((MvPolynomial.le_totalDegree hd).trans hP)
    exact hm dr hdr
  calc
    _ = P.coeff d*(∑ x : J → Ω, (∏ r, pa (x r))*(∏ z, a (x z.1) z.2 ^ d z)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [hmono,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
