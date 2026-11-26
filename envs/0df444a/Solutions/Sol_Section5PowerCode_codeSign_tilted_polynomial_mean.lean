-- Prove2me | solution 1 for Section5PowerCode.codeSign_tilted_polynomial_mean
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:48:09.632435+00:00
-- url     : https://prove2.me/submissions/76c5eb9a-f696-4371-9181-8ab4f445549f

import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5CodedPolynomialMoments
import Definitions.Def_Section5Verified_Section5PowerCodeCharacters
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
import Theorems.Thm_Section5PowerCode_codeSign_product_sum_zero
import Theorems.Thm_Section5SignMoments_polynomial_mean_match
section
set_option autoImplicit false

/-! Uniform seed characters of a finite-field power code. Every nonempty
product of at most `k` distinct output signs has exactly zero mean. -/

namespace Section5PowerCode

variable {F : Type*} [Field F] [Fintype F]









theorem codeSign_sq [CharP F 2] {ι : Type*} {k : ℕ}
    (χ : AddChar F ℝ) (v : ι → F) (t : Fin k → F) (i : ι) :
    codeSign χ v t i ^ 2=1 := by
  rw [codeSign,pow_two,← AddChar.map_add_eq_mul,CharTwo.add_self_eq_zero,
    AddChar.map_zero_eq_one]





end Section5PowerCode

end
section
set_option autoImplicit false

namespace Section5PowerCode

variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]

theorem codeSign_squarefree_mean {k : ℕ} (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (S : Finset ι) (hS : S.card ≤ k) :
    Section5SignMoments.mean (fun t : Fin k → F => ∏ i ∈ S, codeSign χ v t i)=
      if S=∅ then 1 else 0 := by
  by_cases he : S=∅
  · subst S
    simp [Section5SignMoments.mean]
  · rw [if_neg he]
    unfold Section5SignMoments.mean
    rw [codeSign_product_sum_zero χ hχ v hv S (Finset.nonempty_iff_ne_empty.mpr he) hS,
      mul_zero]

theorem codeSign_polynomial_mean {k : ℕ} (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v)
    (p : MvPolynomial ι ℝ) (hp : p.totalDegree ≤ k) :
    Section5SignMoments.mean (fun t : Fin k → F => MvPolynomial.eval (codeSign χ v t) p)=
      Section5SignMoments.mean (fun x : ι → Bool =>
        MvPolynomial.eval (Section5BooleanFrame.sign x) p) := by
  exact Section5SignMoments.polynomial_mean_match _
    (fun t i => codeSign_sq χ v t i) k (codeSign_squarefree_mean χ hχ v hv) p hp



theorem amplitudePolynomial_eval (w a : ι → ℝ) :
    MvPolynomial.eval a (amplitudePolynomial w)=∑ i, w i*a i := by
  simp [amplitudePolynomial]

theorem amplitudePolynomial_degree (w : ι → ℝ) :
    (amplitudePolynomial w).totalDegree ≤ 1 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)



end Section5PowerCode

end
set_option autoImplicit false
namespace Section5PowerCode
end Section5PowerCode
open Section5PowerCode
variable {F ι : Type*} [Field F] [Fintype F] [CharP F 2]
  [Fintype ι] [DecidableEq ι]
theorem solution {k : ℕ} (χ : AddChar F ℝ) (hχ : χ ≠ 0)
    (v : ι → F) (hv : Function.Injective v) (w : ι → ℝ)
    (p : MvPolynomial ι ℝ) (hp : p.totalDegree+2 ≤ k) :
    Section5SignMoments.mean (fun t : Fin k → F =>
      (∑ i, w i*Section5PowerCode.codeSign χ v t i)^2*MvPolynomial.eval (Section5PowerCode.codeSign χ v t) p)=
      Section5SignMoments.mean (fun x : ι → Bool =>
        (∑ i, w i*Section5BooleanFrame.sign x i)^2*
          MvPolynomial.eval (Section5BooleanFrame.sign x) p) := by
  have hdeg : ((Section5PowerCode.amplitudePolynomial w)^2*p).totalDegree ≤ k := by
    calc
      _ ≤ ((Section5PowerCode.amplitudePolynomial w)^2).totalDegree+p.totalDegree :=
        MvPolynomial.totalDegree_mul _ _
      _ ≤ 2*1+p.totalDegree := Nat.add_le_add_right
        ((MvPolynomial.totalDegree_pow _ _).trans
          (Nat.mul_le_mul_left 2 (Section5PowerCode.amplitudePolynomial_degree w))) _
      _ ≤ k := by omega
  simpa only [map_mul,map_pow,Section5PowerCode.amplitudePolynomial_eval] using
    Section5PowerCode.codeSign_polynomial_mean χ hχ v hv ((Section5PowerCode.amplitudePolynomial w)^2*p) hdeg
