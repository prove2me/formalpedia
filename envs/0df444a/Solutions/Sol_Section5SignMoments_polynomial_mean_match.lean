-- Prove2me | solution 1 for Section5SignMoments.polynomial_mean_match
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:44:34.329865+00:00
-- url     : https://prove2.me/submissions/340200ab-e171-4af4-9353-7bd6800c040d

import Definitions.Def_Section5Verified_Section5BooleanFrameMoments
import Definitions.Def_Section5Verified_Section5SignMomentTransfer
import Mathlib
section
set_option autoImplicit false

/-! Bounded squarefree sign moments determine the expectation of every
polynomial of bounded total degree. This is a finite-sum identity. -/

namespace Section5SignMoments

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]



theorem mean_finset_sum {κ : Type*} (S : Finset κ) (f : κ → Ω → ℝ) :
    mean (fun x => ∑ i ∈ S, f i x)=∑ i ∈ S, mean (f i) := by
  simp only [mean,Finset.mul_sum]
  exact Finset.sum_comm

theorem mean_smul (a : ℝ) (f : Ω → ℝ) : mean (fun x => a*f x)=a*mean f := by
  simp only [mean,← Finset.mul_sum]
  ring

theorem squarefree_full (S : Finset ι) :
    mean (fun x : ι → Bool => ∏ i ∈ S, Section5BooleanFrame.sign x i)=
      if S=∅ then 1 else 0 := by
  by_cases hs : S=∅
  · subst S
    exact Section5BooleanFrame.average_const 1
  · rw [if_neg hs]
    change Section5BooleanFrame.average _=0
    obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    apply Section5BooleanFrame.average_zero_of_flip i
    intro x
    rw [← Finset.mul_prod_erase S _ hi,← Finset.mul_prod_erase S _ hi,
      Section5BooleanFrame.sign_flip_same]
    have he : (∏ j ∈ S.erase i,
        Section5BooleanFrame.sign (Section5BooleanFrame.flip i x) j)=
        ∏ j ∈ S.erase i, Section5BooleanFrame.sign x j := by
      apply Finset.prod_congr rfl
      intro j hj
      exact Section5BooleanFrame.sign_flip_other x (Finset.ne_of_mem_erase hj)
    rw [he]
    ring

theorem pow_reduce (a : ℝ) (ha : a ^ 2=1) (n : ℕ) :
    a ^ n=if n % 2=1 then a else 1 := by
  have he : a ^ n=a ^ (n % 2) := by
    conv_lhs => rw [← Nat.mod_add_div n 2]
    rw [pow_add,pow_mul,ha,one_pow,mul_one]
  rw [he]
  have hm := Nat.mod_lt n (by decide : 0 < 2)
  by_cases h : n % 2=1
  · simp [h]
  · have h0 : n % 2=0 := by omega
    simp [h0]



theorem monomial_reduce (a : ι → ℝ) (ha : ∀ i, a i ^ 2=1) (d : ι →₀ ℕ) :
    (∏ i ∈ d.support, a i ^ d i)=∏ i ∈ oddSupport d, a i := by
  simp only [oddSupport,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i _
  exact pow_reduce (a i) (ha i) (d i)

theorem oddSupport_card_le (d : ι →₀ ℕ) : (oddSupport d).card ≤ d.sum (fun _ e => e) := by
  calc
    _ ≤ d.support.card := Finset.card_filter_le _ _
    _ = ∑ _ ∈ d.support, 1 := by simp
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    _ = _ := rfl

theorem monomial_mean_match (a : Ω → ι → ℝ) (ha : ∀ x i, a x i ^ 2=1) (k : ℕ)
    (hm : ∀ S : Finset ι, S.card ≤ k →
      mean (fun x => ∏ i ∈ S, a x i)=if S=∅ then 1 else 0)
    (d : ι →₀ ℕ) (hd : d.sum (fun _ e => e) ≤ k) :
    mean (fun x => ∏ i ∈ d.support, a x i ^ d i)=
      mean (fun x : ι → Bool => ∏ i ∈ d.support, Section5BooleanFrame.sign x i ^ d i) := by
  simp only [monomial_reduce _ (ha _),
    monomial_reduce _ (Section5BooleanFrame.sign_sq _)]
  rw [hm _ ((oddSupport_card_le d).trans hd),squarefree_full]



end Section5SignMoments

end
set_option autoImplicit false
namespace Section5SignMoments
end Section5SignMoments
open Section5SignMoments
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
theorem solution (a : Ω → ι → ℝ) (ha : ∀ x i, a x i ^ 2=1) (k : ℕ)
    (hm : ∀ S : Finset ι, S.card ≤ k →
      Section5SignMoments.mean (fun x => ∏ i ∈ S, a x i)=if S=∅ then 1 else 0)
    (p : MvPolynomial ι ℝ) (hp : p.totalDegree ≤ k) :
    Section5SignMoments.mean (fun x => MvPolynomial.eval (a x) p)=
      Section5SignMoments.mean (fun x : ι → Bool => MvPolynomial.eval (Section5BooleanFrame.sign x) p) := by
  have hexp (b : ι → ℝ) : MvPolynomial.eval b p=
      ∑ d ∈ p.support, p.coeff d*(∏ i ∈ d.support, b i ^ d i) := by
    exact MvPolynomial.eval₂_eq (RingHom.id ℝ) b p
  simp only [hexp,Section5SignMoments.mean_finset_sum,Section5SignMoments.mean_smul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Section5SignMoments.monomial_mean_match a ha k hm d ((MvPolynomial.le_totalDegree hd).trans hp)]
