-- Prove2me | solution 1 for ReciprocityTheory.PGsh.fischer_mul_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:11:16.883157+00:00
-- url     : https://prove2.me/submissions/278b385d-d8c8-43eb-8457-16ad45612ea6

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_FischerSmulRight
import Theorems.Thm_ReciprocityTheory_PGsh_fw_add_single
import Theorems.Thm_ReciprocityTheory_PGsh_fischer_add_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
open scoped Classical
namespace ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
private theorem fischer_eq_sum_of_support_subset (P Q : MvPolynomial (Fin ν × ι) ℂ)
    (S : Finset (Fin ν × ι →₀ ℕ)) (hS : Q.support ⊆ S) :
    fischer P Q = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
  have key : ∀ T : Finset (Fin ν × ι →₀ ℕ), Q.support ⊆ T →
      ∑ A ∈ T, coeff A P * starRingEnd ℂ (coeff A Q) * fw A
        = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
    intro T hT
    symm
    apply Finset.sum_subset hT
    intro A _ hA
    have h0 : coeff A Q = 0 := by simpa [MvPolynomial.mem_support_iff] using hA
    simp [h0]
  calc fischer P Q
      = ∑ A ∈ Q.support, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := by
        unfold fischer
        exact key _ (fun x hx => Finset.mem_union_right _ hx)
    _ = ∑ A ∈ S, coeff A P * starRingEnd ℂ (coeff A Q) * fw A := (key S hS).symm
private theorem fischer_monomial_right (P : MvPolynomial (Fin ν × ι) ℂ)
    (m : Fin ν × ι →₀ ℕ) (b : ℂ) :
    fischer P (monomial m b) = coeff m P * starRingEnd ℂ b * fw m := by
  rw [fischer_eq_sum_of_support_subset P (monomial m b) {m} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]
end ReciprocityTheory.PGsh
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open scoped Classical
open ReciprocityTheory ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
namespace ReciprocityTheory.PGsh
theorem _root_.solution (P Q : MvPolynomial (Fin ν × ι) ℂ) (v : Fin ν × ι) :
    fischer (P * X v) Q = fischer P (pderiv v Q) := by
  induction Q using MvPolynomial.induction_on'
  next m b =>
    rw [MvPolynomial.pderiv_monomial, fischer_monomial_right, fischer_monomial_right,
      MvPolynomial.coeff_mul_X']
    split_ifs with h
    · have hv : m v ≠ 0 := Finsupp.mem_support_iff.1 h
      have hm : m - Finsupp.single v 1 + Finsupp.single v 1 = m := by
        ext x
        rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
        split_ifs with hx
        · subst hx
          omega
        · omega
      have hw : fw m = fw (m - Finsupp.single v 1) * (m v : ℂ) := by
        have h1 := fw_add_single (m - Finsupp.single v 1) v
        rw [hm, Finsupp.tsub_apply, Finsupp.single_eq_same,
          Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hv), Nat.cast_one, sub_add_cancel] at h1
        exact h1
      rw [hw, map_mul, map_natCast]
      ring
    · have hv : m v = 0 := by simpa [Finsupp.mem_support_iff] using h
      rw [hv]
      simp
  next Q₁ Q₂ h₁ h₂ =>
    rw [fischer_add_right, map_add, fischer_add_right, h₁, h₂]
end ReciprocityTheory.PGsh
