-- Prove2me | solution 1 for PI.WickFormula.Asm.claim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:50:44.944504+00:00
-- url     : https://prove2.me/submissions/17846e28-e4d9-408f-941c-9acfb6fe058d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_DeltaEqGdelta
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_WickFormula_XdegLeTotalDegree
import Theorems.Thm_PI_WickFormula_Asm_xdeg_add
import Theorems.Thm_PI_WickFormula_Asm_xdeg_single
import Theorems.Thm_PI_WickFormula_Asm_dL_monomial_support
import Theorems.Thm_PI_WickFormula_Asm_phiH_apply
import Theorems.Thm_PI_WickFormula_Asm_psi_sum
import Theorems.Thm_PI_WickFormula_Asm_phi_X
import Theorems.Thm_PI_WickFormula_Asm_psi_X
import Theorems.Thm_PI_WickFormula_Asm_psi_base

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open PI PI.WickFormula PI.WickFormula.Asm
variable {k AA M : Type} [CommRing k] [Algebra ℚ k] [Ring AA] [Algebra k AA] [AddCommGroup M]
  [Module AA M] {r s : ℕ}
variable {a b : Fin r → AA} {a' b' : Fin s → AA} {κ : Fin r → Fin s → k} {σ₀ : M}
namespace PI.WickFormula.Asm
theorem _root_.solution (h1 : OrdLin) (h2 : OrdX) (h3 : Base) (h4 : BComm) (g1 : Gen.PowXL) (g2 : Gen.CommL)
    (g3 : Gen.VanL) (H : Hyp a b a' b' κ σ₀) (d : ℕ) :
    ∀ R : MvPolynomial (Fin r ⊕ Fin s) k, (∀ m ∈ R.support, xdeg m ≤ d) → ∀ N, d < N →
      phiH h1 a b a' b' σ₀ R = psi h1 a a' κ σ₀ N R := by
  induction d with
  | zero =>
    intro R hR N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [psi_base h1 g3 N' R (fun m hm => Nat.le_zero.mp (hR m hm)), phiH_apply]
    apply h3 k AA M r s a b a' b' κ σ₀ H R
    intro m hm i
    have := hR m hm
    unfold xdeg at this
    exact Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp this) i (Finset.mem_univ _)
  | succ d ih =>
    intro R hR N hN
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [R.as_sum, map_sum, psi_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmd := hR m hm
    by_cases h0 : xdeg m = 0
    · refine ih _ (fun u hu => ?_) _ (by omega)
      have hu' := MvPolynomial.support_monomial_subset hu
      rw [Finset.mem_singleton] at hu'
      subst hu'
      omega
    · have h0' : ∑ i, m (Sum.inl i) ≠ 0 := h0
      obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0'
      obtain ⟨m', hm'd⟩ : ∃ m', m' = m - Finsupp.single (Sum.inl i) 1 := ⟨_, rfl⟩
      have hm' : m = Finsupp.single (Sum.inl i) 1 + m' := by
        ext x
        by_cases hx : x = Sum.inl i
        · subst hx
          simp [hm'd]
          omega
        · simp [hm'd, Finsupp.single_apply, Ne.symm hx]
      have hxm' : xdeg m' ≤ d := by
        have := xdeg_add (Finsupp.single (Sum.inl i : Fin r ⊕ Fin s) 1) m'
        rw [← hm', xdeg_single] at this
        omega
      have hmon : monomial m (coeff m R) = X (Sum.inl i) * monomial m' (coeff m R) := by
        rw [X, monomial_mul, one_mul, ← hm']
      rw [hmon, phi_X h1 h2 h4 H, psi_X h1 h2 g1 g2 H]
      have e1 := ih (monomial m' (coeff m R)) (fun u hu => by
        have hu' := MvPolynomial.support_monomial_subset hu
        rw [Finset.mem_singleton] at hu'
        rw [hu']
        exact hxm') (N' + 1) (by omega)
      have e2 := ih (Gen.dL κ i (monomial m' (coeff m R)))
        (fun u hu => (dL_monomial_support κ i m' _ u hu).trans hxm') N' (by omega)
      rw [e1, e2]
end PI.WickFormula.Asm
