-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.SCPf.secondOrder_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:40:17.993506+00:00
-- url     : https://prove2.me/submissions/2b0ba588-9f79-4c64-9d98-eed2ce1f4ac1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LiftXHasSubst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SecondOrderIterateEqZero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_pairMin_step
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_SCPf_nablaL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.TB.SCPf.nablaL_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.SCPf
variable {k : Type} [CommRing k] {ι : Type} [Fintype ι]
variable {π : Type} [Fintype π] [DecidableEq π]
namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf
theorem _root_.solution (c : ι → π) (s : ι → Bool) (κ : ι → ι → k)
    (hκ : ∀ l l', κ l l' ≠ 0 → c l = c l' ∧ s l = true ∧ s l' = false) (Q : MvPolynomial ι k) (p j : ℕ)
    (hQ : ∀ n ∈ Q.support, pairMin c s n + j ≤ p) :
    ∀ n ∈ (secondOrder k κ Q).support, pairMin c s n + (j + 1) ≤ p := by
  intro n hn
  rw [MvPolynomial.mem_support_iff] at hn
  have h1 : coeff n (secondOrder k κ Q) = ∑ l, ∑ l', κ l l' * coeff n (pderiv l (pderiv l' Q)) := by
    rw [show secondOrder k κ Q = ∑ l, ∑ l', C (κ l l') * pderiv l (pderiv l' Q) from rfl]
    simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  rw [h1] at hn
  obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨l', -, hl'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hl
  have hκ0 : κ l l' ≠ 0 := left_ne_zero_of_mul hl'
  have hc0 : coeff n (pderiv l (pderiv l' Q)) ≠ 0 := right_ne_zero_of_mul hl'
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv] at hc0
  have hQn : n + Finsupp.single l 1 + Finsupp.single l' 1 ∈ Q.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    apply hc0
    rw [h0, zero_mul, zero_mul]
  obtain ⟨hcl, hsl, hsl'⟩ := hκ l l' hκ0
  have h2 := hQ _ hQn
  rw [pairMin_step c s n l l' hcl hsl hsl'] at h2
  omega
end ReciprocityTheory.ChartRestriction.G.TB.SCPf
