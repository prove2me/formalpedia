-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.support_free_of_block_subst_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:25:03.802675+00:00
-- url     : https://prove2.me/submissions/b43b8c72-e7fb-4749-a959-0e6e3b876a49

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DecompBlock0
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SupportFreeOfBlockSubstInvariant
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_mem_support_compB
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply


section
namespace ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
section Comp
variable {K : Type} [Field K] {D N : ℕ}
end Comp
section Pres
variable {K : Type} [Field K] [CharZero K] {D N : ℕ}
private lemma aeval_block_zero_monomial (s : TVar D N →₀ ℕ) (a : K) :
    (aeval (fun v : TVar D N => if v.1 = 0 then C ((0 : Fin (N + 1) → K) v.2) else X v) :
      KTp K D N →ₐ[K] KTp K D N) (monomial s a) =
      if degB 0 s = 0 then monomial s a else 0 := by
  rw [aeval_monomial]
  split_ifs with h
  · have h' : ∑ j, s (0, j) = 0 := h
    have hz : ∀ v ∈ s.support, v.1 ≠ 0 := by
      intro v hv h0
      have hsum : s (0, v.2) = 0 := Finset.sum_eq_zero_iff.mp h' v.2 (Finset.mem_univ _)
      have hv' : v = (0, v.2) := Prod.ext h0 rfl
      rw [Finsupp.mem_support_iff, hv'] at hv
      exact hv hsum
    rw [Finsupp.prod_congr (g2 := fun i k => (X i : KTp K D N) ^ k) (fun i hi => by simp [hz i hi]),
      MvPolynomial.algebraMap_eq, ← monomial_eq]
  · have h' : ∃ j, s (0, j) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (Finset.sum_eq_zero fun j _ => hc j)
    obtain ⟨j, hj⟩ := h'
    rw [Finsupp.prod, Finset.prod_eq_zero (i := ((0 : Fin (D + 1)), j))
      (Finsupp.mem_support_iff.mpr hj) (by simp [hj]), mul_zero]
end Pres
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
variable {K : Type} [Field K] [CharZero K] {D N : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (P : KTp K D N)
    (hP : ∀ x : Fin (N + 1) → K, (aeval (fun v : TVar D N =>
      if v.1 = 0 then C (x v.2) else X v) : KTp K D N →ₐ[K] KTp K D N) P = P) :
    ∀ s ∈ P.support, degB 0 s = 0 := by
  have h0 := hP 0
  have hc : (aeval (fun v : TVar D N => if v.1 = 0 then C ((0 : Fin (N + 1) → K) v.2) else X v) :
      KTp K D N →ₐ[K] KTp K D N) P = compB 0 0 P := by
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    simp only [aeval_block_zero_monomial]
    unfold compB
    rw [Finset.sum_filter]
  have hPc : P = compB 0 0 P := h0.symm.trans hc
  intro s hs
  rw [hPc] at hs
  exact (mem_support_compB hs).2
end ReciprocityTheory.ChartRestriction.G.T0
