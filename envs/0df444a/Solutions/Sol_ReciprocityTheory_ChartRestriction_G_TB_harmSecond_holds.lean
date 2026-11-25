-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.TB.harmSecond_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:40:10.571697+00:00
-- url     : https://prove2.me/submissions/dc096c9c-5b93-4d5e-bbbb-0327cb05042c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_mvpoly_pderiv_comm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB
namespace ReciprocityTheory.ChartRestriction.G.TB
theorem _root_.solution : HarmSecondSt := by
  intro k _ T _ r cc isX hcc hX n c hc P hP
  classical
  set S : (Σ τ : T, Fin (r τ)) → (Σ τ : T, Fin (r τ)) → MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k :=
    fun l l' => ∑ b : Fin n, MvPolynomial.pderiv (l, b) (MvPolynomial.pderiv (l', b) P) with hS
  have hsymm : ∀ l l', S l l' = S l' l := by
    intro l l'
    simp only [hS]
    exact Finset.sum_congr rfl fun b _ => mvpoly_pderiv_comm _ _ _
  have hzero1 : ∀ l l' : (Σ τ : T, Fin (r τ)), isX l.1 → l'.1 = cc l.1 → S l l' = 0 := by
    rintro ⟨σ, i⟩ ⟨σ', i'⟩ hXσ h
    dsimp only at h hXσ
    subst h
    exact hP σ hXσ i i'
  have hzero : ∀ l l' : (Σ τ : T, Fin (r τ)), l'.1 = cc l.1 → S l l' = 0 := by
    intro l l' h
    rcases hX l.1 with h1 | h1
    · exact hzero1 l l' h1 h
    · rw [hsymm]
      refine hzero1 l' l (by rw [h]; exact h1) ?_
      rw [h, hcc]
  have hterm : ∀ l l', MvPolynomial.C (c l l') * S l l' = 0 := by
    intro l l'
    by_cases h : l'.1 = cc l.1
    · rw [hzero l l' h, mul_zero]
    · rw [hc l l' h, map_zero, zero_mul]
  unfold secondOrder
  simp_rw [Fintype.sum_prod_type]
  simp only [apply_ite MvPolynomial.C, ite_mul, map_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  apply Finset.sum_eq_zero
  intro l _
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro l' _
  rw [← Finset.mul_sum]
  exact hterm l l'
end ReciprocityTheory.ChartRestriction.G.TB
