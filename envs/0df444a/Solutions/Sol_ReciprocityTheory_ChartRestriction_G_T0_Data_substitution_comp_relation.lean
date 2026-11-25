-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.substitution_comp_relation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:53:47.856826+00:00
-- url     : https://prove2.me/submissions/4e5ad8af-7980-4167-9764-9388b9c31f2d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionVanishesOfRelation
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_ratio_self__251685145268

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField MvPolynomial
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) :
    (d.linearSubstitution c).comp (MvPolynomial.aeval (fun t : TVar d.D d.N =>
      (MvPolynomial.X (Sum.inr 0) * MvPolynomial.X (Sum.inl (t.1.succ, t.2)) -
        MvPolynomial.X (Sum.inr t.1.succ) * MvPolynomial.X (Sum.inl (0, t.2)) :
          MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K))) =
      ((d.pluckerSubstitution c).restrictScalars K).comp (d.relationEliminateColumn c) := by
  have hy : d.affineCoord c (d.jc c) = 1 := ratio_self' (hd.w_base c)
  have hs : ∀ a, d.affineRowCombination c a = ∑ k, X (a, k) * C (d.affineCoord c k) := fun a => rfl
  have hphi_inl : ∀ p, d.linearSubstitution c (X (Sum.inl p)) = X p := by
    intro p
    simp [Data.linearSubstitution]
  have hphi_inr : ∀ i, d.linearSubstitution c (X (Sum.inr i)) = d.affineRowCombination c i := by
    intro i
    simp [Data.linearSubstitution, Data.affineRowCombination]
  have hrho : ∀ t : TVar d.D d.N, d.pluckerSubstitution c (X t) =
      d.affineRowCombination c 0 * X (t.1.succ, t.2) - d.affineRowCombination c t.1.succ * X (0, t.2) := by
    intro t
    simp [Data.pluckerSubstitution]
  apply MvPolynomial.algHom_ext
  intro t
  simp only [AlgHom.comp_apply, aeval_X, map_sub, map_mul, hphi_inl, hphi_inr,
    AlgHom.restrictScalars_apply]
  simp only [Data.relationEliminateColumn, aeval_X]
  split_ifs with ht
  · rw [map_neg, map_sum]
    simp only [map_mul, hrho, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]

    have htot : ∑ k, (d.affineRowCombination c 0 * X (t.1.succ, k) - d.affineRowCombination c t.1.succ * X (0, k)) *
        C (d.affineCoord c k) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, ← hs]
      ring
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (d.jc c)), hy, map_one, mul_one] at htot
    have hC : ∀ r, d.pluckerSubstitution c (C r) = C r := fun r => by simp [Data.pluckerSubstitution]
    have hyd : ∀ k, ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c) = d.affineCoord c k := fun k => rfl
    simp only [hC, hyd]
    rw [ht]
    linear_combination htot
  · rw [hrho]
end ReciprocityTheory.ChartRestriction.G.T0.Data
