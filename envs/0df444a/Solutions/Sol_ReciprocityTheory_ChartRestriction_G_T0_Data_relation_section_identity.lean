-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.relation_section_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:11.930068+00:00
-- url     : https://prove2.me/submissions/b10f0af8-297f-47b5-9a71-4abe6e2becee

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_BlockSphereProbIsProbabilityMeasure
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ratio_self_height


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (i : Fin (d.D + 1)) :
    d.sH c (MvPolynomial.X (i, d.jc c)) + ∑ k ∈ Finset.univ.erase (d.jc c),
      d.sH c (MvPolynomial.X (i, k)) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)) =
      if i = 0 then d.rationalBaseRow c else 0 := by
  have h1 : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 := ratio_self_height (hd.w_base c)
  split_ifs with hi
  · subst hi
    unfold Data.rationalBaseRow
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (d.jc c))]
    simp only [h1, map_one, mul_one]
  · have hsum : ∑ k ∈ Finset.univ.erase (d.jc c), d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)) =
        ∑ k : Fin d.N, d.sH c (MvPolynomial.X (i, (d.jc c).succAbove k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (d.x c k) := by
      have e1 := Finset.add_sum_erase Finset.univ (fun k => d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c)))
          (Finset.mem_univ (d.jc c))
      have e2 := Fin.sum_univ_succAbove (fun k => d.sH c (MvPolynomial.X (i, k)) *
          algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.w k c) (d.w (d.jc c) c))) (d.jc c)
      exact add_left_cancel (e1.trans e2)
    have hX : ∀ j, d.sH c (MvPolynomial.X (i, j)) = sImg (d.jc c) (d.x c) (i, j) :=
      fun j => MvPolynomial.aeval_X _ _
    have hS0 : ∀ (y : MvPolynomial (SVar d.D d.N) (Ω c)) (q : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c)),
        Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q (d.jc c) = y :=
      fun y q => Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q
    have hS1 : ∀ (y : MvPolynomial (SVar d.D d.N) (Ω c)) (q : Fin d.N → MvPolynomial (SVar d.D d.N) (Ω c))
        (k : Fin d.N), Fin.succAboveCases (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q
          ((d.jc c).succAbove k) = q k :=
      fun y q k => Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar d.D d.N) (Ω c)) (d.jc c) y q k
    have hA : d.sH c (MvPolynomial.X (i, d.jc c)) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
          (-∑ k, MvPolynomial.X (Sum.inr (i, k)) * MvPolynomial.C (d.x c k)) := by
      rw [hX]
      simp only [sImg, hS0, if_neg hi]
    have hB : ∀ k : Fin d.N, d.sH c (MvPolynomial.X (i, (d.jc c).succAbove k)) =
        algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
          (MvPolynomial.X (Sum.inr (i, k))) := by
      intro k
      rw [hX]
      simp only [sImg, hS1]
    rw [hsum, hA]
    simp only [hB]
    rw [map_neg, map_sum, neg_add_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), MvPolynomial.algebraMap_eq]
end ReciprocityTheory.ChartRestriction.G.T0.Data
