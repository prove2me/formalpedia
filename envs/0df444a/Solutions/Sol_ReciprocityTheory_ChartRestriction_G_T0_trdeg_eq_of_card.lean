-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.trdeg_eq_of_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:31:11.649533+00:00
-- url     : https://prove2.me/submissions/cf074f9d-90fc-4c8e-a320-fe97fd233c0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_IntegralClosureRankAndResidueTrdegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraicIndependentResidueOfIsUnit
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_card_le_trdeg_add
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_indep_of_le_trdeg
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_trdeg_adjoin_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open MvPolynomial
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {F E C : Type} [Field F] [Field E] [Field C] [Algebra F E] [Algebra E C]
    [Algebra F C] {σ τ : Type} [Fintype σ] [Fintype τ] (tb : σ → C)
    (ub : τ → C) (hu : AlgebraicIndependent F ub)
    (hmem : ∀ j, ub j ∈ Algebra.adjoin E (Set.range tb)) (n : ℕ)
    (hE : Algebra.trdeg F E ≤ n) (hcard : Fintype.card τ = Fintype.card σ + n)
    (hT : ∀ x : F, algebraMap F C x = algebraMap E C (algebraMap F E x)) :
    Algebra.trdeg F E = n ∧ AlgebraicIndependent E tb := by
  haveI : IsScalarTower F E C := IsScalarTower.of_algebraMap_eq hT
  have h1 := ReciprocityTheory.MultiplicativeHeights.gauss_card_le_trdeg_add tb ub hu hmem
  have h2 := ReciprocityTheory.MultiplicativeHeights.gauss_trdeg_adjoin_le (E := E) tb
  obtain ⟨a, ha⟩ : ∃ a : ℕ, Algebra.trdeg F E = a :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt hE (Cardinal.nat_lt_aleph0 n))
  rw [Cardinal.mk_fintype] at h2
  obtain ⟨b, hb⟩ : ∃ b : ℕ, Algebra.trdeg E (Algebra.adjoin E (Set.range tb)) = b :=
    Cardinal.lt_aleph0.mp (lt_of_le_of_lt h2 (Cardinal.nat_lt_aleph0 _))
  rw [Cardinal.mk_fintype, hcard, ha, hb] at h1
  rw [ha] at hE
  rw [hb] at h2
  have h1' : Fintype.card σ + n ≤ a + b := by exact_mod_cast h1
  have hE' : a ≤ n := by exact_mod_cast hE
  have h2' : b ≤ Fintype.card σ := by exact_mod_cast h2
  have han : a = n := by omega
  have hbs : b = Fintype.card σ := by omega
  refine ⟨by rw [ha, han], ReciprocityTheory.MultiplicativeHeights.gauss_indep_of_le_trdeg tb ?_⟩
  rw [hb, hbs, Cardinal.mk_fintype]
end ReciprocityTheory.ChartRestriction.G.T0
