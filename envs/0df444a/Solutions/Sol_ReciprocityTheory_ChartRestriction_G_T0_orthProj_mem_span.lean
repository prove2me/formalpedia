-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.orthProj_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:37:13.978574+00:00
-- url     : https://prove2.me/submissions/ea755df2-65c6-458d-a12e-8eeebc2ab7bb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SingleMemStandardLattice
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsNeZeroMemNormSqLeGramDetDivRelIndex
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsSmallSaturatingVector

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Matrix NumberField
open scoped ComplexOrder
variable {K : Type} [Field K] [NumberField K] {r k : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {m : ℕ} (b : Fin k → Fin r → K) (c : Fin m → Fin r → K) {t : Fin r → K}
    (ht : t ∈ Submodule.span (𝓞 K) (Set.range c)) :
    hpv b t ∈ Submodule.span ℤ (Set.range (hwv b c)) := by
  classical
  obtain ⟨o, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 ht
  have e : ∀ j, o j • c j = ∑ a, (RingOfIntegers.basis K).repr (o j) a • (integralBasis K a • c j) := by
    intro j
    conv_lhs => rw [← (RingOfIntegers.basis K).sum_repr (o j)]
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_assoc, integralBasis_apply, algebraMap_smul]
  have e2 : hpv b (∑ j, o j • c j) = ∑ j, ∑ a, (RingOfIntegers.basis K).repr (o j) a • hwv b c (j, a) := by
    simp_rw [e]
    change hpvHom b _ = _
    simp only [map_sum, map_zsmul]
    rfl
  rw [e2]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun a _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, a), rfl⟩)
end ReciprocityTheory.ChartRestriction.G.T0
