-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_T0_ratio_self__251685145268
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:41:33.805416+00:00
-- url     : https://prove2.me/submissions/9250e386-0cc9-4296-abc8-be9a196b127e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionVanishesOfRelation

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
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] {f : V} (hf : f ≠ 0) :
    ratio (Ω := Ω) f f = 1 := by
  have hex : ∃ a : Ω, f = a • f := ⟨1, (one_smul Ω f).symm⟩
  unfold ratio
  rw [dif_pos hex]
  have hs := hex.choose_spec
  have h0 : (hex.choose - 1) • f = 0 := by rw [sub_smul, ← hs, one_smul, sub_self]
  rcases smul_eq_zero.mp h0 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hf
end ReciprocityTheory.ChartRestriction.G.T0
