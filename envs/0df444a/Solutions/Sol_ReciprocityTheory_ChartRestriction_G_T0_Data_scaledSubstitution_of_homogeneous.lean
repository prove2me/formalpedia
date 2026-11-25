-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.scaledSubstitution_of_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:08.911025+00:00
-- url     : https://prove2.me/submissions/7928dd67-1c10-49f7-8c70-39a7521a5cf7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_aeval_elim_mul_of_xhom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_scaledSubstitution_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aeval_elim_eq_rename_linearSubstitution

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
theorem _root_.solution (c : ι) (n : ℕ)
    (Q : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K)
    (hQ : ∀ s ∈ Q.support, ∑ i, s (Sum.inr i) = n) :
    d.scaledSubstitution c Q = MvPolynomial.X none ^ n * MvPolynomial.rename some (d.linearSubstitution c Q) := by
  rw [scaledSubstitution_eq, aeval_elim_mul_of_xhom _ _ _ n Q hQ, aeval_elim_eq_rename_linearSubstitution]
end ReciprocityTheory.ChartRestriction.G.T0.Data
