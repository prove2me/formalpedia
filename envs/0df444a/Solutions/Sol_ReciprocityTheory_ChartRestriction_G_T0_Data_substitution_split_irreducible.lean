-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.substitution_split_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:16:12.285627+00:00
-- url     : https://prove2.me/submissions/76c535b8-7775-43bc-807f-f6f656dcd26d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionSplitIrreducibleOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionVanishesOfRelation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_substitution_split_irreducible_of


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
theorem _root_.solution (hd : d.AxH 𝒜) (c : ι) (F0 : KTp K d.D d.N) (hirr : Irreducible F0) (d0 : ℕ)
    (hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d0) F0)
    (hker : ∀ Q : KTp K d.D d.N, d.relationEliminateColumn c Q = 0 ↔ F0 ∣ Q) :
    ∃ (a : ℕ) (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (deF : ℕ),
      bilinearSubstitution F0 = X (Sum.inr 0) ^ a * F1 ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧ deF ≤ d0 ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d0) := d.substitution_split_irreducible_of c F0 hirr d0 hmh hker
end ReciprocityTheory.ChartRestriction.G.T0.Data
