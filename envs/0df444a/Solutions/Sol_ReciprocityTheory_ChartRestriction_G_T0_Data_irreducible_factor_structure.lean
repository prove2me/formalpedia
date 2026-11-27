-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.irreducible_factor_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:07:07.061542+00:00
-- url     : https://prove2.me/submissions/620b6aa3-c679-4671-8d8f-6691f1984c85

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AevalElimEqRenameLinearSubstitution
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ComponentFormProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZEqConstMulIrreduciblePow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SubstitutionVanishesOfRelation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CoeffPsiBNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IrreducibleFactorStructure
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_componentForm_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fZ_eq_const_mul_irreducible_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_substitution_split_irreducible
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_substitution_vanishes_of_relation
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_MHF_isMH_of_pow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 (F c)) :
    ∃ (F1 : MvPolynomial ((Fin (d.D + 2) × Fin (d.N + 1)) ⊕ Fin (d.D + 2)) K) (κ : K)
      (a m deF : ℕ), κ ≠ 0 ∧ 1 ≤ m ∧ m * deF ≤ d.delc c ∧ Irreducible F1 ∧
      (∀ s ∈ F1.support, ∑ i, s (Sum.inr i) = deF) ∧
      (∀ s ∈ F1.support, ∑ p, s (Sum.inl p) ≤ (d.D + 1) * d.delc c) ∧
      bilinearSubstitution (F c) = MvPolynomial.C κ * MvPolynomial.X (Sum.inr 0) ^ a * F1 ^ m ∧
      d.linearSubstitution c (bilinearSubstitution (F c)) = 0 ∧
      ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := by

  obtain ⟨F0, κ0, m0, hκ0, hm0, hirr0, hFeq, hker⟩ := d.fZ_eq_const_mul_irreducible_pow hd h c (F c) (hF c) hpos
  obtain ⟨F', hF', -, hmh', -⟩ := d.componentForm_properties hd h c
  have hFF : F c = F' := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) ((hF c).trans hF'.symm)
  have hmh : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (F c) := hFF ▸ hmh'
  have hmh1 : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) (MvPolynomial.C κ0 * F0 ^ m0) := by
    rw [← hFeq]; exact hmh
  obtain ⟨d0, hd0, hmh0⟩ :=
    MHF.isMH_of_pow (Nat.succ_pos _) F0 κ0 m0 (d.delc c) hm0 hκ0 hirr0.ne_zero hmh1
  obtain ⟨a0, F1, deF, hG0, hirr1, hxh, hdeF, hU⟩ := d.substitution_split_irreducible hd c F0 hirr0 d0 hmh0 hker
  have hg : bilinearSubstitution (F c) = MvPolynomial.C κ0 * bilinearSubstitution F0 ^ m0 := by
    rw [hFeq]; simp only [bilinearSubstitution, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  refine ⟨F1, κ0, a0 * m0, m0, deF, hκ0, hm0, ?_, hirr1, hxh, ?_, ?_, ?_, hmh⟩
  · calc m0 * deF ≤ m0 * d0 := Nat.mul_le_mul_left _ hdeF
      _ = d.delc c := hd0
  · intro s hs
    refine (hU s hs).trans (Nat.mul_le_mul_left _ ?_)
    calc d0 ≤ m0 * d0 := Nat.le_mul_of_pos_left _ hm0
      _ = d.delc c := hd0
  · rw [hg, hG0, mul_pow, pow_mul]; ring
  · rw [hg, map_mul, map_pow, d.substitution_vanishes_of_relation hd c F0 ((hker F0).2 dvd_rfl), zero_pow (by omega), mul_zero]
end ReciprocityTheory.ChartRestriction.G.T0.Data
