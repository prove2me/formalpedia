-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.fZ_multiHomogeneous_degree_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:01:11.904815+00:00
-- url     : https://prove2.me/submissions/0ab8dc01-1b12-4813-8d1c-8589d3dbafb8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ProdZpowEqZpowSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_KerPLeOfPlace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FZMultiHomogeneousDegreeSum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_rename_swap_F
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_F_degrees
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_aMM_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_componentForm_poly
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (F : KTp K d.D d.N)
    (hF : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F = d.fZ h c) :
    ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => d.delc c) F ∧
      (∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nPMM h c (d.w (d.jc c) c) p * (d.dg (d.gen p) : ℤ)) = d.delc c := by
  classical
  obtain ⟨F', hF', hF'0⟩ := d.componentForm_poly hd h c
  have hFF : F = F' := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N) (hF.trans hF'.symm)
  have hF0 : F ≠ 0 := hFF ▸ hF'0
  obtain ⟨hdeg0, hdegb⟩ := d.F_degrees hd h c F hF
  obtain ⟨ρ, hρ⟩ := d.rename_swap_F hd h c F hF
  have h10 : (1 : Fin (d.D + 1)) ≠ 0 := by
    have hD := hd.D_ge
    intro h1
    have h2 := congrArg (fun i : Fin (d.D + 1) => (i : ℕ)) h1
    first
    | (simp only [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (show 1 < d.D + 1 by omega)] at h2; omega)
    | (simp at h2; omega)
    | (simp [Fin.val_one'] at h2; omega)
  obtain ⟨s, hs⟩ : F.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
    exact hF0
  have ht : s.mapDomain swapT ∈ F.support := by
    have h1 : (rename swapT F).coeff (s.mapDomain swapT) = F.coeff s :=
      MvPolynomial.coeff_rename_mapDomain _ (swapT (D := d.D) (N := d.N)).injective F s
    rw [hρ, MvPolynomial.coeff_C_mul] at h1
    rw [MvPolynomial.mem_support_iff] at hs ⊢
    intro h0
    rw [h0, mul_zero] at h1
    exact hs h1.symm
  have key : (d.aMM h c).toNat = d.delc c := by
    rw [← hdegb 1 h10 s hs, ← hdeg0 _ ht]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsw : (swapT (D := d.D) (N := d.N)) (1, j) = (0, j) := by
      simp [swapT, Equiv.swap_apply_right]
    rw [← hsw, Finsupp.mapDomain_apply (swapT (D := d.D) (N := d.N)).injective]
  have hA : d.aMM h c = d.delc c := by
    have h1 := d.aMM_nonneg hd h c
    omega
  refine ⟨?_, hA⟩
  intro s' hs' b
  by_cases hb : b = 0
  · subst hb
    exact hdeg0 s' hs'
  · rw [hdegb b hb s' hs', key]
end ReciprocityTheory.ChartRestriction.G.T0.Data
