-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isBranch_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:57:31.608628+00:00
-- url     : https://prove2.me/submissions/faca7c3d-63d0-4b56-b17d-4c0dcc94dd90

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution {T : Set W} (hT : IsClosed T) {U V : W.Opens} {s : Γ(W, U)}
    {s' : Γ(W, V)} {y : W} (hyU : y ∈ U) (hyV : y ∈ V) {C : Set W} (hb : IsBranchH T s y C)
    (u : W.presheaf.stalk y) (heq : W.presheaf.germ V y hyV s' = W.presheaf.germ U y hyU s * u) :
    IsBranchH T s' y C := by
  unfold IsBranchH at hb ⊢
  obtain ⟨hC, hyC, hirr, hηU, hηZ⟩ := hb
  obtain ⟨U₁, hy1, t, ht⟩ := W.presheaf.germ_exist u
  have e1 : W.presheaf.germ (U ⊓ U₁) y (show y ∈ U ⊓ U₁ from ⟨hyU, hy1⟩)
      (W.presheaf.map (homOfLE inf_le_left).op s * W.presheaf.map (homOfLE inf_le_right).op t) =
      W.presheaf.germ U y hyU s * u := by
    rw [map_mul]
    first
    | (erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, ht])
    | (simp only [TopCat.Presheaf.germ_res_apply, ht])
  obtain ⟨O₀, hyO₀, i₁, i₂, hO₀⟩ :=
    W.presheaf.germ_eq y hyV (show y ∈ U ⊓ U₁ from ⟨hyU, hy1⟩) s' _ (heq.trans e1.symm)
  have hsp : (IsIrreducible.genericPoint hirr) ⤳ y := by
    first
    | exact (IsIrreducible.isGenericPoint_genericPoint_closure hirr).specializes (subset_closure hyC)
    | exact (IsIrreducible.genericPoint_spec hirr).specializes (subset_closure hyC)
  have hηO : (IsIrreducible.genericPoint hirr) ∈ O₀ := hsp.mem_open O₀.isOpen hyO₀
  have hzV : (IsIrreducible.genericPoint hirr) ∈ V := i₁.le hηO
  have hz1 : (IsIrreducible.genericPoint hirr) ∈ U₁ := (i₂.le hηO).2
  have hg : W.presheaf.germ V (IsIrreducible.genericPoint hirr) hzV s' =
      W.presheaf.germ U (IsIrreducible.genericPoint hirr) hηU s * W.presheaf.germ U₁ (IsIrreducible.genericPoint hirr) hz1 t := by
    have h1 := congrArg (W.presheaf.germ O₀ (IsIrreducible.genericPoint hirr) hηO) hO₀
    first
    | (erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, map_mul,
        TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h1; exact h1)
    | (simp only [TopCat.Presheaf.germ_res_apply, map_mul] at h1; exact h1)
  refine ⟨hC, hyC, hirr, hzV, ?_⟩
  simp only [Scheme.zeroLocus_singleton, Set.mem_compl_iff, SetLike.mem_coe] at hηZ ⊢
  rw [Scheme.mem_basicOpen _ _ _ hηU] at hηZ
  rw [Scheme.mem_basicOpen _ _ _ hzV, hg, IsUnit.mul_iff]
  exact fun h => hηZ h.1
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
