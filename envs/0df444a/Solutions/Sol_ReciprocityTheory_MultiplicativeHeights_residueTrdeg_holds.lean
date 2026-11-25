-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.residueTrdeg_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:00:16.90075+00:00
-- url     : https://prove2.me/submissions/fd60c8db-737f-425d-adb7-402c17d09a4a

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValExists
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussValLeIffDivMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussIndepOfLeTrdeg
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussExtensionAndResidueTrdegEq
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gaussRed_coeff
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gaussRed_eval
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_aeval_mem
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_gauss_card_arith
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
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (hTR : TRStatement) : ResidueTrdegStatement := by
  intro K Ω U _ _ _ _ _ D hD σ _ t V ht τ _ u p hp hcard hpu hind
  letI _iW := residueAlgebra V (algebraMap Ω U)
  letI _io := residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
  letI : Algebra (IsLocalRing.ResidueField
      ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (IsLocalRing.ResidueField V) :=
    ((algebraMap _ (IsLocalRing.ResidueField V)).comp
      (algebraMap _ (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
  have hTRW := hTR K Ω (V.comap (algebraMap Ω U))
  rw [hD] at hTRW
  have hST : IsScalarTower
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (IsLocalRing.ResidueField (V.comap (algebraMap Ω U))) (IsLocalRing.ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hres : ∀ j, IsLocalRing.residue V (u j) =
      aeval (fun s => IsLocalRing.residue V ⟨t s, ht s⟩) (gaussRed V (p j) (hp j)) := by
    intro j
    obtain ⟨h, he⟩ := gaussRed_eval t V ht (p j) (hp j)
    have : u j = ⟨aeval t (p j), h⟩ := Subtype.ext (hpu j).symm
    rw [this, he]
  have hcardc : Cardinal.mk τ = ((Fintype.card σ + D : ℕ) : Cardinal) := by
    rw [Cardinal.mk_fintype, hcard]
  have hσ := Cardinal.mk_fintype σ
  have hmemW : ∀ j, IsLocalRing.residue V (u j) ∈
      Algebra.adjoin (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
        (Set.range fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := by
    intro j
    rw [hres j]
    exact gauss_aeval_mem _ _ (Algebra.adjoin _ _).toSubring
      (fun α => Subalgebra.algebraMap_mem _ _) (fun s => Algebra.subset_adjoin ⟨s, rfl⟩)
  have hW := gauss_card_le_trdeg_add _ _ hind hmemW
  rw [hcardc] at hW
  obtain ⟨h2, h3⟩ := gauss_card_arith hW hTRW (hσ ▸ gauss_trdeg_adjoin_le _)
  refine ⟨?_, h2, gauss_indep_of_le_trdeg _ (hσ.trans h3.symm).le⟩
  intro k₁ hk₁
  letI : Algebra k₁ (IsLocalRing.ResidueField V) :=
    ((algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap Ω U)))
      (IsLocalRing.ResidueField V)).comp (algebraMap k₁ _)).toAlgebra
  have hST1 : IsScalarTower
      (IsLocalRing.ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      k₁ (IsLocalRing.ResidueField V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hmem1 : ∀ j, IsLocalRing.residue V (u j) ∈
      Algebra.adjoin k₁ (Set.range fun s => IsLocalRing.residue V ⟨t s, ht s⟩) := by
    intro j
    rw [hres j]
    refine gauss_aeval_mem _ _ (Algebra.adjoin k₁ _).toSubring (fun α => ?_)
      (fun s => Algebra.subset_adjoin ⟨s, rfl⟩)
    have hc : (gaussRed V (p j) (hp j)).coeff α ∈ k₁ := by
      rw [gaussRed_coeff]; exact hk₁ j α
    exact Subalgebra.algebraMap_mem (Algebra.adjoin k₁ _) (⟨_, hc⟩ : k₁)
  have h1 := @gauss_card_le_trdeg_add _ _ _ _ _ _ _ _ _ hST1 _ _ _ _ hind hmem1
  rw [hcardc] at h1
  have hk : Algebra.trdeg _ k₁ ≤ (D : Cardinal) :=
    (trdeg_le_of_injective k₁.val Subtype.val_injective).trans hTRW
  exact (gauss_card_arith h1 hk (hσ ▸ gauss_trdeg_adjoin_le _)).1
end ReciprocityTheory.MultiplicativeHeights
