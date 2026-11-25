-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.exists_normalized_to
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:49.406659+00:00
-- url     : https://prove2.me/submissions/66f91fe3-dfab-4b02-aee3-06ff9db2341e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_mulGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_one_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_mulGen_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_of_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_corr_pullGen_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_invGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_normalized
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_sumElim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_gen_transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen_of_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sameSum_iff_fsum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {L : LB X} {K K' K₂ K₂' : Type} [Fintype K] [Fintype K'] [Fintype K₂] [Fintype K₂']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
  {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {φ₂' : K₂' → (Y ⟶ X)} {ε₂' : K₂' → ℤ}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K Kr : Type} [Fintype K] [Fintype Kr]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen)
    (p : Y ⟶ Z) (z : Z ⟶ Y) (hzp : z ≫ p = 𝟙 Z)
    (φr : Kr → (Z ⟶ X)) (εr : Kr → ℤ) (r : LB.Gen (LB.LinComb L φr εr)) (hr : r.IsGen)
    (h0 : fsum (fun k => z ≫ φ k) ε = fsum φr εr) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε t' z) r := by
  set rT := LB.pullGen L φr εr r p
  have hrT : rT.IsGen := pullGen_isGen_of_isGen _ _ r hr p
  set v := LB.mulGen L _ _ _ _ t (LB.invGen L _ _ rT)
  have hv : v.IsGen := mulGen_isGen_of_isGen _ ht _ (invGen_isGen_of_isGen _ hrT)
  have h0' : fsum (fun i => z ≫ Sum.elim φ (fun k => p ≫ φr k) i) (Sum.elim ε (fun k => -εr k)) = 0 := by
    rw [fsum_comp, fsum_sumElim, Finsupp.mapDomain_add, ← fsum_comp, h0, ← fsum_comp]
    have e : (fun k => z ≫ p ≫ φr k) = φr := by
      funext k
      rw [← Category.assoc, hzp, Category.id_comp]
    rw [e, fsum_neg, add_neg_cancel]
  obtain ⟨v', hv', hv1⟩ := exists_normalized hL _ _ v hv p z hzp h0'
  have hW := mulGen_isGen_of_isGen _ hv' _ hrT
  have hsW : LB.SameSum (Sum.elim (Sum.elim φ (fun k => p ≫ φr k)) (fun k => p ≫ φr k))
      (Sum.elim (Sum.elim ε (fun k => -εr k)) εr) φ ε := by
    rw [sameSum_iff_fsum, fsum_sumElim, fsum_sumElim, fsum_neg]
    abel
  obtain ⟨u, hu, hcW⟩ := gen_transport hL hsW _ hW
  refine ⟨u, hu, ?_⟩
  have c1 := corr_pullGen (corr_symm hcW) z
  have c2 := corr_pullGen_mulGen v' rT z
  have c4 := corr_trans hL (corr_pullGen_comp r p z)
    (corr_trans hL (corr_pullGen_of_eq r hr _ _ hzp) (corr_pullGen_id r))
  have c3 := corr_mulGen (corr_one_of (fun j hj => hv1 j hj)) c4
  have c5 := corr_mulGen_one r
  exact corr_trans hL c1 (corr_trans hL c2 (corr_trans hL c3 c5))
end ReciprocityTheory.ChartRestriction.G.DVR
