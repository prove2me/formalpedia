-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SpreadIso_equiv_221dddaf2d5b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:59:18.710573+00:00
-- url     : https://prove2.me/submissions/5123c5a4-f413-4a19-bcad-5420d3af9496

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_SpreadIsoModelIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_congr_1fd7b86894c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_id_4d71231cc7a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_assoc_b3f71914056c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_along_cancel_f626b308d17b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_pbSquare_iff_2698731efff4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_genFib_to_fc6efea8f4ed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_genOpen___7496082c92fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genRes___bee8f56e8f74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genOpen___comp_cefde62a231a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isIso_subPre___aa9e1c1a14f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_sub_to_fa96747bb723
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_exists_to_sub_443c20a1e1ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_spreadIso_model_iff_eee980e8fcc9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory AlgebraicGeometry
local notation "along" => GroundTheory.Heights₂.Heights.Model.pullbackIsoAlong
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace SpreadIso
theorem _root_.solution :
    GroundTheory.Heights₂.Heights.Model.SpreadIso.Statement ↔ SpreadIso.Statement := by
  rw [spreadIso_model_iff]
  constructor
  · intro hA X hX a ha F G hF hG ψ
    have := isIso_genOpen_ι X ha
    obtain ⟨t, ht⟩ := exists_genFib_to X ha.ne'
    have e2 := genOpen_ι_comp X ht
    have e1 : inv (genOpen X a).ι ≫ genRes X a = t := by rw [← e2, IsIso.inv_hom_id_assoc]
    obtain ⟨m', hm', ψA, hrel⟩ := hA X hX a ha F G hF hG t ht (along e1 ψ)
    have := isIso_subPre_ι X ha hm'
    obtain ⟨t', ht'⟩ := exists_genFib_to X (Nat.mul_ne_zero ha.ne' hm'.ne')
    have et' : t' ≫ X.homOfLE (invOpen_le X a m') = t := by
      rw [← cancel_mono (invOpen X a).ι, Category.assoc, Scheme.homOfLE_ι, ht', ht]
    obtain ⟨w, ew⟩ := exists_sub_to X a m'
    refine ⟨m', hm', along ew ψA, ?_⟩
    rw [pbSquare_iff]
    have hψ : ψ = along e2 (along e1 ψ) :=
      ((along_assoc e1 e2 (by rw [IsIso.hom_inv_id, Category.id_comp]) ψ).trans
        (along_id (IsIso.hom_inv_id _) _ ψ)).symm
    have M1 : subRes X a m' ≫ w = (genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι ≫ t' := by
      rw [← cancel_mono (invOpen X (a * m')).ι, Category.assoc, Category.assoc, Category.assoc, ht',
        ← Scheme.homOfLE_ι X (invOpen_le X a m'), reassoc_of% ew, reassoc_of% (subRes_square X a m'),
        genRes_ι]
    rw [hψ, ← hrel t' et', along_assoc ew (subRes_square X a m')
        (by rw [Category.assoc, ew, subRes_square]),
      along_assoc et' e2 (by rw [Category.assoc, et', e2]),
      along_assoc _ rfl (by rw [Category.assoc, Category.assoc, et', e2])]
    exact along_congr _ _ M1 _
  · intro hB X hX a ha F G hF hG t ht α
    have := isIso_genOpen_ι X ha
    have e2 := genOpen_ι_comp X ht
    obtain ⟨m', hm', fB, hrel⟩ := hB X hX a ha F G hF hG (along e2 α)
    rw [pbSquare_iff] at hrel
    have := isIso_subPre_ι X ha hm'
    obtain ⟨w', ew'⟩ := exists_to_sub X a m'
    refine ⟨m', hm', along ew' fB, fun t' e => ?_⟩
    have eρ : ((genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι) ≫ t =
        (genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ genRes X a := by rw [Category.assoc, e2]
    have E1 : (t' ≫ w') ≫ (subOpen X a m').ι = t := by rw [Category.assoc, ew', e]
    have M2 : ((genRes X a ⁻¹ᵁ subOpen X a m').ι ≫ (genOpen X a).ι) ≫ t' ≫ w' = subRes X a m' := by
      rw [← cancel_mono (subOpen X a m').ι, subRes_square]
      simp only [Category.assoc]
      rw [ew', e, e2]
    refine along_cancel eρ ?_
    rw [along_assoc ew' e E1, along_assoc E1 eρ (by rw [Category.assoc, E1, eρ]),
      along_congr _ (subRes_square X a m') M2, hrel, along_assoc e2 rfl eρ]
end SpreadIso
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
