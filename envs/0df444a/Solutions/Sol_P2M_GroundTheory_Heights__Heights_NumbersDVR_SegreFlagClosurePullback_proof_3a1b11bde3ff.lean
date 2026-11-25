-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_SegreFlagClosurePullback_proof_3a1b11bde3ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:57.386349+00:00
-- url     : https://prove2.me/submissions/4a87de71-8bc9-4c08-9490-bd831d543c6b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_closureVarEquiv_fst_6eb917874e5f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinDeg_comp_closureBlockEquiv_741d524ae234
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_comp_5064ccd76e47
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureDeg_natAdd_18bace97db63
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_closureForm_d4ffbeabd6a1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_joinClosureForm_natAdd_7163a214e1b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_map_rename_f76916d7d583
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_algebraMap_218307a49609
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isPairExpansion_push_f1807b2e66f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairNum_pushExpansion_bef8f5d6e996


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace SegreFlagClosurePullback
theorem _root_.solution (hPull : PairNumberPullback.Statement)
    (hExp : PairNumberExpansionIndependence.Statement) (hMod : SegreFlagClosureModel.Statement)
    (hRel : PairNumberRelabel.Statement) (hVJ : VerticalDivisorJoinPullback.Statement)
    (hBir : SegreFlagClosureBirational.Statement) : SegreFlagClosurePullback.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hV N E _ _ B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ'
    hφ hφ' Φ _ _ _ _ e t ht k hk1 hkN f₁ g₁ hD₁ _ n z z' fz gz hz r Bf hBf As Bs hAs hBs Q hQ
  classical
  letI : ∀ s, Fintype (Sum.elim ι (lineBlocks M M') s) := fun s =>
    match s with
    | Sum.inl k => inferInstanceAs (Fintype (ι k))
    | Sum.inr o => inferInstanceAs (Fintype (lineBlocks M M' o))

  have hpt : joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k) ∘ closureVarEquiv ι M M' =
      flagClosurePt y w e φ φ' t k := by
    funext p
    rcases p with ⟨_ | (_ | o), l⟩ <;> rfl
  have hPJ : (pointIdeal O (flagClosurePt y w e φ φ' t k)).map (rename (closureVarEquiv ι M M')) =
      pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p)) (flagLinePt w e φ φ' t k)) := by
    rw [← hpt]
    exact pointIdeal_map_rename (closureBlockEquiv K) _ (closureVarEquiv_fst ι M M') _
  have hPV : pointIdeal O (fun p => algebraMap Ω Φ (y p)) = pointIdeal O y := pointIdeal_algebraMap y
  obtain ⟨hRmod, hRvert, hRnum⟩ := hRel O ϖ (Option (Option K)) (bundleIdx (bundleIdx ι M) M')
    (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) (closureBlockEquiv K) (closureVarEquiv ι M M')
    (closureVarEquiv_fst ι M M') (pointIdeal O (flagClosurePt y w e φ φ' t k))
  rw [hPJ] at hRmod hRvert hRnum
  have hJmod : IsModelOver (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p))
      (flagLinePt w e φ φ' t k))) (d + (k - 1)) :=
    hRmod _ (hMod O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht k
      hk1 hkN).1

  have hvert : ∀ i, IsVerticalDivisor (pointIdeal O (fun p => algebraMap Ω Φ (y p))) ϖ
      (Fin.append x z i - Fin.append x' z' i) (Fin.append f fz i) (Fin.append g gz i) := by
    rw [hPV]
    exact fun i => Fin.addCases (fun i => by simpa only [Fin.append_left] using hF.vertical i)
      (fun j => by simpa only [Fin.append_right] using hz j) i

  have hT := hRnum (1 + (N + n)) (joinClosureDeg (zetaFirst a₀) (Fin.append x z))
    (joinClosureDeg (zetaSecond a₀') (Fin.append x' z')) (closureForm M M' f₁ (Fin.append f fz))
    (closureForm M M' g₁ (Fin.append g gz)) As (Q.map joinDeg)
  have hQ' : (Q.map joinDeg).map (· ∘ closureBlockEquiv K) = Q.map liftPairDeg := by
    rw [List.map_map]
    exact List.map_congr_left fun L _ => joinDeg_comp_closureBlockEquiv L
  rw [rename_closureForm, rename_closureForm, joinClosureDeg_comp, joinClosureDeg_comp, hQ'] at hT
  rw [← hT]

  have hvJ : ∀ i, IsVerticalDivisor (pointIdeal O (joinCoords (fun p => algebraMap Ω Φ (y p))
      (flagLinePt w e φ φ' t k))) ϖ
      (joinClosureDeg (zetaFirst a₀) (Fin.append x z) i - joinClosureDeg (zetaSecond a₀') (Fin.append x' z') i)
      (joinClosureForm M M' (rename (closureVarEquiv ι M M') f₁) (Fin.append f fz) i)
      (joinClosureForm M M' (rename (closureVarEquiv ι M M') g₁) (Fin.append g gz) i) := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simp only [joinClosureDeg, joinClosureForm, Fin.append_left]
      apply hRvert
      have hζ : (zetaFirst a₀ ∘ (closureBlockEquiv K).symm - zetaSecond a₀' ∘ (closureBlockEquiv K).symm) ∘
          closureBlockEquiv K = zetaFirst a₀ - zetaSecond a₀' := by
        funext o
        simp
      rw [hζ]
      exact hD₁
    · simp only [joinClosureDeg, joinClosureForm, Fin.append_right]
      have hd : joinDeg (K' := Option Unit) (Fin.append x z j) - joinDeg (Fin.append x' z' j) =
          joinDeg (Fin.append x z j - Fin.append x' z' j) := by
        funext s
        rcases s with s | s <;> simp [joinDeg]
      rw [hd]
      exact hVJ O ϖ Φ K ι (Option Unit) (lineBlocks M M') _ _ _ _ _ (hvert j)

  rw [hExp O ϖ hϖ (K ⊕ Option Unit) (Sum.elim ι (lineBlocks M M')) _ (d + (k - 1)) hJmod (1 + (N + n)) _ _ _ _
    hvJ r (rename (Fin.natAdd 1) Bf) (hBf.rename_isHomogeneous) As (pushExpansion (Fin.natAdd 1) Bs) hAs
    (isPairExpansion_push _ hBs) (Q.map joinDeg) (by rw [List.length_map]; omega),
    pairNum_pushExpansion, joinClosureDeg_natAdd, joinClosureDeg_natAdd, joinClosureForm_natAdd,
    joinClosureForm_natAdd]

  have hPB := hPull O ϖ hϖ Φ K ι (Option Unit) (lineBlocks M M') (fun p => algebraMap Ω Φ (y p))
    (flagLinePt w e φ φ' t k) d (k - 1) (by rw [hPV]; exact hV) hJmod (N + n) (Fin.append x z)
    (Fin.append x' z') (Fin.append f fz) (Fin.append g gz) hvert r Bf hBf Bs hBs Q (by omega)
  split_ifs with hk
  · obtain rfl := hk
    rw [hPB.2 (hBir O ϖ hϖ Ω K ι y d hV N E B B' hBB' w w' x x' f g hF M M' a₀ a₀' φ φ' hφ hφ' Φ e t ht hkN),
      hPV]
  · exact hPB.1 (by omega)
end SegreFlagClosurePullback
end GroundTheory.Heights₂.Heights.NumbersDVR
