-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCut_proof_e41d5e698594
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:04:59.578205+00:00
-- url     : https://prove2.me/submissions/17ba2ab6-8f60-4c8d-8fb6-3587fcb3b35c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleCut
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_intNumL_cons_eq_snoc_d16d0916dd87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_cycEval_single_0f71e3b89ba9

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
open FlagBundleCutProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace FlagBundleCut
theorem _root_.solution (hDim : FlagBundleDim.Statement)
    (hForms : FlagBundleSectionForms.Statement) (hDiv : FlagBundleSectionDiv.Statement)
    (hCut : FieldNumbers.CutRational.Statement.{0}) : FlagBundleCut.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hdim N E _ _ B w b hB M a φ hφ Φ _ _ t ht i hi L hL
  obtain ⟨bf, bg, f, g, hf, hg, hdeg, hfP, hgP, hval⟩ :=
    hForms F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i
  have hdiv := hDiv F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht i hi bf bg f g hf hg hdeg hgP hval
  obtain ⟨hP, hrel⟩ :=
    hDim F Ω K ι y e hV hdim N E B w b hB M a φ hφ Φ t ht ((i : ℕ) + 1) (by omega) i.2
  have hrel' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t ((i : ℕ) + 1))) =
      ((L.length + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hrel]
    congr 2
    omega
  have h := hCut F (Option K) (bundleIdx ι M) _ hP L.length hrel' bf bg f g hf hg hfP hgP L.get
  rw [intNumL_cons_eq_snoc, ← hdeg, h, funext hdiv, intNumL]
  classical
  convert cycEval_single (fun W => intNum F W L.get) (projIdeal F y w φ (truncCoord t i))
end FlagBundleCut
end GroundTheory.Heights₂.Heights.NumbersDVR
