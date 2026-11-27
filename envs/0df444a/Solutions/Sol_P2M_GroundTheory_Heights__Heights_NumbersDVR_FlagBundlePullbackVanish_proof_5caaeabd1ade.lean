-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_proof_5caaeabd1ade
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:05:25.893817+00:00
-- url     : https://prove2.me/submissions/db82ecdd-1117-40c7-b086-c2854e67e6f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundlePullbackVanish
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_liftDeg_eq_pullDeg_a8944c606549
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundlePullbackVanish_contract_projIdeal_be59b63ecd85

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
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
theorem _root_.solution (hPF : FieldNumbers.ProjectionFormulaContracted.Statement.{0})
    (hDim : FlagBundleDim.Statement) : FlagBundlePullbackVanish.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hVdim N E _ _ B w b hflag M a φ hφ Φ _ _ t ht i hi2 hiN L hL
  obtain ⟨hP, hrel⟩ := hDim F Ω K ι y e hV hVdim N E B w b hflag M a φ hφ Φ t ht i (by omega) hiN
  have hlen : (L.map liftDeg).length = e + i - 1 := by simp; omega
  have hrel' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t i)) =
      (((L.map liftDeg).length : ℕ) : WithBot (WithTop ℤ)) := by rw [hrel, hlen]
  have hrelV : FieldNumbers.relDim (ι := ι) (pointIdeal F y) =
      (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim, hVdim]
    have : (((e + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = e := by push_cast; ring
    exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
  have hcontr : FieldNumbers.relDim
      (FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ (truncCoord t i))) <
      (((L.map liftDeg).length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [contract_projIdeal]
    show FieldNumbers.relDim (ι := ι) (pointIdeal F y) < _
    rw [hrelV, hlen]
    show (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) <
      ((((e + i - 1 : ℕ) : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))
  have hzero := hPF F K (Option K) Function.Embedding.some (bundleIdx ι M)
    (projIdeal F y w φ (truncCoord t i)) hP _ hrel' hcontr
    (fun k => L.get (Fin.cast (by simp) k))
  rw [intNumL, ← hzero]
  congr 1
  funext k
  simp [liftDeg_eq_pullDeg]
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundlePullbackVanish
