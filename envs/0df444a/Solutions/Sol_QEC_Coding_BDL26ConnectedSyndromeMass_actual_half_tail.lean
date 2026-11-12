-- Prove2me | solution 1 for QEC.Coding.BDL26ConnectedSyndromeMass.actual_half_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:01:35.519192+00:00
-- url     : https://prove2.me/submissions/cc474de1-43f9-441a-a896-f93af5afc2e3

import Definitions.Def_QEC_Locality_Graph_WeightedConnectedSetMass
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSetCounting
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalSyndromeWeights
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ConnectedSyndromeMass
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_envelope_nonneg
import Theorems.Thm_QEC_Coding_BDL26ConnectedSyndromeMass_actual_shifted_tail
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_WeightedConnectedSetMass_alpha_one_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ConnectedSyndromeMass
open Classical BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26TannerLocalRegularity BDL26DecodingGraph BDL26GraphQuantitativeBounds
open BDL26RXLocalReplacement BDL26RZLocalReplacement BDL26BoundedValence
open BDL26LocalSyndromeWeights BDL26ReplacementSupport MultiscaleDecoder
open scoped BigOperators Classical
universe u
namespace QEC.Coding.BDL26ConnectedSyndromeMass
theorem _root_.solution (S : OddScale) (depth L U : ℕ) (hd : 2≤depth)
    (t : ℝ) (hq : ratio S t≤1/2) (hL : 11≤L) :
    QEC.Locality.WeightedConnectedSetMass.interval (fun m => actualMass S depth m t) L U≤
      2*((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
        alphabet S^10*ratio S t^(L-10) := by
  have ht := actual_shifted_tail S depth L U hd t (by linarith) hL
  have h0 : 0≤ratio S t := mul_nonneg
    (by unfold alphabet; linarith [QEC.Locality.WeightedConnectedSetMass.alpha_one_le (14*S.ell^2+8)]) (envelope_nonneg S t)
  have hα : (0 : ℝ) ≤ alphabet S := by
    unfold alphabet
    exact le_trans (by norm_num) (QEC.Locality.WeightedConnectedSetMass.alpha_one_le _)
  have hp : 0≤((BDL26ConnectedSetCounting.levelTwoAnchors S depth).card : ℝ)*
      alphabet S^10*ratio S t^(L-10) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hα _)) (pow_nonneg h0 _)
  have hden : 0<1-ratio S t := by linarith
  exact ht.trans ((div_le_iff₀ hden).mpr (by
    nlinarith [mul_nonneg hp (show 0≤1-2*ratio S t by linarith)]))
end QEC.Coding.BDL26ConnectedSyndromeMass
