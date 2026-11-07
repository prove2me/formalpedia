-- Prove2me | solution 1 for QEC.Coding.QuantumTanner.LiftedProductTannerBridge.chartLink_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:21:37.8395+00:00
-- url     : https://prove2.me/submissions/42bd73ba-e739-4575-bca0-8b1f8ef839e6

import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTensorBridge
import Definitions.Def_QEC_Coding_QuantumTanner_LiftedProductTannerBridge

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner QEC.Coding.QuantumTanner.LiftedProductTannerBridge
open Classical
open LiftedProductRestriction LiftedProductActionBridge LiftedProductTensorBridge
universe v
variable {G A B C D C' D' : Type v} [Group G] [Fintype G] [DecidableEq G]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
  [Fintype C'] [DecidableEq C'] [Fintype D'] [DecidableEq D']
namespace QEC.Coding.QuantumTanner.LiftedProductTannerBridge
theorem _root_.solution (a : A → G) (b : B → G) (left right : Bool) (u : G) :
    Function.Injective (chartLink a b left right u) := by
  intro p q h
  apply Prod.ext
  · exact congrArg (fun x : A × B × G => x.1) h
  · exact congrArg (fun x : A × B × G => x.2.1) h
end QEC.Coding.QuantumTanner.LiftedProductTannerBridge
