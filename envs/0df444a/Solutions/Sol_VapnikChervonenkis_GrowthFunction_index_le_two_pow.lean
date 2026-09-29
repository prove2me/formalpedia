-- Prove2me | solution 1 for VapnikChervonenkis.GrowthFunction.index_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:31:19.650988+00:00
-- url     : https://prove2.me/submissions/24750d56-fc1a-4b4b-8219-2d24284b6f07

import Mathlib
import Definitions.Def_VapnikChervonenkis_Shared_index
import Definitions.Def_VapnikChervonenkis_Shared_growthFunction

namespace VapnikChervonenkis.GrowthFunction

theorem aux_iltp_bound {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x ≤ 2 ^ r := by
  classical
  unfold Shared.index
  calc _ ≤ (Finset.univ : Finset (Finset (Fin r))).card := Finset.card_filter_le _ _
    _ = 2 ^ r := by simp [Finset.card_univ, Fintype.card_finset]

end VapnikChervonenkis.GrowthFunction

open VapnikChervonenkis.GrowthFunction
open VapnikChervonenkis

theorem solution {X : Type*} (S : Set (Set X)) {r : ℕ} (x : Fin r → X) :
    Shared.index S x ≤ 2 ^ r := aux_iltp_bound S x
