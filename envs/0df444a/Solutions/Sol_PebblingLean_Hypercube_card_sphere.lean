-- Prove2me | solution 1 for PebblingLean.Hypercube.card_sphere
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:52:37.785285+00:00
-- url     : https://prove2.me/submissions/0f652a43-ffa5-46ed-8561-7cc3f393bf6d

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Theorems.Thm_PebblingLean_Hypercube_dist_eq_card_diffSet
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution {n : ℕ} (base : HypercubeVertex n) (k : ℕ) :
    Fintype.card {v : HypercubeVertex n // dist base v = k} = Nat.choose n k := by
  classical
  let e :
      {v : HypercubeVertex n // dist base v = k} ≃
        {s : Finset (Fin n) // s.card = k} :=
    (diffSetEquiv base).subtypeEquiv (fun v => by
      change dist base v = k ↔ (diffSet base v).card = k
      simp [dist_eq_card_diffSet])
  calc
    Fintype.card {v : HypercubeVertex n // dist base v = k}
        = Fintype.card {s : Finset (Fin n) // s.card = k} := by
          exact Fintype.card_congr e
    _ = Nat.choose n k := by
          simp
end PebblingLean.Hypercube
