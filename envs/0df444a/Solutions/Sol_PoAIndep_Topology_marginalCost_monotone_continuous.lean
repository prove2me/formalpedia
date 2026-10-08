-- Prove2me | solution 1 for PoAIndep.Topology.marginalCost_monotone_continuous
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T03:26:42.050371+00:00
-- url     : https://prove2.me/submissions/e2242645-e981-4ef4-bb5b-adf045dfc709

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

open PoAIndep.Topology

theorem solution (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) :
    MonotoneOn (marginalCost ℓ) (Set.Ici 0) ∧ ContinuousOn (marginalCost ℓ) (Set.Ici 0) := by
  have hd : DifferentiableOn ℝ (fun x => x * ℓ x) (Set.Ici 0) :=
    differentiableOn_id.mul hℓ.1.2.1
  have hm : MonotoneOn (marginalCost ℓ) (Set.Ici 0) := hℓ.2.monotoneOn_derivWithin hd
  refine ⟨hm, ?_⟩
  let S : Set ℝ := marginalCost ℓ '' Set.Ici 0
  have hS : Set.OrdConnected S := Set.ordConnected_Ici.image_derivWithin hd
  letI : Set.OrdConnected S := hS
  let f : Set.Ici (0 : ℝ) → S := fun x => ⟨marginalCost ℓ x, ⟨x, x.property, rfl⟩⟩
  have hf : Monotone f := fun x y hxy => hm x.property y.property hxy
  have hs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hc := hf.continuous_of_surjective hs
  exact continuousOn_iff_continuous_restrict.mpr (continuous_subtype_val.comp hc)

#print axioms solution
