-- Prove2me | solution 1 for PoAIndep.Topology.exists_lambda
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T07:43:14.228321+00:00
-- url     : https://prove2.me/submissions/775e6c56-5c37-4bca-be42-00d8a49bdc4a

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model
open PoAIndep.Topology

private theorem marginal_cont (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) :
    ContinuousOn (marginalCost ℓ) (Set.Ici 0) := by
  have hd : DifferentiableOn ℝ (fun x => x * ℓ x) (Set.Ici 0) :=
    differentiableOn_id.mul hℓ.1.2.1
  have hm : MonotoneOn (marginalCost ℓ) (Set.Ici 0) := hℓ.2.monotoneOn_derivWithin hd
  let S : Set ℝ := marginalCost ℓ '' Set.Ici 0
  have hS : Set.OrdConnected S := Set.ordConnected_Ici.image_derivWithin hd
  letI : Set.OrdConnected S := hS
  let f : Set.Ici (0 : ℝ) → S := fun x => ⟨marginalCost ℓ x, ⟨x, x.property, rfl⟩⟩
  have hf : Monotone f := fun x y hxy => hm x.property y.property hxy
  have hs : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  exact continuousOn_iff_continuous_restrict.mpr
    (continuous_subtype_val.comp (hf.continuous_of_surjective hs))

private theorem lambda_exists (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) (r : ℝ) (hr : 0 < r) :
    (marginalCost ℓ 0 = ℓ 0 ∧ ℓ 0 ≤ ℓ r ∧ ℓ r ≤ marginalCost ℓ r) ∧
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, marginalCost ℓ (lam * r) = ℓ r := by
  have h0 : marginalCost ℓ 0 = ℓ 0 := by
    have hd := (hasDerivWithinAt_id (0 : ℝ) (Set.Ici 0)).mul
      ((hℓ.1.2.1 0 (by simp)).hasDerivWithinAt)
    simpa [marginalCost, Pi.mul_def, id_def] using hd.derivWithin (uniqueDiffWithinAt_Ici 0)
  have hmono : ℓ 0 ≤ ℓ r := hℓ.1.2.2 (by simp) hr.le hr.le
  have hbound : ℓ r ≤ marginalCost ℓ r := by
    have h := hℓ.2.slope_le_derivWithin (by simp : (0 : ℝ) ∈ Set.Ici 0) hr.le hr
      ((differentiableOn_id.mul hℓ.1.2.1) r hr.le)
    simpa [slope_def_field, marginalCost, ne_of_gt hr] using h
  refine ⟨⟨h0, hmono, hbound⟩, ?_⟩
  have hc : ContinuousOn (marginalCost ℓ) (Set.Icc 0 r) :=
    (marginal_cont ℓ hℓ).mono (fun _ hx => hx.1)
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc hr.le hc ⟨by simpa [h0] using hmono, hbound⟩
  refine ⟨y/r, ⟨div_nonneg hy.1 hr.le, (div_le_one hr).2 hy.2⟩, ?_⟩
  simpa [ne_of_gt hr] using he

theorem solution (ℓ : ℝ → ℝ) (hℓ : IsStandard ℓ) (r : ℝ) (hr : 0 < r) :
    (marginalCost ℓ 0 = ℓ 0 ∧ ℓ 0 ≤ ℓ r ∧ ℓ r ≤ marginalCost ℓ r) ∧
      ∃ lam ∈ Set.Icc (0 : ℝ) 1, marginalCost ℓ (lam * r) = ℓ r := by
  exact lambda_exists ℓ hℓ r hr

#print axioms solution
