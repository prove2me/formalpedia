-- Prove2me | solution 1 for RH.Transport.SupportedMass.uniform_mass_bound_gives_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:16:30.016824+00:00
-- url     : https://prove2.me/submissions/1a03989a-07a9-4cbe-9e3f-35a3924f4f49

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
import Theorems.Thm_RH_Transport_SupportedMass_weighted_mass_decay

set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section
namespace RH.Transport.SupportedMass
theorem _root_.solution {ι : Type*} (q : ι → ℝ)
    (hbase : ∃ C : ℝ, 0 < C ∧ ∀ F : Finset ι,
      (∑ i ∈ F, q i ^ (-(3 / 2 : ℝ))) ≤ C) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : Finset ι) (a Z ell : ℝ),
      0 < a → 0 < Z → (∀ i ∈ F, a * Z ^ ell ≤ q i) →
      (∑ i ∈ F, q i ^ (-2 : ℝ)) ≤
        (C * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell / 2) := by
  obtain ⟨C, hC, hb⟩ := hbase
  refine ⟨C, hC, ?_⟩
  intro F a Z ell ha hZ hsupport
  simpa only [one_mul] using
    weighted_mass_decay F q (fun _ => 1) ha hZ
      (fun _ _ => zero_le_one) (fun i hi _ => hsupport i hi)
      (by simpa only [one_mul] using hb F)
end RH.Transport.SupportedMass
