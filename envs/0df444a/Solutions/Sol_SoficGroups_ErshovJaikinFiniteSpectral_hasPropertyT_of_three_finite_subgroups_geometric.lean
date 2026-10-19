-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.hasPropertyT_of_three_finite_subgroups_geometric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/9a06c683-d2ac-4f18-8d37-5a9e63356528

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_hasPropertyT_of_geometric_finite_averaging

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
namespace SoficGroups.ErshovJaikinFiniteSpectral
theorem _root_.solution
    {G : Type u} [Group G]
    (K : Fin 3 → Subgroup G) [∀ i, Fintype (K i)]
    (hgen : (⨆ i : Fin 3, K i) = ⊤)
    (q : ℝ) (hq : q < 1)
    (haverage :
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] (π : SoficGroups.UnitaryRepresentation G H),
        ∃ A : H →L[ℂ] H,
          (∀ (x : H) (n : ℕ),
            dist ((A : H → H)^[n] x)
                ((A : H → H)^[n + 1] x) ≤
              (∑ g ∈ threeFiniteSubgroupGenerators K,
                ‖π g x - x‖) * q ^ n) ∧
          (∀ x : H, A x = x →
            ∀ (i : Fin 3) (g : K i), π (g : G) x = x)) :
    SoficGroups.HasPropertyT.{u, v} G := by
  apply hasPropertyT_of_geometric_finite_averaging
    (threeFiniteSubgroupGenerators K) q hq
  intro H _ _ _ π
  obtain ⟨A, hstep, hfixed⟩ := haverage H π
  refine ⟨A, hstep, ?_⟩
  intro x hx g
  have hK : ∀ i : Fin 3,
      K i ≤ unitaryVectorStabilizer π x := by
    intro i k hk
    exact hfixed x hx i ⟨k, hk⟩
  have htop : (⊤ : Subgroup G) ≤ unitaryVectorStabilizer π x := by
    rw [← hgen]
    exact iSup_le hK
  exact htop (show g ∈ (⊤ : Subgroup G) from Subgroup.mem_top g)
end SoficGroups.ErshovJaikinFiniteSpectral
