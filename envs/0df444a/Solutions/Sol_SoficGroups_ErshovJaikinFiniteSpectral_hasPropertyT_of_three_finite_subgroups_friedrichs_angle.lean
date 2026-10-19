-- Prove2me | solution 1 for SoficGroups.ErshovJaikinFiniteSpectral.hasPropertyT_of_three_finite_subgroups_friedrichs_angle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/2ea495f0-da3f-41ed-a17a-47949c517ffb

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
import Theorems.Thm_SoficGroups_ejThreeResidualEnergy_sqrt_div_three_le
import Theorems.Thm_SoficGroups_ejThreeProjectionAverage_fixed_mem
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_finiteUnitarySubgroupAverage_fixed
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_norm_finiteUnitarySubgroupAverage_sub_le
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_norm_sub_starProjection_le_finiteUnitarySubgroupAverage
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_mem_threeFiniteSubgroupGenerators
import Theorems.Thm_SoficGroups_ErshovJaikinFiniteSpectral_hasPropertyT_of_three_finite_subgroups_geometric

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
    (c : ℝ) (hc : 0 ≤ c) (hchalf : c < (1 / 2 : ℝ))
    (hangle :
      ∀ (H : Type v) [NormedAddCommGroup H]
        [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : SoficGroups.UnitaryRepresentation G H)
        (i j : Fin 3), i ≠ j →
        ∀ (a b : H),
          a ∈ SoficGroups.ejUnitaryFixedSubmodule π (K i) →
          a ∈ (SoficGroups.ejUnitaryFixedSubmodule π (K i) ⊓
            SoficGroups.ejUnitaryFixedSubmodule π (K j))ᗮ →
          b ∈ SoficGroups.ejUnitaryFixedSubmodule π (K j) →
          b ∈ (SoficGroups.ejUnitaryFixedSubmodule π (K i) ⊓
            SoficGroups.ejUnitaryFixedSubmodule π (K j))ᗮ →
            ‖inner ℂ a b‖ ≤ c * ‖a‖ * ‖b‖) :
    SoficGroups.HasPropertyT.{u, v} G := by
  classical
  let q : ℝ := 1 - (1 - 2 * c) / 6
  have hq : q < 1 := by
    dsimp [q]
    linarith
  have hqnonneg : 0 ≤ q := by
    dsimp [q]
    linarith
  apply hasPropertyT_of_three_finite_subgroups_geometric K hgen q hq
  intro H _ _ _ π
  let V : Fin 3 → Submodule ℂ H :=
    fun i => SoficGroups.ejUnitaryFixedSubmodule π (K i)
  letI : ∀ i : Fin 3, (V i).HasOrthogonalProjection := fun i => by
    dsimp [V]
    infer_instance
  letI : ∀ i j : Fin 3,
      (V i ⊓ V j).HasOrthogonalProjection := fun i j => by
    dsimp [V]
    infer_instance
  refine ⟨SoficGroups.ejThreeProjectionAverage V, ?_, ?_⟩
  · intro x n
    let T : ℝ := ∑ g ∈ threeFiniteSubgroupGenerators K,
      ‖π g x - x‖
    have hT : 0 ≤ T := by
      dsimp [T]
      positivity
    have hpoint (i : Fin 3) (k : K i) :
        ‖π (k : G) x - x‖ ≤ T := by
      dsimp [T]
      exact Finset.single_le_sum
        (s := threeFiniteSubgroupGenerators K)
        (f := fun g : G => ‖π g x - x‖)
        (fun g _ => norm_nonneg _)
        ((mem_threeFiniteSubgroupGenerators K (k : G)).mpr
          ⟨i, k.property⟩)
    have havgbound (i : Fin 3) :
        ‖finiteUnitarySubgroupAverage π (K i) x - x‖ ≤ T := by
      calc
        ‖finiteUnitarySubgroupAverage π (K i) x - x‖ ≤
            (Fintype.card (K i) : ℝ)⁻¹ *
              ∑ k : K i, ‖π (k : G) x - x‖ :=
          norm_finiteUnitarySubgroupAverage_sub_le π (K i) x
        _ ≤ (Fintype.card (K i) : ℝ)⁻¹ *
              ∑ _k : K i, T := by
          apply mul_le_mul_of_nonneg_left
          · exact Finset.sum_le_sum fun k _ => hpoint i k
          · positivity
        _ = T := by
          have hcard : (Fintype.card (K i) : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          simp [hcard]
    have hres (i : Fin 3) :
        ‖SoficGroups.ejResidualProjection (V i) x‖ ≤ T := by
      rw [SoficGroups.ejResidualProjection_apply]
      apply le_trans
        (norm_sub_starProjection_le_finiteUnitarySubgroupAverage
          π (K i) (V i) x ?_)
        (havgbound i)
      exact (SoficGroups.mem_ejUnitaryFixedSubmodule π (K i) _).mpr
        (finiteUnitarySubgroupAverage_fixed π (K i) x)
    have hfullangle : ∀ (i j : Fin 3) (a b : H),
        a ∈ V i → a ∈ (V i ⊓ V j)ᗮ →
        b ∈ V j → b ∈ (V i ⊓ V j)ᗮ →
          ‖inner ℂ a b‖ ≤ c * ‖a‖ * ‖b‖ := by
      intro i j a b ha haorth hb hborth
      by_cases hij : i = j
      · subst j
        have hazero : a = 0 :=
          inner_self_eq_zero.mp (haorth a ⟨ha, ha⟩)
        simp [hazero]
      · exact hangle H π i j hij a b ha haorth hb hborth
    calc
      dist (((SoficGroups.ejThreeProjectionAverage V : H → H)^[n]) x)
          (((SoficGroups.ejThreeProjectionAverage V : H → H)^[n + 1]) x)
          ≤ Real.sqrt (SoficGroups.ejThreeResidualEnergy V x / 3) *
              (1 - (1 - 2 * c) / 6) ^ n :=
        SoficGroups.ejThreeProjectionAverage_iterate_dist_le_of_pair_angles
          V c hc hchalf hfullangle x n
      _ ≤ T * q ^ n := by
        change Real.sqrt (SoficGroups.ejThreeResidualEnergy V x / 3) *
          q ^ n ≤ T * q ^ n
        exact mul_le_mul_of_nonneg_right
          (SoficGroups.ejThreeResidualEnergy_sqrt_div_three_le
            V x T hT hres)
          (pow_nonneg hqnonneg n)
      _ = (∑ g ∈ threeFiniteSubgroupGenerators K,
            ‖π g x - x‖) * q ^ n := by
        rfl
  · intro x hx i k
    have hxmem : x ∈ V i :=
      SoficGroups.ejThreeProjectionAverage_fixed_mem V x hx i
    exact (SoficGroups.mem_ejUnitaryFixedSubmodule π (K i) x).mp
      hxmem k
end SoficGroups.ErshovJaikinFiniteSpectral
