-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockRootSubgroups_pair_inner_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/49fafae1-0aa9-425f-b4ab-2d1633c9456f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_inner_sq_le_of_finite_orthogonal_sector_splitting
import Theorems.Thm_SoficGroups_finite_finiteOuterBlockRootSubgroup
import Theorems.Thm_SoficGroups_finiteOuterBlockRoot_commutator_exists_productCentral
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_commute_left
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_commute_right
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoot_pair_le_centralizer
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentralRoots_commute
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_sup
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_starProjection_mem_of_commute
import Theorems.Thm_SoficGroups_unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
import Theorems.Thm_SoficGroups_finiteOuterBlockProductCentral_centerComplement_inner_sq_le
import Theorems.Thm_SoficGroups_inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
namespace SoficGroups
theorem _root_.solution
    {R : Type*} [Ring R] [Algebra (ZMod 2) R]
    {H : Type v₁} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (W : Submodule (ZMod 2) R) [Finite W]
    (i j k : Fin 3)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (π : UnitaryRepresentation
      (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) H)
    {a b : H}
    (ha : a ∈ unitaryFixedSubmodule π
      (finiteOuterBlockRootSubgroup W i j hij))
    (hb : b ∈ unitaryFixedSubmodule π
      (finiteOuterBlockRootSubgroup W j k hjk))
    (haQ : a ∈
      (unitaryFixedSubmodule π
        (finiteOuterBlockRootSubgroup W i j hij) ⊓
       unitaryFixedSubmodule π
        (finiteOuterBlockRootSubgroup W j k hjk))ᗮ)
    (hbQ : b ∈
      (unitaryFixedSubmodule π
        (finiteOuterBlockRootSubgroup W i j hij) ⊓
       unitaryFixedSubmodule π
        (finiteOuterBlockRootSubgroup W j k hjk))ᗮ) :
    8 * ‖inner ℂ a b‖ ^ 2 ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  let X := finiteOuterBlockRootSubgroup W i j hij
  let Y := finiteOuterBlockRootSubgroup W j k hjk
  let Z (B : Matrix (Fin 3) (Fin 3) W) :=
    finiteOuterBlockProductCentralRootSubgroup W i k hik B
  let Q : Submodule ℂ H :=
    unitaryFixedSubmodule π X ⊓ unitaryFixedSubmodule π Y
  let U : Submodule ℂ H := unitaryFixedSubmodule π X ⊓ Qᗮ
  let V : Submodule ℂ H := unitaryFixedSubmodule π Y ⊓ Qᗮ
  let F (B : Matrix (Fin 3) (Fin 3) W) :=
    unitaryFixedSubmodule π (Z B)
  letI : Finite X := finite_finiteOuterBlockRootSubgroup W i j hij
  letI : Fintype X := Fintype.ofFinite X
  letI (B : Matrix (Fin 3) (Fin 3) W) : CompleteSpace (F B) :=
    unitaryFixedSubmodule_completeSpace π (Z B)
  have hpairCentral (B : Matrix (Fin 3) (Fin 3) W) :
      ∀ z : Z B, ∀ g :
        (X ⊔ Y : Subgroup
          (elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))),
        Commute
          (z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
          (g : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
    intro z g
    have hg := finiteOuterBlockProductCentralRoot_pair_le_centralizer
      W i j k hij hjk hik B g.property
    rw [Subgroup.mem_centralizer_iff] at hg
    change (z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
      (g : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) =
      (g : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
      (z : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    exact hg z z.property
  refine inner_sq_le_of_finite_orthogonal_sector_splitting
    F U V ?_ ?_ ?_ ?_ ?_ a b ⟨ha, haQ⟩ ⟨hb, hbQ⟩
  · intro B x hx
    change (unitaryFixedSubmodule π (Z B)).starProjection x ∈
      unitaryFixedSubmodule π X ⊓ Qᗮ
    refine ⟨?_, ?_⟩
    · exact unitaryFixedSubmodule_starProjection_mem_of_commute
        π (Z B) X
        (fun z x =>
          (finiteOuterBlockProductCentralRoot_commute_left
            W i j k hij hik B x z x.property z.property).symm)
        hx.1
    · have hq : x ∈ (unitaryFixedSubmodule π (X ⊔ Y))ᗮ := by
        rw [unitaryFixedSubmodule_sup]
        exact hx.2
      have hp := unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
        π (Z B) (X ⊔ Y) (hpairCentral B) hq
      rw [unitaryFixedSubmodule_sup] at hp
      exact hp
  · intro B x hx
    change (unitaryFixedSubmodule π (Z B)).starProjection x ∈
      unitaryFixedSubmodule π Y ⊓ Qᗮ
    refine ⟨?_, ?_⟩
    · exact unitaryFixedSubmodule_starProjection_mem_of_commute
        π (Z B) Y
        (fun z y =>
          (finiteOuterBlockProductCentralRoot_commute_right
            W i j k hjk hik B y z y.property z.property).symm)
        hx.1
    · have hq : x ∈ (unitaryFixedSubmodule π (X ⊔ Y))ᗮ := by
        rw [unitaryFixedSubmodule_sup]
        exact hx.2
      have hp := unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
        π (Z B) (X ⊔ Y) (hpairCentral B) hq
      rw [unitaryFixedSubmodule_sup] at hp
      exact hp
  · intro B C x hx
    change (unitaryFixedSubmodule π (Z B)).starProjection x ∈
      unitaryFixedSubmodule π (Z C)
    exact unitaryFixedSubmodule_starProjection_mem_of_commute
      π (Z B) (Z C)
      (fun z w => finiteOuterBlockProductCentralRoots_commute
        W i k hik B C z w z.property w.property)
      hx
  · intro B x y hx hy hxZ _
    exact finiteOuterBlockProductCentral_centerComplement_inner_sq_le
      W i j k hij hjk hik B π hx.1 hxZ hy.1
  · intro x y hx hy _ hyF
    apply inner_eq_zero_of_finite_subgroupAverage_pair_orthogonal
      π X Y x y
    · exact (mem_unitaryFixedSubmodule π X x).mp hx.1
    · intro s t
      obtain ⟨B, hB⟩ :=
        finiteOuterBlockRoot_commutator_exists_productCentral
          W i j k hij hjk hik s t s.property t.property
      let c : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R) :=
        ⁅(s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)),
          (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))⁆
      have hcb : π c⁻¹ y = y :=
        (mem_unitaryFixedSubmodule π (Z B) y).mp (hyF B)
          ⟨c⁻¹, (Z B).inv_mem hB⟩
      have htb : π (t : elementaryGroup (Fin 3)
          (Matrix (Fin 3) (Fin 3) R)) y = y :=
        (mem_unitaryFixedSubmodule π Y y).mp hy.1 t
      have hsc : Commute
          (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) c :=
        finiteOuterBlockProductCentralRoot_commute_left
          W i j k hij hik B s c s.property hB
      have hgroup :
          (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) =
            (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              c⁻¹ *
              (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
        calc
          (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) =
            c⁻¹ *
              (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
                dsimp [c]
                simp only [commutatorElement_def]
                group
          _ = (s : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) *
              c⁻¹ *
              (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R)) := by
                rw [hsc.inv_right.eq]
      calc
        π (t : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
            (π (s : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R)) y) =
          π ((t : elementaryGroup (Fin 3)
            (Matrix (Fin 3) (Fin 3) R)) * s) y := by
              simp [map_mul]
        _ = π ((s : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R)) * c⁻¹ * t) y := by
              rw [hgroup]
        _ = π (s : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R))
            (π c⁻¹ (π (t : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R)) y)) := by
              simp [map_mul]
        _ = π (s : elementaryGroup (Fin 3)
              (Matrix (Fin 3) (Fin 3) R)) y := by
              rw [htb, hcb]
    · intro z hzX hzY
      apply (Submodule.mem_orthogonal' Q x).mp hx.2
      exact ⟨(mem_unitaryFixedSubmodule π X z).mpr hzX,
        (mem_unitaryFixedSubmodule π Y z).mpr hzY⟩
end SoficGroups
