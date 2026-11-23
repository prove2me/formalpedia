-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.IsFrame.relIndex_span_frame_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:15.240806+00:00
-- url     : https://prove2.me/submissions/ae48458d-1a51-4f87-a985-9559c9425641

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_ConjSymm
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_DegStA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open NumberField Module
open scoped ComplexOrder Matrix
variable {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace ReciprocityTheory.GeometryOfNumbersTheory
namespace IsFrame
theorem _root_.solution {E : Submodule (𝓞 K) V} (hE : E.FG) {r : ℕ} {v : Fin r → V}
    (hv : IsFrame K E v) :
    (Submodule.span (𝓞 K) (Set.range v)).toAddSubgroup.relIndex E.toAddSubgroup ≠ 0 := by
  classical
  set S := Submodule.span (𝓞 K) (Set.range v) with hSdef
  set H := S.toAddSubgroup.addSubgroupOf E.toAddSubgroup with hH
  have : Module.Finite (𝓞 K) E := Module.Finite.iff_fg.mpr hE
  have : Module.Finite ℤ E := Module.Finite.trans (𝓞 K) E
  have hfg : AddGroup.FG E := Module.Finite.iff_addGroup_fg.mp inferInstance
  have hfg' : AddGroup.FG E.toAddSubgroup := hfg
  have : Module.Finite ℤ E.toAddSubgroup := Module.Finite.iff_addGroup_fg.mpr hfg'
  have : Module.Finite ℤ (E.toAddSubgroup ⧸ H) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' H).toIntLinearMap
      (QuotientAddGroup.mk'_surjective H)
  have : Finite (E.toAddSubgroup ⧸ H) := by
    apply Module.finite_of_fg_torsion
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hv.2.2 x.2)
      obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
      have hd : ∀ i, IsIntegral ℤ (y • c i) := fun i => hy _ (Finset.mem_image_of_mem c (Finset.mem_univ i))
      let d : Fin r → 𝓞 K := fun i => ⟨y • c i, hd i⟩
      refine ⟨⟨y, mem_nonZeroDivisors_of_ne_zero hy0⟩, ?_⟩
      have hmem : (y • (x : V)) ∈ S := by
        have : y • (x : V) = ∑ i, d i • v i := by
          rw [← hc, Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← algebraMap_smul K (d i) (v i), ← smul_assoc]
          rfl
        rw [this]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      show (y : ℤ) • (QuotientAddGroup.mk x : E.toAddSubgroup ⧸ H) = 0
      rw [← QuotientAddGroup.mk_zsmul, QuotientAddGroup.eq_zero_iff]
      exact hmem
  exact AddSubgroup.index_ne_zero_of_finite
end IsFrame
end ReciprocityTheory.GeometryOfNumbersTheory
