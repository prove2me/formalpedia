-- Prove2me | solution 1 for ProfiniteMeasure.ext_of_clopen_masses
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T05:28:45.72283+00:00
-- url     : https://prove2.me/submissions/674a3b80-557e-410d-ad5e-aaecc46c2c54

import Mathlib.NumberTheory.Padics.Measure.Basic
import Mathlib.Analysis.Normed.Field.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set Filter UniformSpace ContinuousMap TopologicalSpace

/-- Continuous abstract measures on a profinite space are determined by clopen masses. -/
theorem solution {X R : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [TotallyDisconnectedSpace X] [NormedField R]
    (μ ν : AbstractMeasure X R R)
    (h : ∀ U : Clopens X,
      μ ⟨(U : Set X).indicator (fun _ => (1 : R)),
        U.isClopen.continuous_indicator continuous_const⟩ =
      ν ⟨(U : Set X).indicator (fun _ => (1 : R)),
        U.isClopen.continuous_indicator continuous_const⟩) : μ = ν := by
  classical
  have hclosed : IsClosed {g : C(X,R) | μ g = ν g} :=
    isClosed_eq μ.continuous ν.continuous
  apply DFunLike.ext
  intro f
  apply hclosed.closure_subset
  rw [mem_closure_iff]
  intro W hWo hWf
  have hW := mem_nhds_uniformity_iff_right.mp (hWo.mem_nhds hWf)
  obtain ⟨J,hJ,hJ'⟩ := (hasBasis_compactConvergenceUniformity_of_compact).mem_iff.mp hW
  obtain ⟨n,U,v,hv⟩ := exists_finite_sum_const_indicator_approximation_of_mem_nhds_diagonal
    f (nhdsSet_diagonal_le_uniformity hJ)
  let e (i : Fin n) : C(X,R) :=
    ⟨(U i : Set X).indicator (fun _ => (1 : R)),
      (U i).isClopen.continuous_indicator continuous_const⟩
  let g := ∑ i : Fin n, v i • e i
  have hg : μ g = ν g := by
    simp only [g,map_sum,map_smul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => v i • z) (h (U i)))
  have hgp (x : X) : g x = ∑ i : Fin n, (U i : Set X).indicator (fun _ => v i) x := by
    simp only [g,ContinuousMap.sum_apply,ContinuousMap.smul_apply,e,ContinuousMap.coe_mk,smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ U i <;> simp [hx]
  have hG := Set.mem_of_subset_of_mem hJ' (a := (f,g))
  simp only [Set.mem_ofPred_eq,forall_const] at hG
  exact ⟨g,hG (by simpa only [hgp] using hv),hg⟩
