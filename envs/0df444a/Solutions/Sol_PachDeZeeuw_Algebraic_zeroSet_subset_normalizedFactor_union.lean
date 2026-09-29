-- Prove2me | solution 1 for PachDeZeeuw.Algebraic.zeroSet_subset_normalizedFactor_union
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-17T01:40:00.484846+00:00
-- url     : https://prove2.me/submissions/56de9221-5b8a-4718-ac49-b1b8020ec56e

import Mathlib
import Definitions.Def_PdzPrelim

open EuclideanGeometry
open scoped Topology
open PachDeZeeuw.Algebraic
open PachDeZeeuw.Algebraic.PlaneCurve

open PachDeZeeuw.Algebraic in
theorem solution {p : MvPolynomial (Fin 2) ℝ} (hp0 : p ≠ 0) :
    PlaneCurveZeroSet p ⊆
      ⋃ h ∈ (UniqueFactorizationMonoid.normalizedFactors p).toFinset,
        PlaneCurveZeroSet h := by
  classical
  intro z hz
  let s : Multiset (MvPolynomial (Fin 2) ℝ) := UniqueFactorizationMonoid.normalizedFactors p
  have hs : Associated s.prod p := by
    simpa [s] using (UniqueFactorizationMonoid.prod_normalizedFactors hp0)
  have hsp : Associated (MvPolynomial.eval (fun i => z i) s.prod)
      (MvPolynomial.eval (fun i => z i) p) := by
    exact Associated.map (MvPolynomial.eval (fun i => z i)) hs
  have hzero : MvPolynomial.eval (fun i => z i) s.prod = 0 := by
    exact (hsp.eq_zero_iff).2 hz
  have hzero' :
      (s.map (fun h : MvPolynomial (Fin 2) ℝ => MvPolynomial.eval (fun i => z i) h)).prod = 0 := by
    simpa [s, map_multiset_prod] using hzero
  have hmem : 0 ∈ s.map (fun h : MvPolynomial (Fin 2) ℝ => MvPolynomial.eval (fun i => z i) h) := by
    simpa using (Multiset.prod_eq_zero_iff.mp hzero')
  rcases Multiset.mem_map.mp hmem with ⟨h, hh, hhz⟩
  refine Set.mem_iUnion.2 ?_
  refine ⟨h, ?_⟩
  refine Set.mem_iUnion.2 ?_
  refine ⟨by simpa only [Multiset.mem_toFinset, s] using hh, ?_⟩
  simpa [PlaneCurveZeroSet] using hhz
