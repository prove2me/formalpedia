-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P24.twisting_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T07:00:53.881981+00:00
-- url     : https://prove2.me/submissions/c2211610-d795-40d8-ad40-d1c2013c532c

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P24

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

open Finset

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Accepted declarations are imported rather than redeclared locally.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P04 (bellProjector)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart negativePart)

open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

open QAlgorithms.Papers.Independent.Information100.P54 (relativeEntropyBits relativeEntanglement)

/-- PDF pp.5–6, Theorem 1: the SAME unit purification is transported by twisting. -/
theorem solution {d : ℕ} [NeZero d] {S T E : Type*}
    [Fintype S] [Fintype T] [Fintype E] [Nonempty S] [Nonempty T] [Nonempty E]
    (psi : EuclideanSpace ℂ ((Key d × (S × T)) × E)) (hpsi : IsState psi)
    (U : Key d → Matrix.unitaryGroup (S × T) ℂ) :
    associatedCCQ (twistPurification U psi) = associatedCCQ psi := by
  have hU : ∀ k (s1 s2 : S × T), ∑ s, conj ((U k : Op (S × T)) s s2) * (U k : Op (S × T)) s s1 =
      if s2 = s1 then 1 else 0 := by
    intro k s1 s2
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.mp (U k).2) s2) s1
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] at h
    simpa [Matrix.star_apply] using h
  ext a b
  simp only [associatedCCQ, twistPurification]
  split_ifs with hab
  · simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    have : ∀ s1 s2 : S × T, ∑ s, (U a.1 : Op (S × T)) s s1 * psi ((a.1, s1), a.2) *
        (conj ((U a.1 : Op (S × T)) s s2) * conj (psi ((a.1, s2), b.2))) =
        (if s2 = s1 then 1 else 0) * (psi ((a.1, s1), a.2) * conj (psi ((a.1, s2), b.2))) := by
      intro s1 s2
      rw [← hU a.1 s1 s2, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun s _ => by ring)
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    simp_rw [this, ite_mul, one_mul, zero_mul]
    simp
  · rfl
