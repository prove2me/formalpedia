-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P22.abort_factorization
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:38:48.459192+00:00
-- url     : https://prove2.me/submissions/7d6f8087-84b8-4da6-9a1f-7df4fb4093bb

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P22

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Advance50.P47
  (Box IsCorrelation IsNoSignaling HasLocalModel correlationMixture prBox)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Gap48.P25 (classicalMI)

open QAlgorithms.Papers.Independent.Intakethird100.P22 in
theorem solution {K T E Z : Type}
    [Fintype K] [Fintype T] [Fintype E] [Fintype Z]
    [Nonempty K] [Nonempty T] [Nonempty E] [Nonempty Z] (r : KeyOutput K T E Z) :
    cdDistance (withAbort r.abortProbability r.abort r.pass)
      (withAbort r.abortProbability r.abort (idealCDKey r.pass)) = securityError r := by
  have h1r : 0 ≤ 1 - r.abortProbability := by linarith [r.abort_le_one]
  have hlin : ∀ (g : CDObservation (K × K × T) E Z) (j : Fin g.size),
      g.apply (withAbort r.abortProbability r.abort r.pass) j -
        g.apply (withAbort r.abortProbability r.abort (idealCDKey r.pass)) j =
      (1 - r.abortProbability) * (g.apply r.pass j - g.apply (idealCDKey r.pass) j) := by
    intro g j
    rw [← sub_eq_zero]
    simp only [CDObservation.apply, withAbort, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun z _ =>
      Finset.sum_eq_zero (fun e _ => by ring)))
  have hval : ∀ g : CDObservation (K × K × T) E Z,
      (1 / 2 : ℝ) * ∑ j, |g.apply (withAbort r.abortProbability r.abort r.pass) j -
        g.apply (withAbort r.abortProbability r.abort (idealCDKey r.pass)) j| =
      (1 - r.abortProbability) *
        ((1 / 2 : ℝ) * ∑ j, |g.apply r.pass j - g.apply (idealCDKey r.pass) j|) := by
    intro g
    simp_rw [hlin g, abs_mul, abs_of_nonneg h1r]
    rw [← Finset.mul_sum]
    ring
  have hset : {v | ∃ g : CDObservation (K × K × T) E Z,
      v = (1 / 2 : ℝ) * ∑ j, |g.apply (withAbort r.abortProbability r.abort r.pass) j -
        g.apply (withAbort r.abortProbability r.abort (idealCDKey r.pass)) j|} =
      (1 - r.abortProbability) • {v | ∃ g : CDObservation (K × K × T) E Z,
        v = (1 / 2 : ℝ) * ∑ j, |g.apply r.pass j - g.apply (idealCDKey r.pass) j|} := by
    ext v
    simp only [Set.mem_setOf_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨_, ⟨g, rfl⟩, (hval g).symm⟩
    · rintro ⟨w, ⟨g, rfl⟩, rfl⟩
      exact ⟨g, (hval g).symm⟩
  unfold securityError cdDistance
  rw [hset, Real.sSup_smul_of_nonneg h1r, smul_eq_mul]

end
