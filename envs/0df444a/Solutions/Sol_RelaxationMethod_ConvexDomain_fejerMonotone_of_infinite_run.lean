-- Prove2me | solution 1 for RelaxationMethod.ConvexDomain.fejerMonotone_of_infinite_run
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:05:31.900621+00:00
-- url     : https://prove2.me/submissions/ddf7a005-dffb-4ec0-a24e-8a6f07d36f05

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
import Definitions.Def_RelaxationMethod_Shared_FejerMonotone

namespace RelaxationMethod.ConvexDomain

theorem aux_fejRun_inner_le {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ A) (p q : EuclideanSpace ℝ (Fin n)) (hq : IsNearestPoint A p q) :
    ∀ a ∈ A, inner ℝ (p - q) (a - q) ≤ 0 := by
  obtain ⟨hqA, hmin⟩ := hq
  have : Nonempty A := ⟨⟨q, hqA⟩⟩
  refine (norm_eq_iInf_iff_real_inner_le_zero hconv hqA).1 ?_
  apply le_antisymm
  · refine le_ciInf (fun w => ?_)
    have := hmin w.1 w.2
    simpa [dist_eq_norm] using this
  · have hb : BddBelow (Set.range fun w : A => ‖p - (w : EuclideanSpace ℝ (Fin n))‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨w, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hb ⟨q, hqA⟩

theorem aux_fejRun_step {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hconv : Convex ℝ A) (p q : EuclideanSpace ℝ (Fin n)) (hq : IsNearestPoint A p q)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ A) :
    dist (p + (2 : ℝ) • (q - p)) a ≤ dist p a := by
  have hin := aux_fejRun_inner_le A hconv p q hq a ha
  set u := p - q with hu
  set w := a - q with hw
  have h1 : p + (2 : ℝ) • (q - p) - a = -(u + w) := by
    rw [hu, hw]; module
  have h2 : p - a = u - w := by
    rw [hu, hw]; abel
  rw [dist_eq_norm, dist_eq_norm, h1, h2, norm_neg]
  have e1 := norm_add_sq_real u w
  have e2 := norm_sub_sq_real u w
  have hsq : ‖u + w‖ ^ 2 ≤ ‖u - w‖ ^ 2 := by nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

end RelaxationMethod.ConvexDomain

open RelaxationMethod.ConvexDomain

theorem solution {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsImageRun A p) (hinf : ∀ ν : ℕ, p ν ∉ A) :
    RelaxationMethod.Shared.IsFejerMonotone A p := by
  refine ⟨hinf, fun ν => ?_, fun a ha ν => ?_⟩
  · obtain ⟨q, hq, heq⟩ := hrun ν (hinf ν)
    intro h
    rw [← h] at heq
    have : q - p ν = 0 := by
      have h2 : (2 : ℝ) • (q - p ν) = 0 := by
        have := congrArg (fun x => x - p ν) heq
        simpa using this.symm
      exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
    have hqp : q = p ν := sub_eq_zero.1 this
    exact hinf ν (hqp ▸ hq.1)
  · obtain ⟨q, hq, heq⟩ := hrun ν (hinf ν)
    rw [heq]
    exact aux_fejRun_step A hconv (p ν) q hq a ha
