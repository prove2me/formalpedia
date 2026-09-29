-- Prove2me | solution 1 for RelaxationMethod.ConvexDomain.limit_mem_frontier
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:56:35.793844+00:00
-- url     : https://prove2.me/submissions/f89a74eb-124d-47af-bc1a-664b49d20308

import Mathlib
import Definitions.Def_RelaxationMethod_ConvexDomain_ImageProcess
open Filter Topology

namespace RelaxationMethod.ConvexDomain

theorem aux_lmf_midpoint {n : ℕ} (x q : EuclideanSpace ℝ (Fin n)) :
    q = x + (1/2 : ℝ) • ((x + (2 : ℝ) • (q - x)) - x) := by
  rw [add_sub_cancel_left, smul_smul]
  norm_num

end RelaxationMethod.ConvexDomain

open RelaxationMethod.ConvexDomain
open Filter Topology

theorem solution {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hbdd : Bornology.IsBounded A)
    (p : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsImageRun A p) (hinf : ∀ ν : ℕ, p ν ∉ A)
    (a : EuclideanSpace ℝ (Fin n)) (ha : Tendsto p atTop (𝓝 a)) :
    a ∈ A ∧ a ∈ frontier A := by
  have hq : ∀ ν, ∃ q, q ∈ A ∧ p (ν+1) = p ν + (2:ℝ) • (q - p ν) := fun ν => by
    obtain ⟨q, hq, h⟩ := hrun ν (hinf ν)
    exact ⟨q, hq.1, h⟩
  choose q hqA hqeq using hq
  have hqform : ∀ ν, q ν = p ν + (1/2 : ℝ) • (p (ν+1) - p ν) := by
    intro ν
    rw [hqeq ν]
    exact aux_lmf_midpoint (p ν) (q ν)
  have h1 : Tendsto (fun ν => p (ν+1)) atTop (𝓝 a) := ha.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun ν => p ν + (1/2:ℝ) • (p (ν+1) - p ν)) atTop
      (𝓝 (a + (1/2:ℝ) • (a - a))) := ha.add ((h1.sub ha).const_smul _)
  rw [sub_self, smul_zero, add_zero] at h2
  have hqlim : Tendsto q atTop (𝓝 a) := by
    have : q = fun ν => p ν + (1/2:ℝ) • (p (ν+1) - p ν) := funext hqform
    rw [this]; exact h2
  have haA : a ∈ A := hclosed.mem_of_tendsto hqlim (Eventually.of_forall hqA)
  refine ⟨haA, ?_⟩
  rw [frontier, hclosed.closure_eq]
  refine ⟨haA, fun hint => ?_⟩
  obtain ⟨N, hN⟩ := (ha.eventually (isOpen_interior.mem_nhds hint)).exists
  exact hinf N (interior_subset hN)
