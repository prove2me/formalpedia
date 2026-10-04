-- Prove2me | solution 1 for ProcessingNetworks.FeedforwardStability.workload_derivative_nonidling
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:09:11.965466+00:00
-- url     : https://prove2.me/submissions/84a04f0e-fce4-4a70-90f8-8e6486d75941

import Mathlib
import Definitions.Def_ProcessingNetworks_FeedforwardStability_QueueingNetworkData
import Definitions.Def_ProcessingNetworks_FeedforwardStability_WorkloadOperator
import Definitions.Def_ProcessingNetworks_FeedforwardStability_NonIdling

namespace ProcessingNetworks.FeedforwardStability

theorem workload_derivative_nonidling_core {I K : ℕ} (dat : QueueingNetworkData I K)
    (Q : Matrix (Fin I) (Fin I) ℝ) (hQ : IsRoutingInverse dat.P Q)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hsol : IsFluidModelSolutionQN dat Dh Fh Th Zh)
    (k : Fin K) (s : ℝ) (hs : 0 ≤ s) :
    ∑ i ∈ poolBuffers dat k, Th s i =
      workloadOperator dat Q (Zh 0) k + workloadOperator dat Q dat.lam k * s
        - workloadOperator dat Q (Zh s) k := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := hsol
  have hZ : Zh s = Zh 0 + s • dat.lam - (1 - dat.P.transpose).mulVec (Fh s) := by
    ext i
    rw [h1 s hs i, h3 s hs i]
    simp [Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    ring
  have hQZ : Q.mulVec (Zh s) = Q.mulVec (Zh 0) + s • Q.mulVec dat.lam - Fh s := by
    rw [hZ, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      hQ.1, Matrix.one_mulVec]
  unfold workloadOperator
  rw [hQZ, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← h4 s hs i]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

end ProcessingNetworks.FeedforwardStability

open ProcessingNetworks.FeedforwardStability

theorem solution
    {I K : ℕ} (dat : QueueingNetworkData I K) (Q : Matrix (Fin I) (Fin I) ℝ)
    (hQ : IsRoutingInverse dat.P Q)
    (Dh Fh Th Zh : ℝ → Fin I → ℝ) (hni : IsNonIdlingSolution dat Dh Fh Th Zh)
    (k : Fin K) (t : ℝ) (ht : 0 < t) (hz : 0 < ∑ i ∈ poolBuffers dat k, Zh t i) :
    ∀ d : ℝ, HasDerivAt (fun s => workloadOperator dat Q (Zh s) k) d t →
      d = workloadOperator dat Q dat.lam k - dat.b k := by
  intro d hd
  have hg : HasDerivAt (fun s => workloadOperator dat Q (Zh 0) k +
      workloadOperator dat Q dat.lam k * s - workloadOperator dat Q (Zh s) k)
      (workloadOperator dat Q dat.lam k - d) t := by
    have := ((hasDerivAt_id t).const_mul (workloadOperator dat Q dat.lam k)).const_add
      (workloadOperator dat Q (Zh 0) k)
    have h2 := this.sub hd
    rw [mul_one] at h2
    exact h2
  have hT : HasDerivAt (fun s => ∑ i ∈ poolBuffers dat k, Th s i)
      (workloadOperator dat Q dat.lam k - d) t := by
    refine hg.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds ht] with s hs
    exact workload_derivative_nonidling_core dat Q hQ Dh Fh Th Zh hni.1 k s hs.le
  have := hni.2 k t ht hz _ hT
  linarith


