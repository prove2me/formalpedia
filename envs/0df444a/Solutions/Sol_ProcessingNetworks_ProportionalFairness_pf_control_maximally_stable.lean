-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.pf_control_maximally_stable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:58:48.768577+00:00
-- url     : https://prove2.me/submissions/f2c728ff-6625-491d-8a4d-aaab82b616f8

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_BWSAndQueueing
import Definitions.Def_ProcessingNetworks_ProportionalFairness_MaximalStability



namespace ProcessingNetworks.ProportionalFairness

lemma pfmx_no_solution {I L : ℕ} (hI : 0 < I) (dat : PFUnitaryNetworkData I L)
    (hlam : ∀ i, dat.lam i = -1)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1)
    (Ah Dh Th Zh : ℝ → Fin I → ℝ) : ¬ IsPFFluidModelSolution dat Ah Dh Th Zh := by
  rintro ⟨hZ, hZnn, hA, hD, ⟨hT0, hTmono, _⟩, _⟩
  set t : ℝ := ∑ i, Zh 0 i + 1 with ht
  have hs0 : 0 ≤ ∑ i, Zh 0 i := Finset.sum_nonneg fun i _ => hZnn 0 le_rfl i
  have htnn : 0 ≤ t := by linarith
  have hDnn : ∀ k, 0 ≤ Dh t k := by
    intro k
    rw [hD t htnn k]
    have : Th 0 k ≤ Th t k := hTmono htnn k
    rw [hT0] at this
    exact div_nonneg (by simpa using this) (dat.hm k).le
  have hsum : ∑ i, Zh t i = ∑ i, Zh 0 i + ∑ i, (dat.lam i * t)
      + (∑ k, Dh t k * ∑ i, dat.P k i - ∑ i, Dh t i) := by
    rw [hZ t htnn]
    simp only [hA t htnn, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_comm (f := fun i k => dat.P k i * Dh t k)]
    simp only [mul_comm]
    ring
  have hle : ∑ k, Dh t k * ∑ i, dat.P k i - ∑ i, Dh t i ≤ 0 := by
    rw [sub_nonpos]
    apply Finset.sum_le_sum
    intro k _
    have := mul_le_mul_of_nonneg_left (hP_rowsum k) (hDnn k)
    linarith
  have hlamsum : ∑ i, (dat.lam i * t) = -(I : ℝ) * t := by
    simp [hlam]
  have hpos : 0 ≤ ∑ i, Zh t i := Finset.sum_nonneg fun i _ => hZnn t htnn i
  have hI1 : (1 : ℝ) ≤ I := by exact_mod_cast hI
  nlinarith

lemma pfmx_stable_neg {I L : ℕ} (hI : 0 < I) (dat : PFUnitaryNetworkData I L)
    (hlam : ∀ i, dat.lam i = -1)
    (hP_nonneg : ∀ i j, 0 ≤ dat.P i j) (hP_rowsum : ∀ i, ∑ j, dat.P i j ≤ 1) :
    PFFluidStable dat :=
  ⟨1, one_pos, fun Ah Dh Th Zh h =>
    (pfmx_no_solution hI dat hlam hP_nonneg hP_rowsum Ah Dh Th Zh h).elim⟩

theorem pf_control_maximally_stable_core
    {I L : ℕ} {Policy : Type*} (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (grp : Fin I → Fin L) (TildeAllocSet : Set (Fin L → ℝ))
    (PolicyStable : Policy → (Fin I → ℝ) → Prop) (pf : Policy)
    (hfluid : ∀ lam : Fin I → ℝ,
      PFFluidStable (⟨lam, m, hm, P, grp, TildeAllocSet⟩ : PFUnitaryNetworkData I L) →
        PolicyStable pf lam)
    (hnn : ∀ lam ∈ StabilityRegion PolicyStable, ∀ i, 0 ≤ lam i) :
    IsMaximallyStable PolicyStable pf := by
  intro lam _
  apply hfluid
  rcases Nat.eq_zero_or_pos I with hI | hI
  · subst hI
    exact ⟨1, one_pos, fun _ _ _ _ _ _ _ => funext fun i => i.elim0⟩
  · exfalso
    have h := pfmx_stable_neg (L := L) hI ⟨fun _ => -1, m, hm, P, grp, TildeAllocSet⟩
      (fun _ => rfl) hP_nonneg hP_rowsum
    have hmem : (fun _ => (-1 : ℝ)) ∈ StabilityRegion PolicyStable := ⟨pf, hfluid _ h⟩
    have := hnn _ hmem ⟨0, hI⟩
    norm_num at this

theorem hlpps_core
    {I K : ℕ} {Policy : Type*} (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (server : Fin I → Fin K) (b : Fin K → ℝ) (hb : ∀ k, 0 < b k)
    (PolicyStable : Policy → (Fin I → ℝ) → Prop) (hlpps : Policy)
    (hfluid : ∀ lam : Fin I → ℝ,
      HLPPSFluidStable (⟨lam, m, hm, P, server, b, hb⟩ : QueueingNetworkDataHL I K) →
        PolicyStable hlpps lam)
    (hnn : ∀ lam ∈ StabilityRegion PolicyStable, ∀ i, 0 ≤ lam i) :
    IsMaximallyStable PolicyStable hlpps :=
  pf_control_maximally_stable_core (L := K) m hm P hP_nonneg hP_rowsum server
    {y : Fin K → ℝ | ∀ k, 0 ≤ y k ∧ y k ≤ b k} PolicyStable hlpps hfluid hnn

end ProcessingNetworks.ProportionalFairness

open ProcessingNetworks.ProportionalFairness


theorem solution
    {I L : ℕ} {Policy : Type*} (m : Fin I → ℝ) (hm : ∀ i, 0 < m i)
    (P : Matrix (Fin I) (Fin I) ℝ)
    (hP_nonneg : ∀ i j, 0 ≤ P i j) (hP_rowsum : ∀ i, ∑ j, P i j ≤ 1)
    (hP_transient : ∀ i j, Filter.Tendsto (fun n => (P ^ n) i j) Filter.atTop (nhds 0))
    (grp : Fin I → Fin L) (TildeAllocSet : Set (Fin L → ℝ)) (hdom : IsPFDomain TildeAllocSet)
    (alpha : (Fin I → ℝ) → (Fin I → ℝ))
    (halpha : ∀ lam, IsTotalArrivalRates
      (⟨lam, m, hm, P, grp, TildeAllocSet⟩ : PFUnitaryNetworkData I L) (alpha lam))
    (PolicyStable : Policy → (Fin I → ℝ) → Prop) (pf : Policy)
    (hfluid : ∀ lam : Fin I → ℝ,
      PFFluidStable (⟨lam, m, hm, P, grp, TildeAllocSet⟩ : PFUnitaryNetworkData I L) →
        PolicyStable pf lam)
    (hnecessary : ∀ lam ∈ StabilityRegion PolicyStable, (∀ i, 0 ≤ lam i) ∧
      ∃ a ∈ TildeAllocSet, ∀ ℓ, groupAggregate grp (fun i => alpha lam i * m i) ℓ < a ℓ) :
    IsMaximallyStable PolicyStable pf := by
  exact pf_control_maximally_stable_core m hm P hP_nonneg hP_rowsum grp TildeAllocSet PolicyStable pf hfluid (fun lam h => (hnecessary lam h).1)
