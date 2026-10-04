-- Prove2me | solution 1 for ProcessingNetworks.ProportionalFairness.pf_maximally_stable_for_bws
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:13:27.346499+00:00
-- url     : https://prove2.me/submissions/ae32afcf-b947-404f-954a-b96397c6c974

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedFluidModel
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore
import Definitions.Def_ProcessingNetworks_ProportionalFairness_BWSAndQueueing

open ProcessingNetworks.ProportionalFairness

theorem solution
    {I K L : ℕ} {Policy : Type*} (PolicyStable : Policy → BWSNetworkData I K → Prop)
    (pf : Policy) (grp : Fin I → Fin L) (TildeAllocSet : Set (Fin L → ℝ))
    (hdom : IsPFDomain TildeAllocSet)
    (hpf : ∀ dat : BWSNetworkData I K,
      PolicyStable pf dat ↔
        PFFluidStable (⟨dat.lam, dat.m, dat.hm, 0, grp, TildeAllocSet⟩ : PFUnitaryNetworkData I L))
    (hload_iff : ∀ dat : BWSNetworkData I K,
      BWSLoadCondition dat ↔
        ∃ a ∈ TildeAllocSet, ∀ ℓ, groupAggregate grp (fun i => dat.lam i * dat.m i) ℓ < a ℓ)
    (hnecessary : ∀ dat : BWSNetworkData I K, ¬ BWSLoadCondition dat → ∀ p, ¬ PolicyStable p dat)
    (dat : BWSNetworkData I K) :
    (BWSLoadCondition dat → PolicyStable pf dat) ∧
    (¬ BWSLoadCondition dat → ∀ p, ¬ PolicyStable p dat) := by
  refine ⟨fun hload => ?_, hnecessary dat⟩
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    rcases Nat.eq_zero_or_pos I with hI | hI
    · subst hI
      exact (hpf dat).mpr ⟨1, one_pos, fun _ _ _ _ _ _ _ => funext fun i => i.elim0⟩
    · exfalso
      let i0 : Fin I := ⟨0, hI⟩
      obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).mp hdom.1
      let lam' : Fin I → ℝ := fun i => if i = i0 then (|R| + 1) / dat.m i0 else 0
      let dat' : BWSNetworkData I 0 := ⟨lam', dat.m, dat.hm, dat.Amat, dat.bvec⟩
      obtain ⟨a, ha, hlt⟩ := (hload_iff dat').mp (fun k => k.elim0)
      have h1 := hlt (grp i0)
      have hagg : groupAggregate grp (fun i => dat'.lam i * dat'.m i) (grp i0) = |R| + 1 := by
        unfold groupAggregate
        rw [Finset.sum_eq_single i0]
        · simp only [dat', lam', if_pos rfl]
          field_simp [(dat.hm i0).ne']
        · intro b _ hb
          simp [dat', lam', hb]
        · intro h; simp at h
      rw [hagg] at h1
      have h2 : ‖a‖ ≤ R := hR a ha
      have h3 : |a (grp i0)| ≤ ‖a‖ := by
        have := norm_le_pi_norm a (grp i0)
        rwa [Real.norm_eq_abs] at this
      have := le_abs_self (a (grp i0))
      have := le_abs_self R
      linarith
  · exfalso
    let k0 : Fin K := ⟨0, hK⟩
    let d1 : BWSNetworkData I K := ⟨dat.lam, dat.m, dat.hm, 0, fun _ => 1⟩
    let d2 : BWSNetworkData I K := ⟨dat.lam, dat.m, dat.hm, 0, fun _ => -1⟩
    have h1 := (hload_iff d1).mp (fun k => by simp [d1])
    have h2 := (hload_iff d2).mpr h1 k0
    simp [d2] at h2
    linarith


