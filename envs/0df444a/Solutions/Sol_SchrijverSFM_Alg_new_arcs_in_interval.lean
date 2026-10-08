-- Prove2me | solution 1 for SchrijverSFM.Alg.new_arcs_in_interval
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:22:42.262087+00:00
-- url     : https://prove2.me/submissions/25e5d6de-17e0-42d5-9039-50dedb2a7400

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

open SchrijverSFM.Alg NonmonotoneSubmod.Shared

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ)
    (S S' : State n) (t s : Fin n) (i : ℕ) (hstep : StepVia f S S' t s i)
    (σ₁ : Equiv.Perm (Fin n)) (lam₁ : ℝ) (hi : S[i]? = some (σ₁, lam₁)) :
    ∀ v w : Fin n, arc S' v w → ¬ arc S v w →
      σ₁ s ≤ σ₁ w ∧ σ₁ w < σ₁ v ∧ σ₁ v ≤ σ₁ t := by
  classical
  obtain ⟨hvalid, hcase, ht, hs, σ, lam, hidx, hmax, δ, hsub, hseg, hvalid', hlen, hnew⟩ := hstep
  have heq : (σ, lam) = (σ₁, lam₁) := Option.some.inj (hidx.symm.trans hi)
  have heσ := congrArg Prod.fst heq
  have helam := congrArg Prod.snd heq
  dsimp only at heσ helam
  subst σ
  subst lam
  obtain ⟨L₁, L₂, hperm, hperm₁, hnodup, hmoved⟩ := hnew
  have hσ : (σ₁, lam₁) ∈ S := List.mem_of_getElem? hi
  intro v w harc hn
  obtain ⟨q, hq, hlt⟩ := harc
  have hmem : q.1 ∈ L₁ ++ L₂ := hperm.mem_iff.mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
  rcases List.mem_append.mp hmem with hmem | hmem
  · have hmem' := hperm₁.subset hmem
    rcases List.mem_append.mp hmem' with hold | hold
    · obtain ⟨p, hp, he⟩ := List.mem_map.mp hold
      exact (hn ⟨p, List.mem_of_mem_eraseIdx hp, he ▸ hlt⟩).elim
    · have he : q.1 = σ₁ := by
        split_ifs at hold <;> simp_all
      exact (hn ⟨(σ₁, lam₁), hσ, he ▸ hlt⟩).elim
  · obtain ⟨u, hu, hmove⟩ := hmoved q.1 hmem
    have hh := (hmove v w).mp hlt
    rcases hh with ⟨rfl, hsw, hwv⟩ | ⟨hvw, _⟩
    · exact ⟨hsw, hwv, (Finset.mem_filter.mp hu).2.2⟩
    · exact (hn ⟨(σ₁, lam₁), hσ, hvw⟩).elim

#print axioms solution
