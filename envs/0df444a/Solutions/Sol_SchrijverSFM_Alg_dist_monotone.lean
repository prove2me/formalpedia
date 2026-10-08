-- Prove2me | solution 1 for SchrijverSFM.Alg.dist_monotone
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T04:20:28.339824+00:00
-- url     : https://prove2.me/submissions/c00c4587-b095-44e9-b23d-0ccad1aaad17

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting

open SchrijverSFM.Alg

private lemma dist_walk {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n)
    {m : ℕ} {v : Fin n} (h : walkLen f S m v) : dist f S v ≤ (m : ℕ∞) :=
  iInf_le_of_le m (iInf_le_of_le h le_rfl)

private lemma dist_arc {n : ℕ} (f : Finset (Fin n) → ℝ) (S : State n)
    {u v : Fin n} (h : arc S u v) : dist f S v ≤ dist f S u + 1 := by
  unfold SchrijverSFM.Alg.dist
  simp only [ENat.iInf_add]
  refine le_iInf fun m => le_iInf fun hm => ?_
  have hh := dist_walk f S (show walkLen f S (m + 1) v from ⟨u, hm, h⟩)
  simpa [SchrijverSFM.Alg.dist] using hh

theorem solution {n : ℕ} (f : Finset (Fin n) → ℝ)
    (S S' : State n) (t s : Fin n) (i : ℕ) (hstep : StepVia f S S' t s i) :
    ∀ v : Fin n, dist f S v ≤ dist f S' v := by
  classical
  obtain ⟨hvalid, _, ht, hs, σ, lam, hi, _, δ, ⟨Mv, hout⟩, hseg, _, _, hord⟩ := hstep
  have hσ : (σ, lam) ∈ S := List.mem_of_getElem? hi
  have hlam : 0 ≤ lam := (hvalid.2.1 _ hσ).le
  have hδ : 0 ≤ δ := hout.1
  obtain ⟨θ, hθ, _, hpoint, hpt, _⟩ := hseg
  have hpos : posSet f S' ⊆ posSet f S := by
    intro v hv
    have hvp : 0 < point f S' v := by simpa [posSet] using hv
    have hp : 0 < point f S v := by
      by_cases hvt : v = t
      · subst v
        exact (not_lt_of_ge hpt hvp).elim
      · have he := hpoint v
        by_cases hvs : v = s
        · subst v
          simp [chi, hvt] at he
          have hn : 0 ≤ θ * (lam * δ) := mul_nonneg hθ (mul_nonneg hlam hδ)
          linarith
        · rw [he] at hvp
          simpa [chi, hvt, hvs] using hvp
    simpa [posSet] using hp
  have hedge : ∀ v w : Fin n, arc S' v w → dist f S w ≤ dist f S v + 1 := by
    intro v w hvw
    obtain ⟨q, hq, hlt⟩ := hvw
    obtain ⟨L₁, L₂, hperm, hsub, _, hmove⟩ := hord
    have hqm : q.1 ∈ L₁ ++ L₂ := hperm.mem_iff.mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
    rcases List.mem_append.mp hqm with hq₁ | hq₂
    · have hqold := hsub.subset hq₁
      rcases List.mem_append.mp hqold with hqe | hqe
      · obtain ⟨p, hp, he⟩ := List.mem_map.mp hqe
        exact dist_arc f S ⟨p, List.eraseIdx_subset hp, he ▸ hlt⟩
      · have he : q.1 = σ := by
          split_ifs at hqe with hh
          · simpa using hqe
          · simp at hqe
        exact dist_arc f S ⟨(σ, lam), hσ, he ▸ hlt⟩
    · obtain ⟨u, hu, hm⟩ := hmove q.1 hq₂
      rcases (hm v w).mp hlt with ⟨hvu, hsw, hwu⟩ | ⟨hvwold, _⟩
      · subst v
        have hut : σ u ≤ σ t := (Finset.mem_filter.mp hu).2.2
        have hsu : σ s < σ u := (Finset.mem_filter.mp hu).2.1
        have hds : dist f S s ≤ dist f S u := by
          have hdu : dist f S t ≤ dist f S u + 1 := by
            rcases lt_or_eq_of_le hut with hut | hut
            · exact dist_arc f S ⟨(σ, lam), hσ, hut⟩
            · have he : u = t := σ.injective hut
              subst u
              exact le_self_add
          rw [← hs.2.1] at hdu
          exact (ENat.add_le_add_iff_right (by simp)).mp hdu
        have hdw : dist f S w ≤ dist f S s + 1 := by
          rcases lt_or_eq_of_le hsw with hsw | hsw
          · exact dist_arc f S ⟨(σ, lam), hσ, hsw⟩
          · have he : s = w := σ.injective hsw
            subst w
            exact le_self_add
        exact hdw.trans (add_le_add hds le_rfl)
      · exact dist_arc f S ⟨(σ, lam), hσ, hvwold⟩
  intro v
  unfold SchrijverSFM.Alg.dist
  refine le_iInf fun m => le_iInf fun hm => ?_
  have hbound : ∀ (m : ℕ) (v : Fin n), walkLen f S' m v → dist f S v ≤ (m : ℕ∞) := by
    intro m
    induction m with
    | zero =>
      intro v hv
      exact dist_walk f S (hpos hv)
    | succ m ih =>
      intro v hv
      obtain ⟨w, hw, ha⟩ := hv
      have hh := (hedge w v ha).trans (add_le_add (ih w hw) (show (1 : ℕ∞) ≤ 1 from le_rfl))
      simpa using hh
  exact hbound m v hm

#print axioms solution
