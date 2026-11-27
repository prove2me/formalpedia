-- Prove2me | solution 1 for SelfAdaptingFNR.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-26T22:50:58.057115+00:00
-- url     : https://prove2.me/submissions/202a87e0-440a-43d6-a3c6-27d4e685db06

import Mathlib
import Definitions.Def_SelfAdaptingFNR_slackNetwork

open scoped Classical

open SelfAdaptingFNR

variable {J K T : ℕ}

/-- The 0th layer of the cumulative slack is `b` (the sum over `{j : Fin J | j < 0}` is empty). -/
theorem sv_zero (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (k : Fin K) :
    M.slackValue t s a 0 k = M.b k := by
  simp [WDP.slackValue]

namespace P2MHole01_3c3bf453
theorem solution {J K T : ℕ} (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
  (a : (j : Fin J) → M.Act t j) (j : Fin J) (k : Fin K) :
  M.slackValue t s a j.succ k = M.slackValue t s a j.castSucc k - M.C t k j (s j) (a j) := by
  simp only [WDP.slackValue]
  have : Finset.univ.filter (fun j' : Fin J => (j' : ℕ) < (j.succ : ℕ)) =
      insert j (Finset.univ.filter (fun j' : Fin J => (j' : ℕ) < (j.castSucc : ℕ))) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.coe_castSucc, Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp)]
  ring
end P2MHole01_3c3bf453

/-- The cumulative slack advances by one summand per layer:
`u_{t,j+1} = u_{t,j} − C_{t,k,j}(s_j, a_j)`. -/
theorem sv_succ (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (j : Fin J) (k : Fin K) :
    M.slackValue t s a j.succ k = M.slackValue t s a j.castSucc k - M.C t k j (s j) (a j) := by
  (first | exact P2MHole01_3c3bf453.solution M t s a j k | (apply P2MHole01_3c3bf453.solution <;> assumption))

/-- At the final layer `i = J` the filter `j < J` is all of `Fin J`, so the cumulative slack
is `b_k − ∑_j C_{t,k,j}(s_j, a_j)` (the full sum). -/
theorem sv_last (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (k : Fin K) :
    M.slackValue t s a (Fin.last J) k = M.b k - ∑ j, M.C t k j (s j) (a j) := by
  simp only [WDP.slackValue]
  rw [Finset.filter_true_of_mem (fun j _ => by simp)]

namespace P2MHole02_dc63b64a
/-- At layer `j.succ` the filter of `slackValue` gains exactly the index `j`, so the
cumulative slack drops by the cost `C_{t,k,j}(s_j, a_j)` componentwise in `k`. -/
theorem slackValue_succ {J K T : ℕ} (M : WDP J K T) (t : ℕ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (j : Fin J) :
    M.slackValue t s a j.succ = fun k => M.slackValue t s a j.castSucc k - M.C t k j (s j) (a j) := by
  funext k
  simp only [WDP.slackValue]
  have : Finset.univ.filter (fun j' : Fin J => (j' : ℕ) < (j.succ : ℕ)) =
      insert j (Finset.univ.filter (fun j' : Fin J => (j' : ℕ) < (j.castSucc : ℕ))) := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]; omega
  rw [this, Finset.sum_insert (by simp)]; ring

theorem solution {J K T : ℕ} (M : WDP J K T) (t : ℕ) (u : Fin K → Fin (J + (1 : ℕ)) → ℝ)
  (s : (j : Fin J) → M.S t j) (a : (j : Fin J) → M.Act t j) (h : (u, s, a) ∈ M.slackSet t) (k : Fin K)
  (i : Fin (J + (1 : ℕ))) : u k i = M.slackValue t s a i k := by
  obtain ⟨hA, hb, hc, hd⟩ := h
  dsimp only at hb hc hd
  induction i using Fin.induction with
  | zero =>
    rw [hb k, sv_zero M t s a k]
  | succ j ih =>
    rw [hc k j, ih, slackValue_succ M t s a j]
end P2MHole02_dc63b64a

-- riskiest
/-- Chain uniqueness (p.ec5): any `u` satisfying the slack-chain clauses of `𝓕^V_t` is forced,
layer by layer, to equal the cumulative slack vector `slackValue`. -/
theorem chain_eq_slackValue (M : WDP J K T) (t : ℕ)
    (u : Fin K → Fin (J + 1) → ℝ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (h : (u, s, a) ∈ M.slackSet t) (k : Fin K) (i : Fin (J + 1)) :
    u k i = M.slackValue t s a i k := by
  (first | exact P2MHole02_dc63b64a.solution M t u s a h k i | (apply P2MHole02_dc63b64a.solution <;> assumption))

/-- Direction `⊆`: any triple `(u, s, a)` of `𝓕^V_t` has a feasible pair: component-feasibility
is clause 1, and the linking constraint is the final-slack clause 4 with the chain uniqueness. -/
theorem feasible_of_slackSet (M : WDP J K T) (t : ℕ)
    (u : Fin K → Fin (J + 1) → ℝ) (s : (j : Fin J) → M.S t j)
    (a : (j : Fin J) → M.Act t j) (h : (u, s, a) ∈ M.slackSet t) :
    (s, a) ∈ M.feasiblePairs t := by
  simp only [WDP.slackSet, WDP.feasiblePairs] at h ⊢
  have hlink : ∀ k, ∑ j, M.C t k j (s j) (a j) ≤ M.b k := by
    intro k
    have hlast : 0 ≤ u k (Fin.last J) := h.2.2.2 k
    rw [chain_eq_slackValue M t u s a h k (Fin.last J), sv_last M t s a k] at hlast
    linarith
  exact ⟨h.1, hlink⟩

/-- Direction `⊇`: for a feasible pair `(s, a)`, the cumulative slack vector `u k i = slackValue
t s a i k` satisfies all four clauses of `𝓕^V_t`. -/
theorem slackValue_in_slackSet (M : WDP J K T) (t : ℕ)
    (p : ((j : Fin J) → M.S t j) × ((j : Fin J) → M.Act t j)) (hp : p ∈ M.feasiblePairs t) :
    ((fun k i => M.slackValue t p.1 p.2 i k), p.1, p.2) ∈ M.slackSet t := by
  simp only [WDP.feasiblePairs, WDP.slackSet] at hp ⊢
  refine ⟨hp.1, fun k => sv_zero M t p.1 p.2 k, fun k j => sv_succ M t p.1 p.2 j k, fun k => ?_⟩
  show 0 ≤ M.slackValue t p.1 p.2 (Fin.last J) k
  rw [sv_last M t p.1 p.2 k]
  linarith [hp.2 k]

/-- **Proposition 1 (Slack reformulation of `𝓕_t`)**, Nadarajah & Cire, *Self-Adapting Network
Relaxations for Weakly Coupled MDPs*, SSRN 4081430 (Aug. 2023), §3.1, pp.11–12 (PDF 11–12):
for any `t ∈ 𝒯`, `𝓕_t = {(s,a) | ∃ u such that (u,s,a) belongs to 𝓕^V_t}`.

**Formalization Note.** `𝓕^V_t` is `WDP.slackSet`, in which `a` ranges over the component action
sets `×ⱼ 𝒜_{t,j}(sⱼ)` rather than the printed `𝒜_t(s)`; with the printed set the statement follows
from this one (generalization). The printed "∃ v" is read as "∃ u", the bound variable of the
set (typo). -/
theorem solution {J K T : ℕ} (M : WDP J K T) (t : ℕ) (ht : t < T) :
    M.feasiblePairs t = {p | ∃ u : Fin K → Fin (J + 1) → ℝ, (u, p.1, p.2) ∈ M.slackSet t} := by
  ext p
  simp only [WDP.feasiblePairs]
  constructor
  · rintro ⟨hA, hC⟩
    exact ⟨fun k i => M.slackValue t p.1 p.2 i k, slackValue_in_slackSet M t p ⟨hA, hC⟩⟩
  · rintro ⟨u, hu⟩
    exact feasible_of_slackSet M t u p.1 p.2 hu
