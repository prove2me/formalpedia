-- Prove2me | solution 1 for PutermanMDP.MarkovPolicies.markovization
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:15:00.974807+00:00
-- url     : https://prove2.me/submissions/372aa206-fe6f-4899-a0d6-4bf667a989b3

import Mathlib
import Definitions.Def_PutermanMDP_MarkovPolicies_Model

open PutermanMDP.MarkovPolicies

theorem s225_bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [PMF.mem_support_iff, not_not] at ha
    rw [ha, zero_mul, zero_mul]

section Disint
variable {S : Type*} {B : S → Type*}

theorem s225_marg_apply (ν : PMF (Σ s, B s)) (s : S) :
    (ν.map Sigma.fst) s = ∑' b, ν ⟨s, b⟩ := by
  rw [PMF.map_apply, ENNReal.tsum_sigma']
  rw [tsum_eq_single s]
  · simp
  · intro s' hs'
    apply ENNReal.tsum_eq_zero.mpr
    intro b
    rw [if_neg]
    exact fun h => hs' h.symm

noncomputable def s225_cond [∀ s, Nonempty (B s)] (ν : PMF (Σ s, B s)) (s : S) : PMF (B s) :=
  if h : ∑' b, ν ⟨s, b⟩ = 0 then PMF.pure (Classical.arbitrary _)
  else PMF.normalize (fun b => ν ⟨s, b⟩) h (by
    rw [← s225_marg_apply]; exact PMF.apply_ne_top _ _)

theorem s225_disint [∀ s, Nonempty (B s)] (ν : PMF (Σ s, B s)) :
    ν = (ν.map Sigma.fst).bind (fun s => (s225_cond ν s).map (Sigma.mk s)) := by
  ext ⟨s0, b0⟩
  have key1 : ((s225_cond ν s0).map (Sigma.mk s0)) ⟨s0, b0⟩ = s225_cond ν s0 b0 := by
    rw [PMF.map_apply, tsum_eq_single b0]
    · exact if_pos rfl
    · intro c hc; exact if_neg (fun he => hc (sigma_mk_injective he).symm)
  have key2 : ∀ s, s ≠ s0 → ((s225_cond ν s).map (Sigma.mk s)) ⟨s0, b0⟩ = 0 := by
    intro s hs
    rw [PMF.map_apply]
    exact ENNReal.tsum_eq_zero.mpr (fun c => if_neg (fun he => hs (congrArg Sigma.fst he).symm))
  rw [PMF.bind_apply, tsum_eq_single s0]
  · rw [key1, s225_marg_apply]
    unfold s225_cond
    split_ifs with h
    · have : ν ⟨s0, b0⟩ ≤ ∑' b, ν ⟨s0, b⟩ := ENNReal.le_tsum (f := fun b => ν ⟨s0, b⟩) b0
      rw [h] at this ⊢
      rw [zero_mul]; exact le_antisymm this bot_le
    · rw [PMF.normalize_apply]
      have hT : ∑' b, ν ⟨s0, b⟩ ≠ ⊤ := by
        rw [← s225_marg_apply]; exact PMF.apply_ne_top _ _
      rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel h hT, mul_one]
  · intro s hs
    rw [key2 s hs, mul_zero]
end Disint

section MDP
variable {S A : Type*} (M : Model S A)

def s225_hsnd : History S A → S := fun h => h.2

noncomputable def s225_sig (π : HistoryPolicy M) (μ : PMF S) (n : ℕ) :
    PMF (Σ s : S, {a : A // a ∈ M.actions s}) :=
  (historyLaw M π μ n).bind (fun h => (π h).map (fun a => (⟨h.2, a⟩ : Σ s : S, {a : A // a ∈ M.actions s})))

theorem s225_sal_eq (π : HistoryPolicy M) (μ : PMF S) (n : ℕ) :
    stateActionLaw M π μ n = (s225_sig M π μ n).map (fun x => (x.1, x.2.val)) := by
  unfold stateActionLaw s225_sig
  refine Eq.trans ?_ (PMF.map_bind _ _ _).symm
  congr 1; funext h
  rw [PMF.map_comp]; rfl

theorem s225_succ_snd (π : HistoryPolicy M) (μ : PMF S) (n : ℕ) :
    (historyLaw M π μ (n + 1)).map s225_hsnd =
      (s225_sig M π μ n).bind (fun x => M.transition x.1 x.2) := by
  show ((historyLaw M π μ n).bind fun h =>
      (π h).bind fun a => (M.transition h.2 a).map fun j =>
        ((h.2, a.val) :: h.1, j)).map s225_hsnd = _
  unfold s225_sig
  refine (PMF.map_bind _ _ _).trans ?_
  refine Eq.trans ?_ (PMF.bind_bind _ _ _).symm
  congr 1; funext h
  refine (PMF.map_bind _ _ _).trans ?_
  refine Eq.trans ?_ (PMF.bind_map _ _ _).symm
  congr 1; funext a
  exact (PMF.map_comp _ _ _).trans (PMF.map_id _)

theorem s225_fst_marg (π : HistoryPolicy M) (μ : PMF S) (n : ℕ) :
    (s225_sig M π μ n).map Sigma.fst = (historyLaw M π μ n).map s225_hsnd := by
  unfold s225_sig
  refine (PMF.map_bind _ _ _).trans ?_
  show _ = (historyLaw M π μ n).bind (fun h => PMF.pure (s225_hsnd h))
  congr 1; funext h
  rw [PMF.map_comp]
  exact PMF.map_const _ _

theorem s225_length (π : HistoryPolicy M) (μ : PMF S) :
    ∀ n, ∀ h ∈ (historyLaw M π μ n).support, h.1.length = n := by
  intro n
  induction n with
  | zero =>
    intro h hh
    have hh' : h ∈ (μ.map (fun s => (([] : List (S × A)), s))).support := hh
    obtain ⟨s, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh'
    rfl
  | succ n ih =>
    intro h hh
    have hh' : h ∈ ((historyLaw M π μ n).bind fun h =>
      (π h).bind fun a => (M.transition h.2 a).map fun j =>
        ((h.2, a.val) :: h.1, j)).support := hh
    obtain ⟨h', hh'', h2⟩ := (PMF.mem_support_bind_iff _ _ _).mp hh'
    obtain ⟨a, _, h3⟩ := (PMF.mem_support_bind_iff _ _ _).mp h2
    obtain ⟨j, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h3
    simp [ih h' hh'']

theorem s225_sig_markov (π' : MarkovPolicy M) (μ : PMF S) (n : ℕ) :
    s225_sig M π'.toHistory μ n =
      ((historyLaw M π'.toHistory μ n).map s225_hsnd).bind
        (fun j => (π' n j).map (Sigma.mk j)) := by
  unfold s225_sig
  refine Eq.trans ?_ (PMF.bind_map _ _ _).symm
  apply s225_bind_congr_support
  intro h hh
  have hl := s225_length M π'.toHistory μ n h hh
  show (π' h.1.length h.2).map _ = _
  rw [hl]; rfl

theorem s225_markov_main (μ : PMF S) (π : HistoryPolicy M) : ∃ π' : MarkovPolicy M,
    ∀ n, stateActionLaw M π'.toHistory μ n = stateActionLaw M π μ n := by
  have : ∀ s, Nonempty {a : A // a ∈ M.actions s} :=
    fun s => ⟨⟨_, (M.actions_nonempty s).some_mem⟩⟩
  let π' : MarkovPolicy M := fun n j => s225_cond (s225_sig M π μ n) j
  have hsig : ∀ n, (historyLaw M π'.toHistory μ n).map s225_hsnd =
      (historyLaw M π μ n).map s225_hsnd →
      s225_sig M π'.toHistory μ n = s225_sig M π μ n := by
    intro n hn
    rw [s225_sig_markov, hn, ← s225_fst_marg]
    exact (s225_disint _).symm
  have hmarg : ∀ n, (historyLaw M π'.toHistory μ n).map s225_hsnd =
      (historyLaw M π μ n).map s225_hsnd := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [s225_succ_snd, s225_succ_snd, hsig n ih]
  refine ⟨π', fun n => ?_⟩
  rw [s225_sal_eq, s225_sal_eq, hsig n (hmarg n)]
end MDP

theorem solution {S A : Type*} [Countable S] [Nonempty S]
    (M : Model S A) (π : HistoryPolicy M) :
    ∀ s : S, ∃ π' : MarkovPolicy M, ∀ (n : ℕ) (j : S) (a : A),
      a ∈ M.actions j →
      stateActionLaw M π'.toHistory (PMF.pure s) n (j, a) =
        stateActionLaw M π (PMF.pure s) n (j, a) := by
  intro s
  obtain ⟨π', h⟩ := s225_markov_main M (PMF.pure s) π
  exact ⟨π', fun n j a _ => by rw [h n]⟩
