-- Prove2me | solution 1 for PutermanMDP.TotalReward.markov_reduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:36:41.387995+00:00
-- url     : https://prove2.me/submissions/62f4ebc6-6d72-437b-8026-aa01d0093503

import Mathlib
import Definitions.Def_PutermanMDP_TotalReward_Model

open scoped ENNReal
open PutermanMDP.TotalReward

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

theorem s225_tsum_map {α β : Type*} (p : PMF α) (f : α → β) (G : β → ℝ≥0∞) :
    ∑' b, (p.map f) b * G b = ∑' a, p a * G (f a) := by
  classical
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  rw [tsum_eq_single (f a)]
  · rw [if_pos rfl]
  · intro b hb; rw [if_neg hb, zero_mul]

theorem s225_tsum_bind {α β : Type*} (p : PMF α) (f : α → PMF β) (G : β → ℝ≥0∞) :
    ∑' b, (p.bind f) b * G b = ∑' a, p a * ∑' b, f a b * G b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro a
  apply tsum_congr; intro b
  ring

section MDP
variable {S : Type*} {A : S → Type*} (M : Model S A)

noncomputable def s225_sig (π : HRPolicy S A) (s : S) (n : ℕ) : PMF (Sigma A) :=
  (historyLaw M π s n).bind (fun h => (π h).map (Sigma.mk h.2))

theorem s225_acc_eq (π : HRPolicy S A) (s : S) (g : (t : S) → A t → ℝ≥0∞) :
    accumulated M π s g = ∑' n, ∑' x, s225_sig M π s n x * g x.1 x.2 := by
  unfold accumulated
  apply tsum_congr; intro n
  unfold s225_sig
  rw [s225_tsum_bind]
  apply tsum_congr; intro h
  rw [s225_tsum_map, ← ENNReal.tsum_mul_left]
  apply tsum_congr; intro a
  ring

theorem s225_succ_snd (π : HRPolicy S A) (s : S) (n : ℕ) :
    (historyLaw M π s (n + 1)).map Prod.snd =
      (s225_sig M π s n).bind (fun x => M.transition x.1 x.2) := by
  rw [historyLaw]
  unfold s225_sig
  rw [PMF.map_bind, PMF.bind_bind]
  congr 1; funext h
  rw [PMF.map_bind, PMF.bind_map]
  congr 1; funext a
  rw [PMF.map_bind]
  simp only [PMF.pure_map, Function.comp_apply]
  exact PMF.bind_pure _

theorem s225_fst_marg (π : HRPolicy S A) (s : S) (n : ℕ) :
    (s225_sig M π s n).map Sigma.fst = (historyLaw M π s n).map Prod.snd := by
  unfold s225_sig
  rw [PMF.map_bind]
  show _ = (historyLaw M π s n).bind (fun h => PMF.pure h.2)
  congr 1; funext h
  rw [PMF.map_comp]
  exact PMF.map_const _ _

theorem s225_length (π : HRPolicy S A) (s : S) :
    ∀ n, ∀ h ∈ (historyLaw M π s n).support, h.1.length = n := by
  intro n
  induction n with
  | zero =>
    intro h hh
    have hh' : h ∈ (PMF.pure (([] : List (Sigma A)), s)).support := hh
    rw [PMF.mem_support_pure_iff] at hh'
    subst hh'; rfl
  | succ n ih =>
    intro h hh
    have hh' : h ∈ ((historyLaw M π s n).bind fun h =>
      (π h).bind fun a => (M.transition h.2 a).bind fun t =>
        PMF.pure (h.1 ++ [⟨h.2, a⟩], t)).support := hh
    obtain ⟨h', hh'', h2⟩ := (PMF.mem_support_bind_iff _ _ _).mp hh'
    obtain ⟨a, _, h3⟩ := (PMF.mem_support_bind_iff _ _ _).mp h2
    obtain ⟨j, _, h4⟩ := (PMF.mem_support_bind_iff _ _ _).mp h3
    rw [PMF.mem_support_pure_iff] at h4
    subst h4
    simp [ih h' hh'']

theorem s225_sig_markov (π' : MRPolicy S A) (s : S) (n : ℕ) :
    s225_sig M (markovPolicy π') s n =
      ((historyLaw M (markovPolicy π') s n).map Prod.snd).bind
        (fun j => (π' n j).map (Sigma.mk j)) := by
  unfold s225_sig
  rw [PMF.bind_map]
  apply s225_bind_congr_support
  intro h hh
  have hl := s225_length M (markovPolicy π') s n h hh
  show (π' h.1.length h.2).map _ = _
  rw [hl]; rfl

theorem s225_markov_main [∀ s, Nonempty (A s)] (s : S) (π : HRPolicy S A) :
    ∃ π' : MRPolicy S A, ∀ n, s225_sig M (markovPolicy π') s n = s225_sig M π s n := by
  let π' : MRPolicy S A := fun n j => s225_cond (s225_sig M π s n) j
  have hsig : ∀ n, (historyLaw M (markovPolicy π') s n).map Prod.snd =
      (historyLaw M π s n).map Prod.snd →
      s225_sig M (markovPolicy π') s n = s225_sig M π s n := by
    intro n hn
    rw [s225_sig_markov, hn, ← s225_fst_marg]
    exact (s225_disint _).symm
  have hmarg : ∀ n, (historyLaw M (markovPolicy π') s n).map Prod.snd =
      (historyLaw M π s n).map Prod.snd := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [s225_succ_snd, s225_succ_snd, hsig n ih]
  exact ⟨π', fun n => hsig n (hmarg n)⟩
end MDP

theorem solution {S : Type*} {A : S → Type*}
    [Countable S] [Nonempty S] [∀ s, Countable (A s)] [∀ s, Nonempty (A s)]
    (M : Model S A) (hM : WellDefined M) (s : S) :
    optimalValue M s = (⨆ π : HRPolicy S A, policyValue M π s) ∧
    optimalValue M s = (⨆ π : MRPolicy S A, policyValue M (markovPolicy π) s) := by
  refine ⟨rfl, ?_⟩
  unfold optimalValue
  apply le_antisymm
  · apply iSup_le
    intro π
    obtain ⟨π', hπ'⟩ := s225_markov_main M s π
    have hv : policyValue M (markovPolicy π') s = policyValue M π s := by
      unfold policyValue positiveReward negativeReward
      rw [s225_acc_eq, s225_acc_eq, s225_acc_eq M π, s225_acc_eq M π]
      simp only [hπ']
    rw [← hv]
    exact le_iSup (fun π : MRPolicy S A => policyValue M (markovPolicy π) s) π'
  · exact iSup_le (fun π' => le_iSup (fun π : HRPolicy S A => policyValue M π s) (markovPolicy π'))
