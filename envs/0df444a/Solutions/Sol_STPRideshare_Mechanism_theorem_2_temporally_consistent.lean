-- Prove2me | solution 1 for STPRideshare.Mechanism.theorem_2_temporally_consistent
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:20:18.465318+00:00
-- url     : https://prove2.me/submissions/cac139e5-677f-4ae3-9e89-027d010660dc

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP

namespace STPRideshare.Mechanism

open scoped Classical

namespace TCAux

variable {L : Type}

/-- Invariant of driver states at time `u`. -/
def StInv {κ : Type} (P : Params L) (u : ℕ) : DState L κ → Prop
  | .wait _ _ τ => u ≤ τ
  | .enroute a b t' _ => t' < u ∧ u < t' + P.δ a b
  | .gone => True

theorem stInv_step {κ : Type} (P : Params L) (R : κ → Rider L) (u : ℕ) (s : DState L κ)
    (α : DAction L κ) (hs : StInv P u s) :
    StInv P (u + 1) (step P R u s α) := by
  cases s with
  | wait β a τ =>
    simp only [StInv] at hs
    simp only [step]
    by_cases hτ : τ = u
    · subst hτ
      simp only [if_true]
      cases α with
      | move b =>
        simp only [arrive]; split_ifs with h1
        · simp [StInv]
        · simp only [StInv]; omega
      | pick j =>
        simp only [arrive]; split_ifs with h1
        · simp [StInv]
        · simp only [StInv]; omega
      | quit => simp [StInv]
      | cont => simp [StInv]
    · simp only [hτ, if_false, StInv]; omega
  | enroute a b t' j =>
    simp only [StInv] at hs
    simp only [step]; split_ifs with h1
    · simp [StInv]
    · simp only [StInv]; omega
  | gone => simp [step, StInv]

theorem stInv_stateAt {ι κ : Type} (e : Econ L ι κ) :
    ∀ (h : Hist L ι κ) (i : ι), StInv e.P h.length (stateAt e h i)
  | [], i => by simp [stateAt, StInv]
  | α :: h, i => by
    simp only [stateAt, List.length_cons]
    exact stInv_step _ _ _ _ _ (stInv_stateAt e h i)

theorem playFrom_length {ι κ : Type} (σ : Strategy L ι κ) (h : Hist L ι κ) :
    ∀ k, (playFrom σ h k).length = h.length + k
  | 0 => by simp [playFrom]
  | k + 1 => by simp [playFrom, playFrom_length σ h k]; omega

/-- The state map from the original economy (time `t + k`) to `E^{(t)}` (time `k`). -/
def shiftState {κ : Type} (P : Params L) (R : κ → Rider L) (t : ℕ) :
    DState L κ → DState L {j : κ // t ≤ (R j).τ}
  | .wait β a τ => .wait β a (τ - t)
  | .enroute a b t' j => if t' < t then .wait true b (t' + P.δ a b - t)
      else .enroute a b (t' - t) (j.bind fun j => if hj : t ≤ (R j).τ then some ⟨j, hj⟩ else none)
  | .gone => .gone

@[simp] theorem shiftState_wait {κ : Type} (P : Params L) (R : κ → Rider L) (t : ℕ) (β : Bool)
    (a : L) (τ : ℕ) : shiftState P R t (.wait β a τ) = .wait β a (τ - t) := rfl

@[simp] theorem shiftState_gone {κ : Type} (P : Params L) (R : κ → Rider L) (t : ℕ) :
    shiftState P R t (.gone : DState L κ) = .gone := rfl

/-- Lift an action of the shifted economy back to the original one. -/
def liftAct {κ : Type} {p : κ → Prop} : DAction L {j // p j} → DAction L κ
  | .move b => .move b
  | .pick j => .pick j.1
  | .quit => .quit
  | .cont => .cont

theorem planAction_val {κ ι' κ0 : Type} {p : κ → Prop} {e' : Econ L ι' κ0}
    (d : Dispatch e') (i' : ι') (u : ℕ) (emb : κ0 → {j // p j}) :
    planAction (κ := κ) d i' u (fun j => (emb j).1) = liftAct (planAction d i' u emb) := by
  unfold planAction
  rcases hf : (d.z i').find? (fun st => decide (st.1.2.2 = u)) with _ | ⟨⟨a, b, c⟩, _ | j⟩
  · simp [hf, liftAct]
  · simp [hf, liftAct]
  · simp [hf, liftAct]

theorem isAvail_shift {κ : Type} (P : Params L) (R : κ → Rider L) (t k : ℕ) (s : DState L κ)
    (hs : StInv P (t + k) s) :
    IsAvailAt k (shiftState P R t s) ↔ IsAvailAt (t + k) s := by
  cases s with
  | wait β a τ => simp only [StInv] at hs; simp only [shiftState, IsAvailAt]; omega
  | enroute a b t' j =>
    simp only [StInv] at hs
    simp only [shiftState]
    split_ifs with h1
    · simp only [IsAvailAt, iff_false]; omega
    · simp [IsAvailAt]
  | gone => simp [shiftState, IsAvailAt]

@[simp] theorem shiftParams_δ (P : Params L) (t : ℕ) : (shiftParams P t).δ = P.δ := rfl

theorem arrive_shift {κ : Type} (P : Params L) (R : κ → Rider L) (t k : ℕ) (a b : L)
    (j : Option κ) :
    shiftState P R t (arrive P (t + k) a b j) =
      arrive (shiftParams P t) k a b
        (j.bind fun j => if hj : t ≤ (R j).τ then some ⟨j, hj⟩ else none) := by
  simp only [arrive]
  split_ifs with h1 h2 h2 <;> simp only [shiftParams_δ] at * <;> first | omega | skip
  · simp only [shiftState]; congr 1; omega
  · simp only [shiftState]; rw [if_neg (by omega)]; congr 1; omega

theorem step_shift {κ : Type} (P : Params L) (R : κ → Rider L) (t k : ℕ) (s : DState L κ)
    (hs : StInv P (t + k) s) (α : DAction L {j : κ // t ≤ (R j).τ}) :
    shiftState P R t (step P R (t + k) s (liftAct α)) =
      step (shiftParams P t) (fun j => ⟨(R j.1).o, (R j.1).d, (R j.1).τ - t, (R j.1).v⟩) k
        (shiftState P R t s) α := by
  cases s with
  | wait β a τ =>
    simp only [StInv] at hs
    by_cases hτ : τ = t + k
    · subst hτ
      have : t + k - t = k := by omega
      simp only [step, shiftState_wait, this, if_true]
      cases α with
      | move b => simp only [liftAct]; rw [arrive_shift]; rfl
      | pick j =>
        simp only [liftAct]; rw [arrive_shift]
        simp [j.2]
      | quit => simp [liftAct, shiftState]
      | cont => simp [liftAct, shiftState]
    · have : τ - t ≠ k := by omega
      simp [step, shiftState, hτ, this]
  | enroute a b t' j =>
    simp only [StInv] at hs
    by_cases ht : t' < t
    · have hne : t' + P.δ a b - t ≠ k := by omega
      simp only [step, shiftState, ht, if_true, hne, if_false]
      by_cases h1 : t' + P.δ a b ≤ t + k + 1
      · rw [if_pos h1]; simp only [shiftState]; congr 1; omega
      · rw [if_neg h1]; simp [shiftState, ht]
    · simp only [step, shiftState, ht, if_false]
      split_ifs with h1 h2 h2 <;> simp only [shiftParams_δ] at * <;> first | omega | skip
      · congr 1; omega
      · simp [ht]
  | gone => simp [step, shiftState]

theorem planAction_val' {κ ι' : Type} {p : κ → Prop} {e' : Econ L ι' {j // p j}}
    (d : Dispatch e') (i' : ι') (u : ℕ) :
    planAction (κ := κ) d i' u Subtype.val = liftAct (planAction d i' u id) :=
  planAction_val d i' u id

theorem liftAct_eq_pick {κ : Type} {p : κ → Prop} (a : DAction L {j // p j}) (j : {j // p j}) :
    liftAct a = DAction.pick j.1 ↔ a = DAction.pick j := by
  cases a <;> simp [liftAct, Subtype.ext_iff]

section Main

variable [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)

theorem stpDispatchVia_notAvail (t0 : ℕ) (h : Hist L ι κ) (i : ι)
    (hn : ¬ IsAvailAt h.length (stateAt e h i)) : stpDispatchVia sel e t0 h i = .cont := by
  simp [stpDispatchVia, hn]

theorem dispatch_eq (h : Hist L ι κ) (i : ι) :
    (stp sel).dispatch e h i = stpDispatchVia sel e (replanTime sel e h) h i := by
  unfold DynMech.dispatch
  split_ifs with ha
  · rfl
  · rw [stpDispatchVia_notAvail sel e _ _ _ ha]

theorem replanTime_star (h : Hist L ι κ) :
    replanTime sel e ((fun i => (stp sel).sigmaStar e i h) :: h) = replanTime sel e h := by
  simp only [replanTime]
  rw [if_neg]
  push Not
  intro i
  exact dispatch_eq sel e h i

theorem replanTime_dev (α : ι → DAction L κ) (h : Hist L ι κ)
    (hdev : ∃ i, α i ≠ (stp sel).dispatch e h i) :
    replanTime sel e (α :: h) = h.length + 1 := by
  simp only [replanTime]
  rw [if_pos]
  obtain ⟨i, hi⟩ := hdev
  exact ⟨i, by rwa [← dispatch_eq]⟩

theorem gone_stays {ι' : Type} (e' : Econ L ι' κ) (h : Hist L ι' κ) (σ : Strategy L ι' κ)
    (i : ι') (hg : stateAt e' h i = .gone) : ∀ k, stateAt e' (playFrom σ h k) i = .gone
  | 0 => by simpa [playFrom] using hg
  | k + 1 => by
    simp only [playFrom, stateAt]
    rw [gone_stays e' h σ i hg k]
    rfl

theorem H_facts (h' : Hist L ι κ) (hrt : replanTime sel e h' = h'.length) :
    ∀ k, replanTime sel e (playFrom ((stp sel).sigmaStar e) h' k) = h'.length ∧
      (playFrom ((stp sel).sigmaStar e) h' k).drop
        ((playFrom ((stp sel).sigmaStar e) h' k).length - h'.length) = h'
  | 0 => by simp [playFrom, hrt]
  | k + 1 => by
    obtain ⟨h1, h2⟩ := H_facts h' hrt k
    refine ⟨?_, ?_⟩
    · simp only [playFrom]; rw [replanTime_star, h1]
    · simp only [playFrom, List.length_cons, playFrom_length]
      rw [show h'.length + k + 1 - h'.length = k + 1 by omega, List.drop_succ_cons]
      rw [playFrom_length] at h2
      rwa [show h'.length + k - h'.length = k by omega] at h2

theorem G_replan {ι' κ' : Type} [Fintype ι'] [Fintype κ'] (e' : Econ L ι' κ') :
    ∀ k, replanTime sel e' (playFrom ((stp sel).sigmaStar e') [] k) = 0
  | 0 => by simp [playFrom, replanTime]
  | k + 1 => by simp only [playFrom]; rw [replanTime_star, G_replan e' k]

end Main

section TCMain

variable [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)
  (h' : Hist L ι κ)

theorem disp_corr [Fintype {i // stateAt e h' i ≠ .gone}] [Fintype {j // h'.length ≤ (e.R j).τ}]
    (hrt : replanTime sel e h' = h'.length) (hpos : h'.length ≠ 0) (k : ℕ)
    (i' : {i // stateAt e h' i ≠ .gone})
    (hc : stateAt (shiftEcon e h') (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k) i' =
      shiftState e.P e.R h'.length (stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i'.1)) :
    stpDispatchVia sel e (replanTime sel e (playFrom ((stp sel).sigmaStar e) h' k))
        (playFrom ((stp sel).sigmaStar e) h' k) i'.1 =
      liftAct (stpDispatchVia sel (shiftEcon e h')
        (replanTime sel (shiftEcon e h') (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k))
        (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k) i') := by
  obtain ⟨h1, h2⟩ := H_facts sel e h' hrt k
  rw [playFrom_length] at h2
  have hinv := stInv_stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i'.1
  rw [playFrom_length] at hinv
  have hav := isAvail_shift e.P e.R h'.length k _ hinv
  rw [G_replan, h1]
  unfold stpDispatchVia
  rw [playFrom_length, playFrom_length]
  simp only [List.length_nil, zero_add]
  rw [hc, hav]
  by_cases ha : IsAvailAt (h'.length + k) (stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i'.1)
  · rw [if_pos ha, if_pos ha, if_neg hpos, h2, dif_pos i'.2,
      Nat.add_sub_cancel_left, if_pos trivial, planAction_val']
    congr <;> exact Subsingleton.elim _ _
  · rw [if_neg ha, if_neg ha]; rfl

theorem shiftType_wait {κ0 : Type} (P : Params L) (R : κ0 → Rider L) (t : ℕ) (s : DState L κ0)
    (hs : s ≠ .gone) (hinv : StInv P t s) :
    DState.wait (κ := {j : κ0 // t ≤ (R j).τ}) (shiftType P t s hs).β (shiftType P t s hs).ℓ
      (shiftType P t s hs).τ = shiftState P R t s := by
  cases s with
  | wait β a τ => rfl
  | enroute a b t' j =>
    simp only [StInv] at hinv
    simp only [shiftType, shiftState, if_pos hinv.1]
  | gone => exact absurd rfl hs

theorem state_corr [Fintype {i // stateAt e h' i ≠ .gone}] [Fintype {j // h'.length ≤ (e.R j).τ}]
    (hrt : replanTime sel e h' = h'.length) (hpos : h'.length ≠ 0) :
    ∀ (k : ℕ) (i' : {i // stateAt e h' i ≠ .gone}),
      stateAt (shiftEcon e h') (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k) i' =
        shiftState e.P e.R h'.length (stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i'.1)
  | 0, i' => by
    have hinv := stInv_stateAt e h' i'.1
    simp only [playFrom]
    exact shiftType_wait e.P e.R h'.length (stateAt e h' i'.1) i'.2 hinv
  | k + 1, i' => by
    have IH := state_corr hrt hpos k i'
    have hd := disp_corr sel e h' hrt hpos k i' IH
    have hinv := stInv_stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i'.1
    rw [playFrom_length] at hinv
    simp only [playFrom, stateAt]
    rw [playFrom_length, playFrom_length]
    simp only [List.length_nil, zero_add]
    show _ = shiftState e.P e.R h'.length (step e.P e.R (h'.length + k) _
      ((stp sel).dispatch e (playFrom ((stp sel).sigmaStar e) h' k) i'.1))
    rw [dispatch_eq, hd, step_shift _ _ _ _ _ hinv, ← IH]
    exact congrArg (step _ _ k _) (dispatch_eq sel (shiftEcon e h') _ i')

theorem dcorr [Fintype {i // stateAt e h' i ≠ .gone}] [Fintype {j // h'.length ≤ (e.R j).τ}]
    (hrt : replanTime sel e h' = h'.length) (hpos : h'.length ≠ 0) (k : ℕ)
    (i' : {i // stateAt e h' i ≠ .gone}) :
    stpDispatchVia sel e (replanTime sel e (playFrom ((stp sel).sigmaStar e) h' k))
        (playFrom ((stp sel).sigmaStar e) h' k) i'.1 =
      liftAct (stpDispatchVia sel (shiftEcon e h')
        (replanTime sel (shiftEcon e h') (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k))
        (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k) i') :=
  disp_corr sel e h' hrt hpos k i' (state_corr sel e h' hrt hpos k i')

theorem avail_corr [Fintype {i // stateAt e h' i ≠ .gone}] [Fintype {j // h'.length ≤ (e.R j).τ}]
    (hrt : replanTime sel e h' = h'.length) (hpos : h'.length ≠ 0) (k : ℕ)
    (i' : {i // stateAt e h' i ≠ .gone}) :
    IsAvailAt (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k).length
        (stateAt (shiftEcon e h') (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k) i') ↔
      IsAvailAt (playFrom ((stp sel).sigmaStar e) h' k).length
        (stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i'.1) := by
  have hinv := stInv_stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i'.1
  rw [playFrom_length] at hinv
  rw [state_corr sel e h' hrt hpos k i', playFrom_length, playFrom_length]
  simp only [List.length_nil, zero_add]
  exact isAvail_shift e.P e.R h'.length k _ hinv

theorem notAvail_gone (k : ℕ) (i : ι) (hg : ¬ stateAt e h' i ≠ .gone) :
    ¬ IsAvailAt (playFrom ((stp sel).sigmaStar e) h' k).length
        (stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i) := by
  push Not at hg
  rw [gone_stays e h' _ i hg k]
  simp [IsAvailAt]

theorem card_sub {Q : ι → Prop} [Fintype {i // Q i}] (P : ι → Prop) {d1 : DecidablePred P}
    [DecidablePred (fun i' : {i // Q i} => P i'.1)] (hPQ : ∀ i, P i → Q i) :
    (Finset.univ.filter P).card = (Finset.univ.filter (fun i' : {i // Q i} => P i'.1)).card := by
  rw [← Finset.card_map (Function.Embedding.subtype Q)]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.subtype_apply]
  constructor
  · intro hi; exact ⟨⟨i, hPQ i hi⟩, hi, rfl⟩
  · rintro ⟨i', hi', rfl⟩; exact hi'

theorem plan_ext {ι0 κ0 : Type} {e0 : Econ L ι0 κ0} (p1 p2 : Plan e0) (hx : p1.x = p2.x)
    (hz : p1.z = p2.z) (hq : p1.q = p2.q) (hr : p1.r = p2.r) : p1 = p2 := by
  rcases p1 with ⟨⟨x1, z1⟩, q1, r1⟩
  rcases p2 with ⟨⟨x2, z2⟩, q2, r2⟩
  simp only at hx hz hq hr
  subst hx hz hq hr
  rfl

theorem pickCount_corr [Fintype {i // stateAt e h' i ≠ .gone}] [Fintype {j // h'.length ≤ (e.R j).τ}]
    (hrt : replanTime sel e h' = h'.length) (hpos : h'.length ≠ 0) (k : ℕ)
    (j' : {j // h'.length ≤ (e.R j).τ}) :
    pickCount e (playFrom ((stp sel).sigmaStar e) h' k)
        (fun i => (stp sel).sigmaStar e i (playFrom ((stp sel).sigmaStar e) h' k)) j'.1 =
      pickCount (shiftEcon e h') (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k)
        (fun i => (stp sel).sigmaStar (shiftEcon e h') i
          (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k)) j' := by
  unfold pickCount
  rw [card_sub _ (fun i hi => by
    by_contra hg
    exact notAvail_gone sel e h' k i hg hi.1)]
  congr 1
  ext i'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [avail_corr sel e h' hrt hpos k i']
  show _ ∧ (stp sel).dispatch e _ i'.1 = _ ↔ _ ∧ (stp sel).dispatch (shiftEcon e h') _ i' = _
  rw [dispatch_eq, dispatch_eq, dcorr sel e h' hrt hpos k i', liftAct_eq_pick]

theorem dispCount_corr [Fintype {i // stateAt e h' i ≠ .gone}] [Fintype {j // h'.length ≤ (e.R j).τ}]
    (hrt : replanTime sel e h' = h'.length) (hpos : h'.length ≠ 0) (k : ℕ)
    (j' : {j // h'.length ≤ (e.R j).τ}) :
    (Finset.univ.filter fun i => stpDispatchVia sel e
        (replanTime sel e (playFrom ((stp sel).sigmaStar e) h' k))
        (playFrom ((stp sel).sigmaStar e) h' k) i = .pick j'.1).card =
      (Finset.univ.filter fun i' => stpDispatchVia sel (shiftEcon e h')
        (replanTime sel (shiftEcon e h') (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k))
        (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k) i' = .pick j').card := by
  rw [card_sub _ (fun i hi => by
    by_contra hg
    rw [stpDispatchVia_notAvail sel e _ _ _ (notAvail_gone sel e h' k i hg)] at hi
    cases hi)]
  congr 1
  ext i'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [dcorr sel e h' hrt hpos k i', liftAct_eq_pick]

theorem stepTrip_shift (k : ℕ) (s : DState L κ) (hs : StInv e.P (h'.length + k) s)
    (a : DAction L {j : κ // h'.length ≤ (e.R j).τ}) :
    (stepTrip e.R (h'.length + k) s (liftAct a)).map (shiftTrip e h'.length) =
      stepTrip (shiftEcon e h').R k (shiftState e.P e.R h'.length s) a := by
  cases s with
  | wait β x τ =>
    simp only [StInv] at hs
    cases a with
    | move b =>
      simp only [liftAct, stepTrip, shiftState_wait]
      by_cases hτ : τ = h'.length + k
      · rw [if_pos hτ, if_pos (by omega)]; simp [shiftTrip]
      · rw [if_neg hτ, if_neg (by omega)]; rfl
    | pick jj =>
      simp only [liftAct, stepTrip, shiftState_wait]
      by_cases hτ : τ = h'.length + k
      · rw [if_pos hτ, if_pos (by omega)]
        simp [shiftTrip, jj.2, shiftEcon, econAt]
      · rw [if_neg hτ, if_neg (by omega)]; rfl
    | quit => simp [liftAct, stepTrip]
    | cont => simp [liftAct, stepTrip]
  | enroute x b t' jj =>
    simp only [StInv] at hs
    simp only [shiftState]
    by_cases ht : t' < h'.length
    · rw [if_pos ht]
      cases a <;> simp only [liftAct, stepTrip, Option.map_none] <;> rw [if_neg (by omega)]
    · rw [if_neg ht]
      cases a <;> simp [liftAct, stepTrip]
  | gone => cases a <;> simp [liftAct, stepTrip]

theorem stpPrice_inst {ι0 κ0 : Type} (e0 : Econ L ι0 κ0) (i1 i2 : Fintype ι0) (k1 k2 : Fintype κ0)
    (tr : Trip L) : @Econ.stpPrice L ι0 κ0 i1 k1 e0 tr = @Econ.stpPrice L ι0 κ0 i2 k2 e0 tr := by
  obtain rfl := Subsingleton.elim i1 i2
  obtain rfl := Subsingleton.elim k1 k2
  rfl

omit [Fintype L] in
theorem pay_eq {ι0 κ0 : Type} [Fintype ι0] [Fintype κ0] (e0 : Econ L ι0 κ0) (h : Hist L ι0 κ0)
    (i : ι0) : (stp sel).pay e0 h i =
      match stpDispatchVia sel e0 (replanTime sel e0 h) h i with
      | .pick j => stpPriceVia sel e0 h (riderTrip (e0.R j))
      | _ => 0 := rfl

theorem price_corr [Fintype {i // stateAt e h' i ≠ .gone}] [Fintype {j // h'.length ≤ (e.R j).τ}]
    (hrt : replanTime sel e h' = h'.length) (hpos : h'.length ≠ 0) (k : ℕ)
    (j' : {j // h'.length ≤ (e.R j).τ}) :
    stpPriceVia sel e (playFrom ((stp sel).sigmaStar e) h' k) (riderTrip (e.R j'.1)) =
      stpPriceVia sel (shiftEcon e h') (playFrom ((stp sel).sigmaStar (shiftEcon e h')) [] k)
        (riderTrip ((shiftEcon e h').R j')) := by
  obtain ⟨h1, h2⟩ := H_facts sel e h' hrt k
  unfold stpPriceVia
  rw [G_replan, if_pos rfl, h1, if_neg hpos, h2]
  exact stpPrice_inst _ _ _ _ _ _

end TCMain

section TCFinal

variable [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)

theorem tc_aux (h' : Hist L ι κ) [Fintype {i // stateAt e h' i ≠ .gone}]
    [Fintype {j // h'.length ≤ (e.R j).τ}]
    (hrt : replanTime sel e h' = h'.length) (hpos : h'.length ≠ 0) :
    (stp sel).contPlan e h' = (stp sel).plan0 (shiftEcon e h') := by
  apply plan_ext
  · funext j'
    show pickCount e _ _ j'.1 = pickCount (shiftEcon e h') _ _ j'
    simp only [histAt, List.length_nil, Nat.sub_zero]
    exact pickCount_corr sel e h' hrt hpos _ j'
  · funext i'
    show (outTrips e _ h' i'.1).map (shiftTrip e h'.length) = outTrips (shiftEcon e h') _ [] i'
    unfold outTrips
    rw [List.map_filterMap]
    simp only [List.length_nil, Nat.sub_zero]
    apply List.filterMap_congr
    intro k _
    have hinv := stInv_stateAt e (playFrom ((stp sel).sigmaStar e) h' k) i'.1
    rw [playFrom_length] at hinv
    rw [playFrom_length, playFrom_length, List.length_nil, zero_add]
    show (stepTrip e.R _ _ ((stp sel).dispatch e _ i'.1)).map _ =
      stepTrip _ k _ ((stp sel).dispatch (shiftEcon e h') _ i')
    rw [dispatch_eq, dispatch_eq, dcorr sel e h' hrt hpos k i', stepTrip_shift e h' k _ hinv,
      state_corr sel e h' hrt hpos k i']
  · funext j'
    show (stp sel).charge e _ j'.1 * (riderPicked e _ h' j'.1 : ℝ) =
      (stp sel).charge (shiftEcon e h') _ j' * (riderPicked (shiftEcon e h') _ [] j' : ℝ)
    have hx : riderPicked e ((stp sel).sigmaStar e) h' j'.1 =
        riderPicked (shiftEcon e h') ((stp sel).sigmaStar (shiftEcon e h')) [] j' := by
      show pickCount e _ _ j'.1 = pickCount (shiftEcon e h') _ _ j'
      simp only [histAt, List.length_nil, Nat.sub_zero]
      exact pickCount_corr sel e h' hrt hpos _ j'
    rw [hx]
    congr 1
    show stpPriceVia sel e _ _ * _ = stpPriceVia sel (shiftEcon e h') _ _ * _
    simp only [histAt, List.length_nil, Nat.sub_zero]
    rw [price_corr sel e h' hrt hpos _ j']
    congr 2
    convert dispCount_corr sel e h' hrt hpos ((e.R j'.1).τ - h'.length) j' using 3
    all_goals rfl
  · funext i' u
    show (if u < e.P.T - h'.length then _ else 0) = (if u < e.P.T - h'.length - 0 then _ else 0)
    rw [Nat.sub_zero]
    split_ifs with hu
    · unfold DynMech.payNow
      simp only [and_true]
      rw [avail_corr sel e h' hrt hpos u i']
      split_ifs with ha
      · rw [pay_eq, pay_eq, dcorr sel e h' hrt hpos u i']
        generalize stpDispatchVia sel (shiftEcon e h') _ _ i' = a
        cases a with
        | pick jj => exact price_corr sel e h' hrt hpos u jj
        | move b => rfl
        | quit => rfl
        | cont => rfl
      · rfl
    · rfl

theorem tc_main : TemporallyConsistent (stp sel) := by
  intro ι κ _ _ e _ α h _ hdev
  exact tc_aux sel e (α :: h) (by rw [replanTime_dev sel e α h hdev]; simp) (by simp)

end TCFinal

end TCAux

end STPRideshare.Mechanism

open STPRideshare.Mechanism in
theorem solution {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    TemporallyConsistent (stp sel) :=
  TCAux.tc_main sel
