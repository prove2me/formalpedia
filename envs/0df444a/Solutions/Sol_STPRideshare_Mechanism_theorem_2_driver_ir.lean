-- Prove2me | solution 1 for STPRideshare.Mechanism.theorem_2_driver_ir
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T04:43:58.687193+00:00
-- url     : https://prove2.me/submissions/46231a89-730d-4d69-b02f-e40f1aa1673f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_STPRideshare_Mechanism_STP
import Theorems.Thm_STPRideshare_Mechanism_step1_continuation_utility

namespace STPRideshare.Mechanism

open scoped Classical

set_option linter.unusedSectionVars false

namespace BBAux

variable {L : Type}

/-! ### Invariants of a single driver's state -/

/-- Timing invariant of driver states at time `u`. -/
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

/-- Every trip a driver is on, or will become available at, ends by `T`. -/
def V {κ : Type} (P : Params L) : DState L κ → Prop
  | .wait _ _ τ => τ ≤ P.T
  | .enroute a b t' _ => t' + P.δ a b ≤ P.T
  | .gone => True

/-- Consistency of a driver's state with a planned path suffix (original time coordinates). -/
def ConsS {κ : Type} (P : Params L) : DState L κ → List (Trip L) → Prop
  | .wait _ a τ, zs => P.IsPathFrom a τ zs
  | .enroute a b t' _, zs => P.IsPathFrom b (t' + P.δ a b) zs
  | .gone, zs => zs = []

/-- A driver at time `u` is consistent with her planned action path `z`: `z` splits into a part
of trips starting before `u` and a remaining part that the driver can still follow. -/
def Cons {κ : Type} (P : Params L) (u : ℕ) (s : DState L κ) (z : List (Trip L × Option κ)) :
    Prop :=
  ∃ pre zs, z = pre ++ zs ∧ (∀ st ∈ pre, st.1.2.2 < u) ∧ ConsS P s (zs.map Prod.fst)

/-- The action prescribed at time `u` by an action path `z` (original time coordinates). -/
def planAct {κ : Type} (z : List (Trip L × Option κ)) (u : ℕ) : DAction L κ :=
  match z.find? (fun st => decide (st.1.2.2 = u)) with
  | some ((_, b, _), none) => .move b
  | some (_, some j) => .pick j
  | none => .quit

theorem find_pre_append {κ : Type} (pre zs : List (Trip L × Option κ)) (u : ℕ)
    (hpre : ∀ st ∈ pre, st.1.2.2 < u) :
    (pre ++ zs).find? (fun st => decide (st.1.2.2 = u)) =
      zs.find? (fun st => decide (st.1.2.2 = u)) := by
  rw [List.find?_append]
  rw [List.find?_eq_none.mpr]
  · simp
  · intro st hst
    have := hpre st hst
    simp only [decide_eq_true_eq]; omega

theorem isPathFrom_times {κ : Type} (P : Params L) :
    ∀ (a : L) (t : ℕ) (zs : List (Trip L × Option κ)), P.IsPathFrom a t (zs.map Prod.fst) →
      ∀ st ∈ zs, t ≤ st.1.2.2
  | _, _, [], _ => by simp
  | a, t, z :: zs, h => by
    simp only [List.map_cons, Params.IsPathFrom] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    intro st hst
    rcases List.mem_cons.mp hst with rfl | hst
    · omega
    · have := isPathFrom_times P _ _ zs h4 st hst
      have : 1 ≤ 1 := le_refl 1
      omega

theorem cons_step {κ : Type} (P : Params L) (hP : ∀ a b, 1 ≤ P.δ a b) (R : κ → Rider L) (u : ℕ)
    (s : DState L κ) (z : List (Trip L × Option κ)) (hinv : StInv P u s) (hV : V P s)
    (hc : Cons P u s z) (hfeas : ∀ st ∈ z, ∀ j, st.2 = some j → st.1 = riderTrip (R j))
    (α : DAction L κ) (hα : IsAvailAt u s → α = planAct z u) :
    Cons P (u + 1) (step P R u s α) z ∧ V P (step P R u s α) := by
  obtain ⟨pre, zs, rfl, hpre, hcs⟩ := hc
  have hpre' : ∀ st ∈ pre, st.1.2.2 < u + 1 := fun st hst => Nat.lt_succ_of_lt (hpre st hst)
  cases s with
  | wait β a τ =>
    simp only [StInv] at hinv
    simp only [V] at hV
    simp only [ConsS] at hcs
    by_cases hτ : τ = u
    · subst hτ
      have hα' := hα (by simp [IsAvailAt])
      subst hα'
      simp only [step, if_true]
      cases zs with
      | nil =>
        have : planAct (pre ++ []) τ = .quit := by
          simp only [planAct, List.append_nil]
          rw [List.find?_eq_none.mpr]
          intro st hst; have := hpre st hst; simp only [decide_eq_true_eq]; omega
        rw [this]
        exact ⟨⟨pre, [], by simp, hpre', by simp [ConsS]⟩, by simp [V]⟩
      | cons st rest =>
        obtain ⟨⟨a', b, t'⟩, tag⟩ := st
        simp only [List.map_cons, Params.IsPathFrom] at hcs
        obtain ⟨h1, h2, h3, h4⟩ := hcs
        subst a t'
        have hfind : planAct (pre ++ ((a', b, τ), tag) :: rest) τ =
            (match tag with | none => .move b | some j => .pick j) := by
          simp only [planAct]
          rw [find_pre_append _ _ _ hpre]
          cases tag <;> simp
        rw [hfind]
        have hδ := hP a' b
        have key : ∀ jj : Option κ,
            Cons P (τ + 1) (arrive P τ a' b jj) (pre ++ ((a', b, τ), tag) :: rest) ∧
              V P (arrive P τ a' b jj) := by
          intro jj
          refine ⟨⟨pre ++ [((a', b, τ), tag)], rest, by simp, ?_, ?_⟩, ?_⟩
          · intro st hst
            rcases List.mem_append.mp hst with hst | hst
            · exact hpre' st hst
            · simp at hst; subst hst; simp
          · simp only [arrive]
            split_ifs with hh
            · simp only [ConsS]
              rwa [show τ + 1 = τ + P.δ a' b by omega]
            · simpa [ConsS] using h4
          · simp only [arrive]
            split_ifs with hh
            · simp only [V]; omega
            · simp only [V]; omega
        cases tag with
        | none => exact key none
        | some j =>
          have hj := hfeas ((a', b, τ), some j) (by simp) j rfl
          simp only [riderTrip, Prod.mk.injEq] at hj
          simp only
          rw [← hj.2.1]
          exact key (some j)
    · simp only [step, hτ, if_false]
      exact ⟨⟨pre, zs, rfl, hpre', by simpa [ConsS] using hcs⟩, by simpa [V] using hV⟩
  | enroute a b t' j =>
    simp only [StInv] at hinv
    simp only [V] at hV
    simp only [ConsS] at hcs
    simp only [step]
    split_ifs with hh
    · refine ⟨⟨pre, zs, rfl, hpre', ?_⟩, ?_⟩
      · simp only [ConsS]; rwa [show u + 1 = t' + P.δ a b by omega]
      · simp only [V]; omega
    · exact ⟨⟨pre, zs, rfl, hpre', by simpa [ConsS] using hcs⟩, by simpa [V] using hV⟩
  | gone =>
    simp only [step]
    exact ⟨⟨pre, zs, rfl, hpre', hcs⟩, trivial⟩

theorem V_step {κ : Type} (P : Params L) (hP : ∀ a b, 1 ≤ P.δ a b) (R : κ → Rider L) (u : ℕ)
    (s : DState L κ) (z : List (Trip L × Option κ)) (hinv : StInv P u s) (hV : V P s)
    (hc : Cons P u s z) (hfeas : ∀ st ∈ z, ∀ j, st.2 = some j → st.1 = riderTrip (R j))
    (α : DAction L κ)
    (hα : ∀ β a, s = .wait β a u →
      (α = planAct z u ∨ (∃ b, α = .move b ∧ u + P.δ a b ≤ P.T) ∨ α = .quit)) :
    V P (step P R u s α) := by
  by_cases hav : IsAvailAt u s
  · cases s with
    | wait β a τ =>
      simp only [IsAvailAt] at hav
      subst hav
      rcases hα β a rfl with h | ⟨b, rfl, hb⟩ | rfl
      · exact (cons_step P hP R τ _ z hinv hV hc hfeas α (fun _ => h)).2
      · simp only [step, if_true, arrive]
        have := hP a b
        split_ifs with hh
        · simp only [V]; omega
        · simp only [V]; omega
      · simp [step, V]
    | enroute => simp [IsAvailAt] at hav
    | gone => simp [IsAvailAt] at hav
  · exact (cons_step P hP R u s z hinv hV hc hfeas α (fun h => absurd h hav)).2

@[simp] theorem shiftParams_δ' (P : Params L) (t : ℕ) : (shiftParams P t).δ = P.δ := rfl

/-- Shift a trip of `E^{(t₀)}` back to original times. -/
def shiftBack {κ : Type} {p : κ → Prop} (t0 : ℕ) (st : Trip L × Option {j // p j}) :
    Trip L × Option κ :=
  ((st.1.1, st.1.2.1, st.1.2.2 + t0), st.2.map Subtype.val)

theorem planAction_id {κ ι0 : Type} {e0 : Econ L ι0 κ} (d : Dispatch e0) (i0 : ι0) (u : ℕ) :
    planAction d i0 u id = planAct (d.z i0) u := by
  unfold planAction planAct
  rcases hf : (d.z i0).find? (fun st => decide (st.1.2.2 = u)) with _ | ⟨⟨a, b, c⟩, _ | j⟩ <;>
    simp [hf]

theorem planAction_shiftBack {κ ι0 : Type} {p : κ → Prop} {e0 : Econ L ι0 {j // p j}}
    (d : Dispatch e0) (i0 : ι0) (t0 u : ℕ) (hle : t0 ≤ u) :
    planAction (κ := κ) d i0 (u - t0) Subtype.val = planAct ((d.z i0).map (shiftBack t0)) u := by
  unfold planAction planAct
  rw [List.find?_map]
  have hp : ((fun st : Trip L × Option κ => decide (st.1.2.2 = u)) ∘ shiftBack t0) =
      (fun st : Trip L × Option {j // p j} => decide (st.1.2.2 = u - t0)) := by
    funext st
    simp only [Function.comp, shiftBack]
    have : st.1.2.2 + t0 = u ↔ st.1.2.2 = u - t0 := by omega
    simp only [this]
  rw [hp]
  rcases hf : (d.z i0).find? (fun st => decide (st.1.2.2 = u - t0)) with _ | ⟨⟨a, b, c⟩, _ | j⟩ <;>
    simp [hf, shiftBack]

theorem isPathFrom_shift {κ0 : Type} (P : Params L) (t0 : ℕ) (hT : t0 ≤ P.T) {p : κ0 → Prop} :
    ∀ (a : L) (τ' : ℕ) (zs : List (Trip L × Option {j // p j})),
      (shiftParams P t0).IsPathFrom a τ' (zs.map Prod.fst) →
      P.IsPathFrom a (τ' + t0) ((zs.map (shiftBack t0)).map Prod.fst)
  | _, _, [], _ => by simp [Params.IsPathFrom]
  | a, τ', z :: zs, h => by
    simp only [List.map_cons, Params.IsPathFrom] at h ⊢
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [shiftParams_δ'] at h3 h4
    refine ⟨by simp [shiftBack, h1], by simp [shiftBack, h2], ?_, ?_⟩
    · simp only [shiftBack, shiftParams] at h3 ⊢; omega
    · have := isPathFrom_shift P t0 hT _ _ zs h4
      simp only [shiftBack] at this ⊢
      rwa [show τ' + t0 + P.δ a z.1.2.1 = τ' + P.δ a z.1.2.1 + t0 by omega]

theorem consS_shiftType {κ0 : Type} (P : Params L) (t0 : ℕ) (hT : t0 ≤ P.T) (s : DState L κ0)
    (hs : s ≠ .gone) (hinv : StInv P t0 s) {R : κ0 → Rider L}
    (zs : List (Trip L × Option {j // t0 ≤ (R j).τ}))
    (hp : (shiftParams P t0).IsPathFrom (shiftType P t0 s hs).ℓ (shiftType P t0 s hs).τ
      (zs.map Prod.fst)) :
    ConsS P s ((zs.map (shiftBack t0)).map Prod.fst) := by
  cases s with
  | wait β a τ =>
    simp only [StInv] at hinv
    have := isPathFrom_shift P t0 hT a (τ - t0) zs hp
    simp only [ConsS]
    rwa [Nat.sub_add_cancel hinv] at this
  | enroute a b t' j =>
    simp only [StInv] at hinv
    have := isPathFrom_shift P t0 hT b (t' + P.δ a b - t0) zs hp
    simp only [ConsS]
    rwa [Nat.sub_add_cancel (by omega)] at this
  | gone => exact absurd rfl hs

/-- The conclusion of Step 1 used downstream: welfare-optimal dispatchings are CE with the STP
prices (28). -/
def Step1CE (L : Type) [Fintype L] : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ d : Dispatch e, d.IsWelfareOptimal → d.IsCE e.stpPrice

section Global

variable [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)

/-- The current plan's action path of each driver, in original coordinates. -/
noncomputable def curZ (h : Hist L ι κ) (i : ι) : List (Trip L × Option κ) :=
  if replanTime sel e h = 0 then (sel e).z i
  else if hi : stateAt e (h.drop (h.length - replanTime sel e h)) i ≠ .gone then
    ((sel (shiftEcon e (h.drop (h.length - replanTime sel e h)))).z ⟨i, hi⟩).map
      (shiftBack (replanTime sel e h))
  else []

theorem disp_planAct (h : Hist L ι κ) (i : ι) (hle : replanTime sel e h ≤ h.length)
    (ha : IsAvailAt h.length (stateAt e h i)) :
    stpDispatchVia sel e (replanTime sel e h) h i = planAct (curZ sel e h i) h.length := by
  unfold stpDispatchVia curZ
  rw [if_pos ha]
  by_cases h0 : replanTime sel e h = 0
  · rw [if_pos h0, if_pos h0, planAction_id]
  · rw [if_neg h0, if_neg h0]
    by_cases hi : stateAt e (h.drop (h.length - replanTime sel e h)) i ≠ .gone
    · rw [dif_pos hi, dif_pos hi, planAction_shiftBack _ _ _ _ hle]
    · rw [dif_neg hi, dif_neg hi]
      simp [planAct]

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem shiftType_le (P : Params L) (t0 : ℕ) (s : DState L κ) (hs : s ≠ .gone) (hV : V P s) :
    (shiftType P t0 s hs).τ ≤ P.T - t0 := by
  cases s with
  | wait β a τ => simp only [V] at hV; simp only [shiftType]; omega
  | enroute a b t' j => simp only [V] at hV; simp only [shiftType]; omega
  | gone => exact absurd rfl hs

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem econAt_valid (he : e.Valid) (h : Hist L ι κ)
    (hV : ∀ i, V e.P (stateAt e h i)) : (shiftEcon e h).Valid := by
  obtain ⟨⟨hP1, hP2, hP3, hP4, hP5⟩, hD, hRv, hRt⟩ := he
  refine ⟨⟨hP1, hP2, ?_, ?_, hP5⟩, ?_, ?_, ?_⟩
  · intro a b t ht
    have := hP1 a b
    exact hP3 a b (t + h.length) (by simp only [shiftEcon, econAt, shiftParams] at ht ⊢; omega)
  · intro n hn
    exact hP4 n (by simp only [shiftEcon, econAt, shiftParams] at hn ⊢; omega)
  · intro i
    exact shiftType_le e.P h.length _ i.2 (hV i.1)
  · intro j; exact hRv j.1
  · intro j
    have := hRt j.1
    have hj := j.2
    simp only [Params.IsTrip, riderTrip, shiftEcon, econAt, shiftParams] at this ⊢
    omega

/-- The current plan is feasible-like in original coordinates. -/
def PlanOK (Z : ι → List (Trip L × Option κ)) : Prop :=
  (∀ i st, st ∈ Z i → ∀ j, st.2 = some j → st.1 = riderTrip (e.R j)) ∧
  (∀ j, (Finset.univ.filter fun i => (riderTrip (e.R j), some j) ∈ Z i).card ≤ 1)

/-- The global invariant along reachable histories. -/
def Good (h : Hist L ι κ) : Prop :=
  replanTime sel e h ≤ h.length ∧ (∀ i, V e.P (stateAt e h i)) ∧ PlanOK e (curZ sel e h) ∧
    ∀ i, Cons e.P h.length (stateAt e h i) (curZ sel e h i)

theorem good_nil (he : e.Valid) (hsel : IsOptimalSelector sel) : Good sel e [] := by
  have hrt : replanTime sel e [] = 0 := rfl
  have hz : ∀ i, curZ sel e [] i = (sel e).z i := fun i => by simp [curZ, hrt]
  obtain ⟨hf1, hf2, hf3, hf4⟩ := (hsel e he).1
  refine ⟨by simp [hrt], ?_, ?_, ?_⟩
  · intro i; simp only [stateAt, V]; exact he.2.1 i
  · refine ⟨fun i st hst j hj => hf2 i st (by rw [← hz]; exact hst) j hj, fun j => ?_⟩
    have := hf4 j
    rw [hf3 j] at this
    simp only [hz]
    convert this using 2
  · intro i
    refine ⟨[], curZ sel e [] i, by simp, by simp, ?_⟩
    simp only [stateAt, ConsS, hz]
    exact hf1 i

omit [Fintype L] in
theorem stpDispatchVia_notAvail (t0 : ℕ) (h : Hist L ι κ) (i : ι)
    (hn : ¬ IsAvailAt h.length (stateAt e h i)) : stpDispatchVia sel e t0 h i = .cont := by
  simp [stpDispatchVia, hn]

omit [Fintype L] in
theorem dispatch_eq (h : Hist L ι κ) (i : ι) :
    (stp sel).dispatch e h i = stpDispatchVia sel e (replanTime sel e h) h i := by
  unfold DynMech.dispatch
  split_ifs with ha
  · rfl
  · rw [stpDispatchVia_notAvail sel e _ _ _ ha]

omit [Fintype L] in
theorem curZ_noDev (α : ι → DAction L κ) (h : Hist L ι κ) (hle : replanTime sel e h ≤ h.length)
    (hnd : ∀ i, α i = stpDispatchVia sel e (replanTime sel e h) h i) :
    replanTime sel e (α :: h) = replanTime sel e h ∧ curZ sel e (α :: h) = curZ sel e h := by
  have hrt : replanTime sel e (α :: h) = replanTime sel e h := by
    simp only [replanTime]
    rw [if_neg]
    push Not
    exact hnd
  have hdrop : (α :: h).drop ((α :: h).length - replanTime sel e (α :: h)) =
      h.drop (h.length - replanTime sel e h) := by
    rw [hrt, List.length_cons, show h.length + 1 - replanTime sel e h =
      (h.length - replanTime sel e h) + 1 by omega, List.drop_succ_cons]
  refine ⟨hrt, ?_⟩
  funext i
  unfold curZ
  rw [hdrop, hrt]

omit [Fintype L] in
theorem curZ_replan (h : Hist L ι κ) (hrt : replanTime sel e h = h.length) (hpos : h.length ≠ 0)
    (i : ι) :
    curZ sel e h i = if hi : stateAt e h i ≠ .gone then
      ((sel (shiftEcon e h)).z ⟨i, hi⟩).map (shiftBack h.length) else [] := by
  have hdrop : h.drop (h.length - replanTime sel e h) = h := by
    rw [hrt, Nat.sub_self, List.drop_zero]
  unfold curZ
  rw [if_neg (by rw [hrt]; exact hpos)]
  rw [hdrop, hrt]

omit [Fintype L] in
theorem actions_avail (h : Hist L ι κ) (i : ι) (β : Bool) (a : L)
    (hs : stateAt e h i = .wait β a h.length) (α : DAction L κ)
    (hα : α ∈ (stp sel).actions e h i) :
    α = stpDispatchVia sel e (replanTime sel e h) h i ∨
      (∃ b, α = .move b ∧ h.length + e.P.δ a b ≤ e.P.T) ∨ α = .quit := by
  unfold DynMech.actions at hα
  rw [hs] at hα
  simp only [if_true, Set.mem_union, Set.mem_singleton_iff, Set.mem_ofPred_eq] at hα
  rcases hα with (h1 | h1) | h1
  · left; exact h1
  · right; left; exact h1
  · right; right; exact h1

omit [Fintype L] in
theorem actions_notAvail (h : Hist L ι κ) (i : ι) (hn : ¬ IsAvailAt h.length (stateAt e h i))
    (α : DAction L κ) (hα : α ∈ (stp sel).actions e h i) : α = .cont := by
  unfold DynMech.actions at hα
  revert hα hn
  cases stateAt e h i with
  | wait β a τ =>
    intro hn hα
    simp only [IsAvailAt] at hn
    simpa [hn] using hα
  | enroute => intro _ hα; simpa using hα
  | gone => intro _ hα; simpa using hα

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

theorem planOK_replan (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hrt : replanTime sel e h = h.length) (hpos : h.length ≠ 0)
    (hV : ∀ i, V e.P (stateAt e h i)) : PlanOK e (curZ sel e h) := by
  have hval := econAt_valid e he h hV
  obtain ⟨hf1, hf2, hf3, hf4⟩ := (hsel (shiftEcon e h) hval).1
  -- membership in the shifted-back path
  have hmem : ∀ i st, st ∈ curZ sel e h i → ∃ (hi : stateAt e h i ≠ .gone),
      ∃ st0 ∈ (sel (shiftEcon e h)).z ⟨i, hi⟩, shiftBack h.length st0 = st := by
    intro i st hst
    rw [curZ_replan sel e h hrt hpos] at hst
    by_cases hi : stateAt e h i ≠ .gone
    · rw [dif_pos hi] at hst
      obtain ⟨st0, h0, h1⟩ := List.mem_map.mp hst
      exact ⟨hi, st0, h0, h1⟩
    · rw [dif_neg hi] at hst; simp at hst
  refine ⟨?_, ?_⟩
  · intro i st hst j hj
    obtain ⟨hi, st0, h0, rfl⟩ := hmem i st hst
    simp only [shiftBack, Option.map_eq_some_iff] at hj
    obtain ⟨j1, hj1, rfl⟩ := hj
    have := hf2 ⟨i, hi⟩ st0 h0 j1 hj1
    have hτ := j1.2
    simp only [shiftBack, this, riderTrip, shiftEcon, econAt]
    simp only [Prod.mk.injEq, true_and]
    omega
  · intro j
    by_cases hj : h.length ≤ (e.R j).τ
    · set j0 : {j : κ // h.length ≤ (e.R j).τ} := ⟨j, hj⟩
      rw [card_sub (Q := fun i => stateAt e h i ≠ .gone) _ (fun i hi => by
        obtain ⟨hi', _⟩ := hmem i _ hi; exact hi')]
      calc _ ≤ (Finset.univ.filter fun i0 =>
              (riderTrip ((shiftEcon e h).R j0), some j0) ∈ (sel (shiftEcon e h)).z i0).card := by
            apply Finset.card_le_card
            intro i0
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            intro hi0
            obtain ⟨hi, st0, h0, h1⟩ := hmem i0.1 _ hi0
            have h1' := congrArg Prod.snd h1
            simp only [shiftBack, Option.map_eq_some_iff] at h1'
            obtain ⟨j1, hj1, hj1v⟩ := h1'
            have hj10 : j1 = j0 := Subtype.ext hj1v
            have e1 := hf2 ⟨i0.1, hi⟩ st0 h0 j1 hj1
            have e2 : st0 = (st0.1, st0.2) := rfl
            rw [e2, e1, hj1, hj10] at h0
            exact h0
        _ ≤ 1 := by
            have := hf4 j0
            rw [hf3 j0] at this
            convert this using 2
            ext x; simp
    · have : (Finset.univ.filter fun i => (riderTrip (e.R j), some j) ∈ curZ sel e h i) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro hi0
        obtain ⟨hi, st0, h0, h1⟩ := hmem i _ hi0
        have h1' := congrArg Prod.snd h1
        simp only [shiftBack, Option.map_eq_some_iff] at h1'
        obtain ⟨j1, _, hj1v⟩ := h1'
        exact hj (hj1v ▸ j1.2)
      rw [this]; simp

theorem cons_replan (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hrt : replanTime sel e h = h.length) (hpos : h.length ≠ 0) (hT : h.length ≤ e.P.T)
    (hV : ∀ i, V e.P (stateAt e h i)) (i : ι) :
    Cons e.P h.length (stateAt e h i) (curZ sel e h i) := by
  have hval := econAt_valid e he h hV
  obtain ⟨hf1, hf2, hf3, hf4⟩ := (hsel (shiftEcon e h) hval).1
  rw [curZ_replan sel e h hrt hpos]
  by_cases hi : stateAt e h i ≠ .gone
  · rw [dif_pos hi]
    refine ⟨[], ((sel (shiftEcon e h)).z ⟨i, hi⟩).map (shiftBack h.length), by simp, by simp, ?_⟩
    exact consS_shiftType e.P h.length hT _ hi (stInv_stateAt e h i) _ (hf1 ⟨i, hi⟩)
  · rw [dif_neg hi]
    push Not at hi
    refine ⟨[], [], by simp, by simp, ?_⟩
    rw [hi]; simp [ConsS]

theorem good_cons (he : e.Valid) (hsel : IsOptimalSelector sel) (α : ι → DAction L κ)
    (h : Hist L ι κ) (hr : (stp sel).Reachable e (α :: h)) (hg : Good sel e h) :
    Good sel e (α :: h) := by
  obtain ⟨_, hlt, hact⟩ := hr
  obtain ⟨hle, hV, ⟨hok1, hok2⟩, hC⟩ := hg
  have hP1 := he.1.1
  have hst : ∀ i, stateAt e (α :: h) i = step e.P e.R h.length (stateAt e h i) (α i) :=
    fun i => rfl
  have hV' : ∀ i, V e.P (stateAt e (α :: h) i) := by
    intro i
    rw [hst]
    refine V_step e.P hP1 e.R h.length _ (curZ sel e h i) (stInv_stateAt e h i) (hV i) (hC i)
      (hok1 i) (α i) ?_
    intro β a hs
    rcases actions_avail sel e h i β a hs (α i) (hact i) with h1 | h1 | h1
    · left
      rw [h1, disp_planAct sel e h i hle (by rw [hs]; simp [IsAvailAt])]
    · right; left; exact h1
    · right; right; exact h1
  by_cases hdev : ∃ i, α i ≠ stpDispatchVia sel e (replanTime sel e h) h i
  · have hrt : replanTime sel e (α :: h) = (α :: h).length := by
      simp only [replanTime]
      rw [if_pos hdev]; simp
    have hpos : (α :: h).length ≠ 0 := by simp
    have hT : (α :: h).length ≤ e.P.T := by simp; omega
    exact ⟨le_of_eq hrt, hV', planOK_replan sel e he hsel _ hrt hpos hV',
      cons_replan sel e he hsel _ hrt hpos hT hV'⟩
  · push Not at hdev
    obtain ⟨hrt, hz⟩ := curZ_noDev sel e α h hle hdev
    refine ⟨by rw [hrt]; exact Nat.le_succ_of_le hle, hV', by rw [hz]; exact ⟨hok1, hok2⟩, ?_⟩
    intro i
    rw [hz, hst]
    refine (cons_step e.P hP1 e.R h.length _ (curZ sel e h i) (stInv_stateAt e h i) (hV i) (hC i)
      (hok1 i) (α i) ?_).1
    intro ha
    rw [hdev i, disp_planAct sel e h i hle ha]

theorem good_of_reachable (he : e.Valid) (hsel : IsOptimalSelector sel) :
    ∀ h : Hist L ι κ, (stp sel).Reachable e h → Good sel e h
  | [], _ => good_nil sel e he hsel
  | α :: h, hr => good_cons sel e he hsel α h hr (good_of_reachable he hsel h hr.1)

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem planAct_pick (z : List (Trip L × Option κ)) (u : ℕ) (j : κ)
    (hp : planAct z u = .pick j) : ∃ st ∈ z, st.1.2.2 = u ∧ st.2 = some j := by
  unfold planAct at hp
  rcases hf : z.find? (fun st => decide (st.1.2.2 = u)) with _ | ⟨⟨a, b, c⟩, _ | j'⟩ <;>
    rw [hf] at hp
  · cases hp
  · cases hp
  · simp only [DAction.pick.injEq] at hp
    subst hp
    refine ⟨_, List.mem_of_find?_eq_some hf, ?_, rfl⟩
    have := List.find?_some hf
    simpa using this

theorem pick_facts (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (i : ι) (j : κ)
    (hp : stpDispatchVia sel e (replanTime sel e h) h i = .pick j) :
    IsAvailAt h.length (stateAt e h i) ∧ (e.R j).τ = h.length ∧
      (riderTrip (e.R j), some j) ∈ curZ sel e h i := by
  obtain ⟨hle, _, ⟨hok1, _⟩, _⟩ := good_of_reachable sel e he hsel h hr
  by_cases ha : IsAvailAt h.length (stateAt e h i)
  · rw [disp_planAct sel e h i hle ha] at hp
    obtain ⟨st, hst, ht, hj⟩ := planAct_pick _ _ _ hp
    have := hok1 i st hst j hj
    refine ⟨ha, ?_, ?_⟩
    · rw [← ht, this]; rfl
    · have e2 : st = (st.1, st.2) := rfl
      rw [e2, this, hj] at hst; exact hst
  · rw [stpDispatchVia_notAvail sel e _ _ _ ha] at hp; cases hp

theorem dispCount_le (he : e.Valid) (hsel : IsOptimalSelector sel) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (j : κ) :
    (Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e h) h i = .pick j).card ≤ 1 := by
  obtain ⟨_, _, ⟨_, hok2⟩, _⟩ := good_of_reachable sel e he hsel h hr
  refine le_trans (Finset.card_le_card ?_) (hok2 j)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro hp
  exact (pick_facts sel e he hsel h hr i j hp).2.2

omit [Fintype L] in
theorem reach_play (σ : Strategy L ι κ) (hσ : (stp sel).AdmissibleProfile e σ) :
    ∀ k, k ≤ e.P.T → (stp sel).Reachable e (playFrom σ [] k)
  | 0, _ => trivial
  | k + 1, hk => by
    refine ⟨reach_play σ hσ k (by omega), ?_, ?_⟩
    · rw [playFrom_length]; simp; omega
    · intro i
      exact hσ i _ (by rw [playFrom_length]; simp; omega)

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem avail_wait (u : ℕ) (s : DState L κ) (ha : IsAvailAt u s) : ∃ β a, s = .wait β a u := by
  cases s with
  | wait β a τ => simp only [IsAvailAt] at ha; exact ⟨β, a, by rw [ha]⟩
  | enroute => simp [IsAvailAt] at ha
  | gone => simp [IsAvailAt] at ha

omit [Fintype L] in
theorem pick_dispatched (h : Hist L ι κ) (i : ι) (α : DAction L κ)
    (hα : α ∈ (stp sel).actions e h i) (j : κ) (hp : α = .pick j) :
    IsAvailAt h.length (stateAt e h i) ∧ stpDispatchVia sel e (replanTime sel e h) h i = .pick j := by
  by_cases ha : IsAvailAt h.length (stateAt e h i)
  · refine ⟨ha, ?_⟩
    obtain ⟨β, a, hs⟩ := avail_wait _ _ ha
    rcases actions_avail sel e h i β a hs α hα with h1 | ⟨b, h1, _⟩ | h1
    · rw [← h1, hp]
    · rw [hp] at h1; cases h1
    · rw [hp] at h1; cases h1
  · have := actions_notAvail sel e h i ha α hα
    rw [hp] at this; cases this

omit [Fintype L] in
theorem pay_eq (h : Hist L ι κ) (i : ι) : (stp sel).pay e h i =
      match stpDispatchVia sel e (replanTime sel e h) h i with
      | .pick j => stpPriceVia sel e h (riderTrip (e.R j))
      | _ => 0 := rfl

omit [Fintype L] in
theorem payNow_split (h : Hist L ι κ) (hT : h.length < e.P.T) (σ : Strategy L ι κ)
    (hσ : (stp sel).AdmissibleProfile e σ) (i : ι) :
    (stp sel).payNow e h i (σ i h) =
      ∑ j, if IsAvailAt h.length (stateAt e h i) ∧ σ i h = .pick j then
        stpPriceVia sel e h (riderTrip (e.R j)) else 0 := by
  have hadm := hσ i h hT
  unfold DynMech.payNow
  by_cases hc : IsAvailAt h.length (stateAt e h i) ∧ σ i h = (stp sel).dispatch e h i
  · rw [if_pos hc, pay_eq]
    obtain ⟨ha, hd⟩ := hc
    rw [dispatch_eq] at hd
    rw [← hd]
    rcases hs : σ i h with b | j0 | _ | _
    · symm; apply Finset.sum_eq_zero; intro j _; rw [if_neg]; simp
    · simp only [DAction.pick.injEq]
      rw [Finset.sum_eq_single j0]
      · simp [ha]
      · intro j _ hj; rw [if_neg]; intro h1; exact hj h1.2.symm
      · simp
    · symm; apply Finset.sum_eq_zero; intro j _; rw [if_neg]; simp
    · symm; apply Finset.sum_eq_zero; intro j _; rw [if_neg]; simp
  · rw [if_neg hc]
    symm; apply Finset.sum_eq_zero; intro j _
    rw [if_neg]
    rintro ⟨ha, hp⟩
    apply hc
    refine ⟨ha, ?_⟩
    rw [dispatch_eq, (pick_dispatched sel e h i _ hadm j hp).2, hp]

theorem bb_main (he : e.Valid) (hsel : IsOptimalSelector sel) (σ : Strategy L ι κ)
    (hσ : (stp sel).AdmissibleProfile e σ) :
    ∑ j, (stp sel).riderCharge e σ [] j = ∑ i, (stp sel).totalPay e σ i := by
  -- the right-hand side
  have hR : ∑ i, (stp sel).totalPay e σ i = ∑ j, ∑ k ∈ Finset.range e.P.T,
      ((Finset.univ.filter fun i => IsAvailAt (playFrom σ [] k).length
          (stateAt e (playFrom σ [] k) i) ∧ σ i (playFrom σ [] k) = .pick j).card : ℝ) *
        stpPriceVia sel e (playFrom σ [] k) (riderTrip (e.R j)) := by
    unfold DynMech.totalPay
    rw [Finset.sum_comm]
    have : ∀ k ∈ Finset.range e.P.T, ∑ i, (stp sel).payNow e (playFrom σ [] k) i
        (σ i (playFrom σ [] k)) = ∑ j,
          ((Finset.univ.filter fun i => IsAvailAt (playFrom σ [] k).length
            (stateAt e (playFrom σ [] k) i) ∧ σ i (playFrom σ [] k) = .pick j).card : ℝ) *
          stpPriceVia sel e (playFrom σ [] k) (riderTrip (e.R j)) := by
      intro k hk
      have hkT : (playFrom σ [] k).length < e.P.T := by
        rw [playFrom_length]; simp only [List.length_nil, zero_add]
        exact Finset.mem_range.mp hk
      simp_rw [payNow_split sel e _ hkT σ hσ]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
  rw [hR]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hτT : (e.R j).τ < e.P.T := by
    have h1 := he.2.2.2 j
    have h2 := he.1.1 (e.R j).o (e.R j).d
    simp only [Params.IsTrip, riderTrip] at h1
    omega
  have hreach : ∀ k, k < e.P.T → (stp sel).Reachable e (playFrom σ [] k) :=
    fun k hk => reach_play sel e σ hσ k (le_of_lt hk)
  rw [Finset.sum_eq_single (e.R j).τ]
  · -- the rider's term
    unfold DynMech.riderCharge riderPicked pickCount histAt
    simp only [List.length_nil, Nat.sub_zero]
    set H := playFrom σ [] (e.R j).τ
    show stpPriceVia sel e H (riderTrip (e.R j)) *
        ((Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e H) H i = .pick j).card : ℝ) *
        _ = _
    have hD := dispCount_le sel e he hsel H (hreach _ hτT) j
    have hsub : (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
        σ i H = .pick j) ⊆
        (Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e H) H i = .pick j) := by
      intro i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro hi
      have hHT : H.length < e.P.T := by
        simp only [H]; rw [playFrom_length]; simpa using hτT
      exact (pick_dispatched sel e H i _ (hσ i H hHT) j hi.2).2
    have hle := Finset.card_le_card hsub
    rcases Nat.eq_zero_or_pos (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
        σ i H = .pick j).card with h0 | h0
    · rw [h0]; simp
    · have h1 : (Finset.univ.filter fun i =>
          stpDispatchVia sel e (replanTime sel e H) H i = .pick j).card = 1 := by omega
      rw [h1]; push_cast; ring
  · intro k hk hkj
    have hkT := Finset.mem_range.mp hk
    rw [Finset.card_eq_zero.mpr]
    · simp
    · rw [Finset.filter_eq_empty_iff]
      rintro i - ⟨_, hp⟩
      have hHT : (playFrom σ [] k).length < e.P.T := by rw [playFrom_length]; simpa using hkT
      have hd := pick_dispatched sel e _ i _ (hσ i _ hHT) j hp
      have := (pick_facts sel e he hsel _ (hreach k hkT) i j hd.2).2.1
      rw [playFrom_length] at this
      simp at this
      exact hkj this.symm
  · intro h; exact absurd (Finset.mem_range.mpr hτT) h

omit [Fintype L] in
theorem reach_drop : ∀ (h : Hist L ι κ) (n : ℕ), (stp sel).Reachable e h →
    (stp sel).Reachable e (h.drop n)
  | [], _, _ => by simp [DynMech.Reachable]
  | _ :: _, 0, hr => by simpa using hr
  | _ :: h, n + 1, hr => by simpa using reach_drop h n hr.1

theorem stpPrice_inst {ι0 κ0 : Type} (e0 : Econ L ι0 κ0) (i1 i2 : Fintype ι0) (k1 k2 : Fintype κ0)
    (tr : Trip L) : @Econ.stpPrice L ι0 κ0 i1 k1 e0 tr = @Econ.stpPrice L ι0 κ0 i2 k2 e0 tr := by
  obtain rfl := Subsingleton.elim i1 i2
  obtain rfl := Subsingleton.elim k1 k2
  rfl

/-- The rider-trip price used by the mechanism is at most the value of a rider who is dispatched
a driver: a consequence of Step 1 (the STP plan is a CE). -/
theorem price_le_value (hS1 : Step1CE L) (he : e.Valid) (hsel : IsOptimalSelector sel)
    (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (i : ι) (j : κ)
    (hp : stpDispatchVia sel e (replanTime sel e h) h i = .pick j) :
    stpPriceVia sel e h (riderTrip (e.R j)) ≤ (e.R j).v := by
  obtain ⟨_, _, hmemZ⟩ := pick_facts sel e he hsel h hr i j hp
  obtain ⟨hle, _, _, _⟩ := good_of_reachable sel e he hsel h hr
  unfold stpPriceVia
  by_cases h0 : replanTime sel e h = 0
  · rw [if_pos h0]
    have hz : curZ sel e h i = (sel e).z i := by simp [curZ, h0]
    rw [hz] at hmemZ
    have hd := hsel e he
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hd.1
    have hce := hS1 e he (sel e) hd
    have hx : (sel e).x j = 1 := by
      have h1 : (sel e).x j ≤ 1 := hf4 j
      have h2 : 1 ≤ (sel e).x j := by
        rw [hf3 j]
        apply Finset.card_pos.mpr
        exact ⟨i, by simpa using hmemZ⟩
      omega
    exact hce.2.1 j |>.2 hx
  · rw [if_neg h0]
    set t0 := replanTime sel e h with ht0
    set pre := h.drop (h.length - t0) with hpre
    have hlen : pre.length = t0 := by simp only [pre, List.length_drop]; omega
    have hrp : (stp sel).Reachable e pre := reach_drop sel e h _ hr
    obtain ⟨_, hVp, _, _⟩ := good_of_reachable sel e he hsel pre hrp
    have hval := econAt_valid e he pre hVp
    have hd := hsel (shiftEcon e pre) hval
    obtain ⟨hf1, hf2, hf3, hf4⟩ := hd.1
    have hce := hS1 (shiftEcon e pre) hval (sel (shiftEcon e pre)) hd
    have hz : curZ sel e h i = if hi : stateAt e pre i ≠ .gone then
        ((sel (shiftEcon e pre)).z ⟨i, hi⟩).map (shiftBack t0) else [] := by
      unfold curZ; rw [if_neg h0]
    rw [hz] at hmemZ
    by_cases hi : stateAt e pre i ≠ .gone
    · rw [dif_pos hi] at hmemZ
      obtain ⟨st0, hst0, hst0e⟩ := List.mem_map.mp hmemZ
      have h2 := congrArg Prod.snd hst0e
      simp only [shiftBack, Option.map_eq_some_iff] at h2
      obtain ⟨j0, hj0, hj0v⟩ := h2
      have htag := hf2 ⟨i, hi⟩ st0 hst0 j0 hj0
      have hx : (sel (shiftEcon e pre)).x j0 = 1 := by
        have h1 : (sel (shiftEcon e pre)).x j0 ≤ 1 := hf4 j0
        have h2 : 1 ≤ (sel (shiftEcon e pre)).x j0 := by
          rw [hf3 j0]
          apply Finset.card_pos.mpr
          refine ⟨⟨i, hi⟩, ?_⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have e2 : st0 = (st0.1, st0.2) := rfl
          rw [e2, htag, hj0] at hst0; exact hst0
        omega
      have key := hce.2.1 j0 |>.2 hx
      subst hj0v
      rw [stpPrice_inst _ _ (inferInstance) _ (inferInstance)]
      have hv : ((shiftEcon e pre).R j0).v = (e.R j0.1).v := rfl
      have htr : riderTrip ((shiftEcon e pre).R j0) = ((riderTrip (e.R j0.1)).1,
          (riderTrip (e.R j0.1)).2.1, (riderTrip (e.R j0.1)).2.2 - t0) := by
        simp only [riderTrip, shiftEcon, econAt, hlen]
      rw [htr, hv] at key
      exact key
    · rw [dif_neg hi] at hmemZ; simp at hmemZ

theorem rir_main (hS1 : Step1CE L) (he : e.Valid) (hsel : IsOptimalSelector sel) (σ : Strategy L ι κ)
    (hσ : (stp sel).AdmissibleProfile e σ) (j : κ) :
    (stp sel).riderCharge e σ [] j ≤ (riderPicked e σ [] j : ℝ) * (e.R j).v := by
  have hτT : (e.R j).τ < e.P.T := by
    have h1 := he.2.2.2 j
    have h2 := he.1.1 (e.R j).o (e.R j).d
    simp only [Params.IsTrip, riderTrip] at h1
    omega
  unfold DynMech.riderCharge riderPicked pickCount histAt
  simp only [List.length_nil, Nat.sub_zero]
  set H := playFrom σ [] (e.R j).τ
  have hHr : (stp sel).Reachable e H := reach_play sel e σ hσ _ (le_of_lt hτT)
  have hHT : H.length < e.P.T := by simp only [H]; rw [playFrom_length]; simpa using hτT
  show stpPriceVia sel e H (riderTrip (e.R j)) *
      ((Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e H) H i = .pick j).card : ℝ) *
      _ ≤ _
  have hD := dispCount_le sel e he hsel H hHr j
  have hsub : (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
      σ i H = .pick j) ⊆
      (Finset.univ.filter fun i => stpDispatchVia sel e (replanTime sel e H) H i = .pick j) := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro hi
    exact (pick_dispatched sel e H i _ (hσ i H hHT) j hi.2).2
  have hle := Finset.card_le_card hsub
  rcases Nat.eq_zero_or_pos (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
      σ i H = .pick j).card with h0 | h0
  · rw [h0]; simp
  · have h1 : (Finset.univ.filter fun i =>
        stpDispatchVia sel e (replanTime sel e H) H i = .pick j).card = 1 := by omega
    have h2 : (Finset.univ.filter fun i => IsAvailAt H.length (stateAt e H i) ∧
        σ i H = .pick j).card = 1 := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h0
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hp := (pick_dispatched sel e H i _ (hσ i H hHT) j hi.2).2
    have := price_le_value sel e hS1 he hsel H hHr i j hp
    rw [h1, h2]; push_cast; linarith

end Global

/-- The milestone "Step 1 as used in Step 2" (continuation utility of an available driver). -/
def Step1Cont [Fintype L] (sel : Selector L) : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ), e.Valid →
    ∀ (h : Hist L ι κ), (stp sel).Reachable e h → h.length < e.P.T →
      ∀ (i : ι) (β : Bool) (a : L), stateAt e h i = .wait β a h.length →
        (stp sel).contUtil e ((stp sel).sigmaStar e) h i =
          if β = true then
            PhiShift e (replanTime sel e h)
              (stateAt e (h.drop (h.length - replanTime sel e h))) a h.length
          else
            max (PhiShift e (replanTime sel e h)
              (stateAt e (h.drop (h.length - replanTime sel e h))) a h.length) 0

section Cont

variable [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ] (e : Econ L ι κ)

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem playFrom_add (σ : Strategy L ι κ) (h : Hist L ι κ) (m : ℕ) :
    ∀ k, playFrom σ (playFrom σ h m) k = playFrom σ h (m + k)
  | 0 => rfl
  | k + 1 => by
    show (fun i => σ i (playFrom σ (playFrom σ h m) k)) :: playFrom σ (playFrom σ h m) k =
      (fun i => σ i (playFrom σ h (m + k))) :: playFrom σ h (m + k)
    rw [playFrom_add σ h m k]

omit [Fintype L] in
theorem utilNow_notAvail (h : Hist L ι κ) (i : ι) (α : DAction L κ)
    (hn : ¬ IsAvailAt h.length (stateAt e h i)) : (stp sel).utilNow e h i α = 0 := by
  unfold DynMech.utilNow DynMech.payNow costNow
  rw [if_neg (fun hc => hn hc.1)]
  revert hn
  cases stateAt e h i with
  | wait β a τ =>
    intro hn
    simp only [IsAvailAt] at hn
    cases α <;> simp [hn]
  | enroute => intro _; cases α <;> simp
  | gone => intro _; cases α <;> simp

omit [Fintype L] in
theorem contUtil_shift (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (m : ℕ)
    (hm : h.length + m ≤ e.P.T)
    (hz : ∀ k < m, (stp sel).utilNow e (playFrom σ h k) i (σ i (playFrom σ h k)) = 0) :
    (stp sel).contUtil e σ h i = (stp sel).contUtil e σ (playFrom σ h m) i := by
  unfold DynMech.contUtil
  rw [playFrom_length, show e.P.T - h.length = m + (e.P.T - (h.length + m)) by omega,
    Finset.sum_range_add]
  rw [Finset.sum_eq_zero (fun k hk => hz k (Finset.mem_range.mp hk)), zero_add]
  simp_rw [playFrom_add]

omit [Fintype L] in
theorem dispatch_mem_actions (h : Hist L ι κ) (i : ι) :
    (stp sel).dispatch e h i ∈ (stp sel).actions e h i := by
  unfold DynMech.dispatch DynMech.actions
  revert ‹Fintype ι›
  intro _
  rcases hs : stateAt e h i with ⟨β, a, τ⟩ | _ | _
  · by_cases hτ : τ = h.length
    · simp only [IsAvailAt, hτ, if_true]
      left; left; rfl
    · simp [IsAvailAt, hτ]
  · simp [IsAvailAt]
  · simp [IsAvailAt]

omit [Fintype L] in
theorem reach_star (h : Hist L ι κ) (hr : (stp sel).Reachable e h) :
    ∀ k, h.length + k ≤ e.P.T → (stp sel).Reachable e (playFrom ((stp sel).sigmaStar e) h k)
  | 0, _ => hr
  | k + 1, hk => by
    refine ⟨reach_star h hr k (by omega), ?_, ?_⟩
    · rw [playFrom_length]; omega
    · intro i; exact dispatch_mem_actions sel e _ i

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem wait_stays (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (β : Bool) (a : L) (τ : ℕ)
    (hs : stateAt e h i = .wait β a τ) :
    ∀ k, h.length + k ≤ τ → stateAt e (playFrom σ h k) i = .wait β a τ
  | 0, _ => by simpa [playFrom] using hs
  | k + 1, hk => by
    show step e.P e.R (playFrom σ h k).length (stateAt e (playFrom σ h k) i) _ = _
    rw [wait_stays σ h i β a τ hs k (by omega), playFrom_length]
    simp only [step]
    rw [if_neg (by omega)]

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem gone_stays (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι)
    (hs : stateAt e h i = .gone) : ∀ k, stateAt e (playFrom σ h k) i = .gone
  | 0 => by simpa [playFrom] using hs
  | k + 1 => by
    show step e.P e.R (playFrom σ h k).length (stateAt e (playFrom σ h k) i) _ = _
    rw [gone_stays σ h i hs k]
    rfl

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem enroute_stays (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (a b : L) (t' : ℕ)
    (j : Option κ) (hs : stateAt e h i = .enroute a b t' j) :
    ∀ k, h.length + k < t' + e.P.δ a b → stateAt e (playFrom σ h k) i = .enroute a b t' j
  | 0, _ => by simpa [playFrom] using hs
  | k + 1, hk => by
    show step e.P e.R (playFrom σ h k).length (stateAt e (playFrom σ h k) i) _ = _
    rw [enroute_stays σ h i a b t' j hs k (by omega), playFrom_length]
    simp only [step]
    rw [if_neg (by omega)]

omit [Fintype L] [Fintype ι] [Fintype κ] in
theorem enroute_arrive (σ : Strategy L ι κ) (h : Hist L ι κ) (i : ι) (a b : L) (t' : ℕ)
    (j : Option κ) (hs : stateAt e h i = .enroute a b t' j) (hlt : h.length < t' + e.P.δ a b) :
    stateAt e (playFrom σ h (t' + e.P.δ a b - h.length)) i = .wait true b (t' + e.P.δ a b) := by
  obtain ⟨m, hm⟩ : ∃ m, t' + e.P.δ a b - h.length = m + 1 := ⟨t' + e.P.δ a b - h.length - 1, by omega⟩
  rw [hm]
  show step e.P e.R (playFrom σ h m).length (stateAt e (playFrom σ h m) i) _ = _
  rw [enroute_stays e σ h i a b t' j hs m (by omega), playFrom_length]
  simp only [step]
  rw [if_pos (by omega), show h.length + m + 1 = t' + e.P.δ a b by omega]

/-- Continuation utility of a driver who next becomes available at time `u` in state
`(β, a, u)`, computed at that time. -/
theorem cont_arrival (hS : Step1Cont sel) (he : e.Valid) (h : Hist L ι κ)
    (hr : (stp sel).Reachable e h) (i : ι) (u : ℕ) (β : Bool) (a : L)
    (hu1 : h.length ≤ u) (hu2 : u ≤ e.P.T)
    (hz : ∀ k < u - h.length, ¬ IsAvailAt (playFrom ((stp sel).sigmaStar e) h k).length
      (stateAt e (playFrom ((stp sel).sigmaStar e) h k) i))
    (hs : stateAt e (playFrom ((stp sel).sigmaStar e) h (u - h.length)) i = .wait β a u) :
    (stp sel).contUtil e ((stp sel).sigmaStar e) h i =
      if u < e.P.T then
        (if β = true then
          PhiShift e (replanTime sel e (playFrom ((stp sel).sigmaStar e) h (u - h.length)))
            (stateAt e ((playFrom ((stp sel).sigmaStar e) h (u - h.length)).drop
              ((playFrom ((stp sel).sigmaStar e) h (u - h.length)).length -
                replanTime sel e (playFrom ((stp sel).sigmaStar e) h (u - h.length))))) a
            (playFrom ((stp sel).sigmaStar e) h (u - h.length)).length
        else
          max (PhiShift e (replanTime sel e (playFrom ((stp sel).sigmaStar e) h (u - h.length)))
            (stateAt e ((playFrom ((stp sel).sigmaStar e) h (u - h.length)).drop
              ((playFrom ((stp sel).sigmaStar e) h (u - h.length)).length -
                replanTime sel e (playFrom ((stp sel).sigmaStar e) h (u - h.length))))) a
            (playFrom ((stp sel).sigmaStar e) h (u - h.length)).length) 0)
      else 0 := by
  have hlen : (playFrom ((stp sel).sigmaStar e) h (u - h.length)).length = u := by
    rw [playFrom_length]; omega
  rw [contUtil_shift sel e _ h i (u - h.length) (by omega)
    (fun k hk => utilNow_notAvail sel e _ i _ (hz k hk))]
  by_cases hT : u < e.P.T
  · rw [if_pos hT]
    have hr' := reach_star sel e h hr (u - h.length) (by omega)
    rw [hS e he _ hr' (by rw [hlen]; exact hT) i β a (by rw [hlen]; exact hs)]
  · rw [if_neg hT]
    unfold DynMech.contUtil
    rw [hlen, show e.P.T - u = 0 by omega]
    simp

end Cont

end BBAux

end STPRideshare.Mechanism



namespace STPRideshare.Mechanism

open scoped Classical

namespace BBAux

theorem cont_gone {L : Type} [Fintype L] (sel : Selector L) {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : Econ L ι κ) (h : Hist L ι κ) (hT : h.length ≤ e.P.T) (i : ι)
    (hs : stateAt e h i = .gone) :
    (stp sel).contUtil e ((stp sel).sigmaStar e) h i = 0 := by
  rw [contUtil_shift sel e _ h i (e.P.T - h.length) (by omega) (fun k _ => utilNow_notAvail sel e _ i _
    (by rw [gone_stays e _ h i hs k]; simp [IsAvailAt]))]
  unfold DynMech.contUtil
  rw [playFrom_length, show e.P.T - (h.length + (e.P.T - h.length)) = 0 by omega]
  simp

theorem dir_main {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel)
    (hS : Step1Cont sel) : DriverIRFromAnyHistory (stp sel) := by
  intro ι κ _ _ e he h hr hT i a τ hs
  obtain ⟨_, hV, _, _⟩ := good_of_reachable sel e he hsel h hr
  have hinv := stInv_stateAt e h i
  rw [hs] at hinv; simp only [StInv] at hinv
  have hVi := hV i
  rw [hs] at hVi; simp only [V] at hVi
  rw [cont_arrival sel e hS he h hr i τ false a hinv hVi ?_ ?_]
  · split_ifs <;> first | contradiction | simp
  · intro k hk
    rw [wait_stays e _ h i false a τ hs k (by omega), playFrom_length]
    simp only [IsAvailAt]; omega
  · exact wait_stays e _ h i false a τ hs _ (by omega)

end BBAux

end STPRideshare.Mechanism

open STPRideshare.Mechanism in
theorem solution {L : Type} [Fintype L] (sel : Selector L) (hsel : IsOptimalSelector sel) :
    DriverIRFromAnyHistory (stp sel) :=
  BBAux.dir_main sel hsel (fun e he h hh ht i β a hs =>
    step1_continuation_utility sel hsel e he h hh ht i β a hs)
