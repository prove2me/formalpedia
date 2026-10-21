-- Prove2me | solution 1 for SampleComplexityRL.Exploration.deterministic_sample_complexity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:56:09.414562+00:00
-- url     : https://prove2.me/submissions/e6e44389-801b-4fab-a102-ab386c391a7f

import Mathlib
import Definitions.Def_SampleComplexityRL_Exploration_Online

set_option autoImplicit false
open SampleComplexityRL.Exploration

namespace SCRRmax

section Defs
variable {S A : Type}

/-- one-step optimistic value of action `a` in state `s` under a partial model `m`:
a known pair contributes its reward plus the continuation value, an unknown pair is
credited with the maximal reward `1/T` at every one of the `k+1` remaining steps. -/
noncomputable def qv (T : ℕ) (m : S → A → Option (S × ℝ)) (k : ℕ) (Wk : S → ℝ) (s : S) (a : A) :
    ℝ :=
  match m s a with
  | some p => (1 / (T : ℝ)) * p.2 + Wk p.1
  | none => ((k + 1 : ℕ) : ℝ) * (1 / (T : ℝ))

/-- optimistic `k`-step value under the partial model `m`. -/
noncomputable def W [Fintype A] [Nonempty A] (T : ℕ) (m : S → A → Option (S × ℝ)) :
    ℕ → S → ℝ
  | 0, _ => 0
  | k + 1, s => Finset.univ.sup' Finset.univ_nonempty (fun a => qv T m k (W T m k) s a)

theorem W_exists [Fintype A] [Nonempty A] (T : ℕ) (m : S → A → Option (S × ℝ)) (k : ℕ) (s : S) :
    ∃ a, W T m (k + 1) s = qv T m k (W T m k) s a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := A))
    (fun a => qv T m k (W T m k) s a)
  exact ⟨a, by simpa only [W] using ha⟩

noncomputable def pick [Fintype A] [Nonempty A] (T : ℕ) (m : S → A → Option (S × ℝ)) (k : ℕ)
    (s : S) : A := Classical.choose (W_exists T m k s)

theorem pick_spec [Fintype A] [Nonempty A] (T : ℕ) (m : S → A → Option (S × ℝ)) (k : ℕ)
    (s : S) : W T m (k + 1) s = qv T m k (W T m k) s (pick T m k s) :=
  Classical.choose_spec (W_exists T m k s)

open Classical in
/-- the model learned from the observed history `h` with current state `cur`: for a pair `(s,a)`
occurring in `h`, its observed next state and reward; `none` for pairs not yet tried. -/
noncomputable def lookup (h : List (S × A × ℝ)) (cur : S) (s : S) (a : A) : Option (S × ℝ) :=
  if hx : ∃ i : ℕ, ∃ x : S × A × ℝ, h[i]? = some x ∧ x.1 = s ∧ x.2.1 = a then
    some (((h[Classical.choose hx + 1]?).map (fun x => x.1)).getD cur,
          ((h[Classical.choose hx]?).map (fun x => x.2.2)).getD 0)
  else none

/-- the optimistic ("R_max with m = 1") algorithm: act greedily w.r.t. the optimistic value
computed in the model learned from the history, for the number of steps left in the block. -/
noncomputable def rmax [Fintype A] [Nonempty A] (T : ℕ) : OnlineAlg S A := fun h cur =>
  pick T (lookup h cur) (endTime T h.length - h.length - 1) cur

open Classical in
noncomputable def trueModel (f : S → A → S) (r : S → A → ℝ) (D : Set (S × A)) :
    S → A → Option (S × ℝ) :=
  fun s a => if (s, a) ∈ D then some (f s a, r s a) else none

end Defs

section Run
variable {S A : Type} (f : S → A → S) (r : S → A → ℝ) (alg : OnlineAlg S A) (s0 : S)

theorem hist_len (τ : ℕ) : (history f r alg s0 τ).1.length = τ := by
  induction τ with
  | zero => simp [history]
  | succ τ ih => simp [history, ih]

theorem runState_succ (τ : ℕ) :
    runState f r alg s0 (τ + 1) = f (runState f r alg s0 τ) (runAction f r alg s0 τ) := rfl

theorem hist_get (τ i : ℕ) : (history f r alg s0 τ).1[i]? =
    if i < τ then some (runState f r alg s0 i, runAction f r alg s0 i,
      r (runState f r alg s0 i) (runAction f r alg s0 i)) else none := by
  induction τ with
  | zero => simp [history]
  | succ τ ih =>
    have e : (history f r alg s0 (τ + 1)).1 = (history f r alg s0 τ).1 ++
        [(runState f r alg s0 τ, runAction f r alg s0 τ,
          r (runState f r alg s0 τ) (runAction f r alg s0 τ))] := rfl
    rw [e]
    by_cases hi : i < τ
    · rw [List.getElem?_append_left (by rw [hist_len]; exact hi), ih]
      simp [hi, show i < τ + 1 by omega]
    · rw [List.getElem?_append_right (by rw [hist_len]; omega), hist_len]
      by_cases hi2 : i = τ
      · subst hi2; simp
      · have : i - τ = (i - τ - 1) + 1 := by omega
        rw [this]
        simp [hi, show ¬ i < τ + 1 by omega]

/-- the set of pairs played before time `τ`. -/
def D (τ : ℕ) : Set (S × A) :=
  {p | ∃ i < τ, (runState f r alg s0 i, runAction f r alg s0 i) = p}

theorem lookup_run (τ : ℕ) :
    lookup (history f r alg s0 τ).1 (history f r alg s0 τ).2 = trueModel f r (D f r alg s0 τ) := by
  classical
  funext s a
  unfold lookup trueModel
  by_cases hx : ∃ i : ℕ, ∃ x : S × A × ℝ, (history f r alg s0 τ).1[i]? = some x ∧ x.1 = s ∧ x.2.1 = a
  · rw [dif_pos hx]
    have spec := Classical.choose_spec hx
    generalize Classical.choose hx = i at spec ⊢
    clear hx
    obtain ⟨x, hx1, hx2, hx3⟩ := spec
    rw [hist_get] at hx1
    have hiτ : i < τ := by
      by_contra hc; rw [if_neg hc] at hx1; exact absurd hx1 (by simp)
    rw [if_pos hiτ] at hx1
    have hxx := Option.some.inj hx1
    subst hxx
    simp only [] at hx2 hx3
    subst hx2; subst hx3
    have hmem : (runState f r alg s0 i, runAction f r alg s0 i) ∈ D f r alg s0 τ := ⟨i, hiτ, rfl⟩
    rw [if_pos hmem]
    congr 1
    simp only [hist_get, if_pos hiτ, Option.map_some, Option.getD_some]
    rw [Prod.mk.injEq]
    constructor
    · by_cases h1 : i + 1 < τ
      · simp [h1]; rfl
      · have : τ = i + 1 := by omega
        simp [h1]
        subst this; rfl
    · rfl
  · rw [dif_neg hx]
    have hmem : (s, a) ∉ D f r alg s0 τ := by
      rintro ⟨i, hiτ, hp⟩
      apply hx
      have hp1 := (Prod.mk.inj hp).1
      have hp2 := (Prod.mk.inj hp).2
      exact ⟨i, (runState f r alg s0 i, runAction f r alg s0 i,
          r (runState f r alg s0 i) (runAction f r alg s0 i)),
        by rw [hist_get, if_pos hiτ], hp1, hp2⟩
    rw [if_neg hmem]

end Run


section EndTime

theorem endTime_gt {T : ℕ} (hT : 0 < T) (t : ℕ) : t < endTime T t := by
  unfold endTime
  have h := Nat.div_add_mod t T
  have h2 := Nat.mod_lt t hT
  nlinarith

theorem endTime_le {T : ℕ} (hT : 0 < T) (t : ℕ) : endTime T t ≤ t + T := by
  unfold endTime
  have h := Nat.div_mul_le_self t T
  nlinarith

theorem endTime_eq {T : ℕ} (hT : 0 < T) {t τ : ℕ} (h1 : t ≤ τ) (h2 : τ < endTime T t) :
    endTime T τ = endTime T t := by
  have hdiv : τ / T = t / T := by
    apply Nat.div_eq_of_lt_le
    · exact le_trans (Nat.div_mul_le_self t T) h1
    · exact h2
  unfold endTime; rw [hdiv]

end EndTime

section Analysis
variable {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
  (T : ℕ) (f : S → A → S) (r : S → A → ℝ) (s0 : S)

theorem act_spec (τ : ℕ) :
    W T (trueModel f r (D f r (rmax T) s0 τ)) (endTime T τ - τ - 1 + 1)
        (runState f r (rmax T) s0 τ) =
      qv T (trueModel f r (D f r (rmax T) s0 τ)) (endTime T τ - τ - 1)
        (W T (trueModel f r (D f r (rmax T) s0 τ)) (endTime T τ - τ - 1))
        (runState f r (rmax T) s0 τ) (runAction f r (rmax T) s0 τ) := by
  have h1 : runAction f r (rmax T) s0 τ =
      pick T (trueModel f r (D f r (rmax T) s0 τ)) (endTime T τ - τ - 1)
        (runState f r (rmax T) s0 τ) := by
    simp only [runAction, rmax, hist_len, lookup_run]
    rfl
  rw [h1]
  exact pick_spec T _ _ _

theorem D_mono {τ τ' : ℕ} (h : τ ≤ τ') : D f r (rmax T) s0 τ ⊆ D f r (rmax T) s0 τ' := by
  rintro p ⟨i, hi, hp⟩
  exact ⟨i, lt_of_lt_of_le hi h, hp⟩

theorem D_window (t n : ℕ)
    (hwin : ∀ τ, t ≤ τ → τ < t + n →
      (runState f r (rmax T) s0 τ, runAction f r (rmax T) s0 τ) ∈ D f r (rmax T) s0 t) :
    ∀ j, j ≤ n → D f r (rmax T) s0 (t + j) ⊆ D f r (rmax T) s0 t := by
  intro j
  induction j with
  | zero => intro _; exact fun p hp => hp
  | succ j ih =>
    intro hj p hp
    obtain ⟨i, hi, hpi⟩ := hp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact ih (by omega) ⟨i, h, hpi⟩
    · subst hpi
      have : i = t + j := by omega
      rw [this]
      exact hwin (t + j) (by omega) (by omega)

theorem window_value {T : ℕ} (hT : 0 < T) (t : ℕ)
    (hwin : ∀ τ, t ≤ τ → τ < endTime T t →
      (runState f r (rmax T) s0 τ, runAction f r (rmax T) s0 τ) ∈ D f r (rmax T) s0 t) :
    algValue f r T (rmax T) s0 t =
      W T (trueModel f r (D f r (rmax T) s0 t)) (endTime T t - t) (runState f r (rmax T) s0 t) := by
  have hgt := endTime_gt hT t
  obtain ⟨kk, hkk⟩ : ∃ kk, kk = endTime T t - t := ⟨_, rfl⟩
  rw [← hkk]
  set E := D f r (rmax T) s0 t with hE
  set M := trueModel f r E with hM
  have hDτ : ∀ j, j ≤ kk → D f r (rmax T) s0 (t + j) = E := by
    intro j hj
    apply Set.Subset.antisymm
    · exact D_window T f r s0 t kk (fun τ h1 h2 => hwin τ h1 (by omega)) j hj
    · exact D_mono T f r s0 (by omega)
  have key : ∀ j, j ≤ kk →
      (1 / (T : ℝ)) * ∑ τ ∈ Finset.Ico t (t + j),
        r (runState f r (rmax T) s0 τ) (runAction f r (rmax T) s0 τ)
        + W T M (kk - j) (runState f r (rmax T) s0 (t + j))
      = W T M kk (runState f r (rmax T) s0 t) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hτ : t + j < endTime T t := by omega
      have hend : endTime T (t + j) = endTime T t := endTime_eq hT (by omega) hτ
      have hs := act_spec T f r s0 (t + j)
      rw [hDτ j (by omega)] at hs
      have hk2 : endTime T (t + j) - (t + j) - 1 = kk - (j + 1) := by omega
      have hk3 : kk - j = kk - (j + 1) + 1 := by omega
      rw [hk2, ← hk3] at hs
      have hmem := hwin (t + j) (by omega) hτ
      have hq : qv T M (kk - (j + 1)) (W T M (kk - (j + 1)))
          (runState f r (rmax T) s0 (t + j)) (runAction f r (rmax T) s0 (t + j)) =
          (1 / (T : ℝ)) * r (runState f r (rmax T) s0 (t + j)) (runAction f r (rmax T) s0 (t + j))
            + W T M (kk - (j + 1)) (runState f r (rmax T) s0 (t + j + 1)) := by
        unfold qv
        simp only [hM, trueModel, if_pos hmem]
        rw [runState_succ]
      rw [hq] at hs
      rw [← add_assoc, Finset.sum_Ico_succ_top (by omega : t ≤ t + j), mul_add]
      linarith
  have := key kk le_rfl
  rw [Nat.sub_self] at this
  have e : t + kk = endTime T t := by omega
  rw [e] at this
  unfold algValue
  rw [← this]
  simp [W]

theorem optSteps_le_mul (hr : ∀ s a, r s a ≤ 1) (hT : 0 < T) (k : ℕ) (s : S) :
    optSteps f r T k s ≤ (k : ℝ) * (1 / (T : ℝ)) := by
  induction k generalizing s with
  | zero => simp [optSteps]
  | succ k ih =>
    unfold optSteps
    apply Finset.sup'_le
    intro a _
    have h1 : (1 / (T : ℝ)) * r s a ≤ (1 / (T : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (hr s a) (by positivity)
    have h2 := ih (f s a)
    push_cast
    linarith

theorem optSteps_le_W (hr : ∀ s a, r s a ≤ 1) (hT : 0 < T) (E : Set (S × A)) (k : ℕ) :
    ∀ s, optSteps f r T k s ≤ W T (trueModel f r E) k s := by
  induction k with
  | zero => intro s; simp [optSteps, W]
  | succ k ih =>
    intro s
    unfold optSteps
    apply Finset.sup'_le
    intro a _
    have hle : qv T (trueModel f r E) k (W T (trueModel f r E) k) s a ≤
        W T (trueModel f r E) (k + 1) s := by
      rw [W]
      exact Finset.le_sup' (fun a => qv T (trueModel f r E) k (W T (trueModel f r E) k) s a)
        (Finset.mem_univ a)
    refine le_trans ?_ hle
    unfold qv
    by_cases hm : (s, a) ∈ E
    · simp only [trueModel, if_pos hm]
      have := ih (f s a)
      linarith
    · simp only [trueModel, if_neg hm]
      have h1 : (1 / (T : ℝ)) * r s a ≤ (1 / (T : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (hr s a) (by positivity)
      have h2 := optSteps_le_mul T f r hr hT k (f s a)
      push_cast
      linarith

theorem sum_le_opt (alg : OnlineAlg S A) (n : ℕ) :
    ∀ τ0, (1 / (T : ℝ)) * ∑ τ ∈ Finset.Ico τ0 (τ0 + n),
        r (runState f r alg s0 τ) (runAction f r alg s0 τ)
      ≤ optSteps f r T n (runState f r alg s0 τ0) := by
  induction n with
  | zero => intro τ0; simp [optSteps]
  | succ n ih =>
    intro τ0
    have e : τ0 + (n + 1) = τ0 + 1 + n := by omega
    rw [e, Finset.sum_eq_sum_Ico_succ_bot (by omega : τ0 < τ0 + 1 + n), mul_add]
    have h1 := ih (τ0 + 1)
    rw [runState_succ] at h1
    have h2 : (1 / (T : ℝ)) * r (runState f r alg s0 τ0) (runAction f r alg s0 τ0) +
        optSteps f r T n (f (runState f r alg s0 τ0) (runAction f r alg s0 τ0)) ≤
        optSteps f r T (n + 1) (runState f r alg s0 τ0) := by
      exact Finset.le_sup' (fun a => (1 / (T : ℝ)) * r (runState f r alg s0 τ0) a +
        optSteps f r T n (f (runState f r alg s0 τ0) a)) (Finset.mem_univ (runAction f r alg s0 τ0))
    linarith

theorem good_time (hr : ∀ s a, r s a ≤ 1) {T : ℕ} (hT : 0 < T) (t : ℕ)
    (hwin : ∀ τ, t ≤ τ → τ < endTime T t →
      (runState f r (rmax T) s0 τ, runAction f r (rmax T) s0 τ) ∈ D f r (rmax T) s0 t) :
    algValue f r T (rmax T) s0 t = optValue f r T (rmax T) s0 t := by
  have hgt := endTime_gt hT t
  have h1 := window_value f r s0 hT t hwin
  have h2 := optSteps_le_W T f r hr hT (D f r (rmax T) s0 t) (endTime T t - t)
    (runState f r (rmax T) s0 t)
  have h3 : algValue f r T (rmax T) s0 t ≤ optSteps f r T (endTime T t - t)
      (runState f r (rmax T) s0 t) := by
    have := sum_le_opt T f r s0 (rmax T) (endTime T t - t) t
    have e : t + (endTime T t - t) = endTime T t := by omega
    rw [e] at this
    exact this
  unfold optValue
  apply le_antisymm h3
  rw [h1]; exact h2

theorem count_bound (hr : ∀ s a, r s a ≤ 1) {T : ℕ} (hT : 0 < T) :
    ∃ C : Finset ℕ, C.card ≤ Fintype.card S * Fintype.card A * T ∧
      ∀ t, algValue f r T (rmax T) s0 t ≠ optValue f r T (rmax T) s0 t → t ∈ C := by
  classical
  let pr : ℕ → S × A := fun τ => (runState f r (rmax T) s0 τ, runAction f r (rmax T) s0 τ)
  let Bp : S × A → Finset ℕ := fun p =>
    if h : ∃ τ, pr τ = p then Finset.Icc (Nat.find h + 1 - T) (Nat.find h) else ∅
  refine ⟨Finset.univ.biUnion Bp, ?_, ?_⟩
  · calc (Finset.univ.biUnion Bp).card ≤ ∑ p ∈ (Finset.univ : Finset (S × A)), (Bp p).card :=
          Finset.card_biUnion_le
      _ ≤ (Finset.univ : Finset (S × A)).card • T := by
          apply Finset.sum_le_card_nsmul
          intro p _
          simp only [Bp]
          split_ifs with h
          · simp only [Nat.card_Icc]; omega
          · simp
      _ = Fintype.card S * Fintype.card A * T := by
          rw [Finset.card_univ, Fintype.card_prod, smul_eq_mul]
  · intro t ht
    by_contra hnot
    apply ht
    apply good_time f r s0 hr hT t
    intro τ h1 h2
    by_contra hτ
    apply hnot
    have h : ∃ τ', pr τ' = pr τ := ⟨τ, rfl⟩
    have hle : Nat.find h ≤ τ := Nat.find_min' h rfl
    have hspec : pr (Nat.find h) = pr τ := Nat.find_spec h
    have hge : t ≤ Nat.find h := by
      by_contra hc
      push_neg at hc
      exact hτ (show pr τ ∈ D f r (rmax T) s0 t by rw [← hspec]; exact ⟨Nat.find h, hc, rfl⟩)
    have hend := endTime_le hT t
    rw [Finset.mem_biUnion]
    refine ⟨pr τ, Finset.mem_univ _, ?_⟩
    simp only [Bp, dif_pos h, Finset.mem_Icc]
    omega

end Analysis

end SCRRmax

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [DecidableEq A] [Nonempty A] (T : ℕ) (hT : 0 < T) :
    ∃ alg : OnlineAlg S A,
      ∀ (f : S → A → S) (r : S → A → ℝ), (∀ s a, 0 ≤ r s a ∧ r s a ≤ 1) →
        ∀ (s₀ : S) (L : ℕ),
          ((Finset.range L).filter
              (fun t => algValue f r T alg s₀ t ≠ optValue f r T alg s₀ t)).card
            ≤ Fintype.card S * Fintype.card A * T := by
  refine ⟨SCRRmax.rmax T, fun f r hr s₀ L => ?_⟩
  obtain ⟨C, hC, hmem⟩ := SCRRmax.count_bound f r s₀ (fun s a => (hr s a).2) hT
  calc _ ≤ C.card := Finset.card_le_card (fun t ht => hmem t (Finset.mem_filter.mp ht).2)
    _ ≤ _ := hC
