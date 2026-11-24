-- Prove2me | solution 1 for WindowedMatching.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T19:08:10.943609+00:00
-- url     : https://prove2.me/submissions/bc3d3c45-a603-47a5-b61a-77258c377c3b

import Definitions.Def_WindowedMatching_PostponedGreedy
import Theorems.Thm_WindowedMatching_disjoint_paths
import Theorems.Thm_WindowedMatching_status_alternates
import Theorems.Thm_WindowedMatching_expected_reward_eq
import Theorems.Thm_WindowedMatching_sum_price_eq_sum_margin
import Theorems.Thm_WindowedMatching_dual_feasible
import Theorems.Thm_WindowedMatching_weak_duality

namespace WindowedMatching

private theorem bid_S {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (k : Fin n) (st : State n) :
    (bid d v tie k st).S = st.S := by
  unfold bid
  dsimp only
  split_ifs <;> rfl

private theorem arrive_S {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (k : Fin n) (st : State n) :
    (arrive d v tie k st).S = insert k st.S := by
  simp [arrive, bid_S, addVertex]

private theorem critical_S_sub {n : ℕ} (ω : Fin n → Bool) (k : Fin n) (st : State n) :
    (critical ω k st).S ⊆ st.S := by
  unfold critical
  cases st.m k with
  | none => exact Finset.Subset.refl _
  | some l =>
    dsimp only
    split_ifs <;> exact Finset.erase_subset k st.S

private theorem period_mem_S {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (ω : Fin n → Bool) (t : ℕ) (st : State n) (s : Fin n)
    (hs : s ∈ (period d v tie ω t st).S) :
    (s : ℕ) = t ∨ s ∈ st.S := by
  unfold period at hs
  dsimp only at hs
  have hs₁ : s ∈ (if h : t < n then arrive d v tie ⟨t, h⟩ st else st).S := by
    by_cases hc : d ≤ t ∧ t - d < n
    · rw [dif_pos hc] at hs
      exact critical_S_sub ω ⟨t - d, hc.2⟩ _ hs
    · rw [dif_neg hc] at hs
      exact hs
  by_cases ht : t < n
  · rw [dif_pos ht, arrive_S, Finset.mem_insert] at hs₁
    rcases hs₁ with rfl | hs₀
    · exact Or.inl rfl
    · exact Or.inr hs₀
  · rw [dif_neg ht] at hs₁
    exact Or.inr hs₁

private theorem mem_S_lt {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (ω : Fin n → Bool) :
    ∀ (t : ℕ) (s : Fin n), s ∈ (stateAfter d v tie ω t).S → (s : ℕ) < t
  | 0, s, hs => by simp [stateAfter, State.init] at hs
  | t + 1, s, hs => by
    simp only [stateAfter] at hs
    rcases period_mem_S d v tie ω t (stateAfter d v tie ω t) s hs with h_eq | hs₀
    · omega
    · exact Nat.lt_succ_of_lt (mem_S_lt d v tie ω t s hs₀)

private theorem online_stateAfter {n : ℕ} (d : ℕ) (v v' : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (ω ω' : Fin n → Bool) :
    ∀ t : ℕ,
      (∀ i j : Fin n, (i : ℕ) < t → (j : ℕ) < t → v s(i, j) = v' s(i, j)) →
      (∀ k : Fin n, (k : ℕ) + d < t → ω k = ω' k) →
      stateAfter d v tie ω t = stateAfter d v' tie ω' t
  | 0, _, _ => rfl
  | t + 1, hv_eq, hω_eq => by
    have ih := online_stateAfter d v v' tie ω ω' t
      (fun i j hi hj => hv_eq i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj))
      (fun k hk => hω_eq k (Nat.lt_succ_of_lt hk))
    simp only [stateAfter]
    rw [ih]
    set st := stateAfter d v' tie ω' t
    unfold period
    have hst₁ : (if h : t < n then arrive d v tie ⟨t, h⟩ st else st) =
        (if h : t < n then arrive d v' tie ⟨t, h⟩ st else st) := by
      split_ifs with ht
      · set k : Fin n := ⟨t, ht⟩
        set st₀ := addVertex k st
        have hS_lt : ∀ s ∈ st₀.S, (s : ℕ) < t + 1 := by
          intro s hs
          simp only [st₀, addVertex, Finset.mem_insert] at hs
          rcases hs with rfl | hs'
          · exact Nat.lt_succ_self t
          · exact Nat.lt_succ_of_lt (mem_S_lt d v' tie ω' t s hs')
        have how : ∀ s ∈ st₀.S, onlineWeight d v s k = onlineWeight d v' s k := by
          intro s hs
          unfold onlineWeight
          rw [hv_eq s k (hS_lt s hs) (Nat.lt_succ_self t)]
        have hmarg : margins d v k st₀ = margins d v' k st₀ := by
          ext s
          unfold margins
          split_ifs with hs
          · rw [how s hs]
          · rfl
        simp only [arrive]
        change bid d v tie k st₀ = bid d v' tie k st₀
        unfold bid
        rw [hmarg]
        dsimp only
        split_ifs with hpos
        · have hs_mem : tie k st₀.S (margins d v' k st₀) ∈ st₀.S := by
            by_contra hs_nmem
            have hzero : margins d v' k st₀ (tie k st₀.S (margins d v' k st₀)) = 0 := by
              simp [margins, hs_nmem]
            linarith
          rw [how _ hs_mem]
        · rfl
      · rfl
    rw [hst₁]
    set st₁ := if h : t < n then arrive d v' tie ⟨t, h⟩ st else st
    split_ifs with hc
    · have hk : ω ⟨t - d, hc.2⟩ = ω' ⟨t - d, hc.2⟩ := by
        apply hω_eq
        dsimp only
        omega
      unfold critical
      rw [hk]
    · rfl

private theorem arrive_finalized_inv {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (t : ℕ) (ht : t < n) (st : State n)
    (hlt : ∀ e ∈ st.finalized, (e.1 : ℕ) + d < t)
    (hmS : ∀ e ∈ st.finalized, e.1 ∉ st.S ∧ st.m e.1 = some e.2) :
    (arrive d v tie ⟨t, ht⟩ st).finalized = st.finalized ∧
    ∀ e ∈ st.finalized,
      e.1 ∉ (arrive d v tie ⟨t, ht⟩ st).S ∧
      (arrive d v tie ⟨t, ht⟩ st).m e.1 = some e.2 := by
  set j : Fin n := ⟨t, ht⟩
  set st₀ := addVertex j st
  have hst₀ : ∀ e ∈ st.finalized, e.1 ∉ st₀.S ∧ st₀.m e.1 = some e.2 := by
    intro e he
    have he_lt : (e.1 : ℕ) < t := by
      have := hlt e he
      omega
    have hne : e.1 ≠ j := by
      intro h_eq
      have : (e.1 : ℕ) = t := congrArg Fin.val h_eq
      omega
    refine ⟨?_, ?_⟩
    · simp only [st₀, addVertex, Finset.mem_insert, not_or]
      exact ⟨hne, (hmS e he).1⟩
    · simp only [st₀, addVertex, Function.update_of_ne hne]
      exact (hmS e he).2
  have hbid_fin : (arrive d v tie j st).finalized = st.finalized := by
    unfold arrive bid addVertex
    dsimp only
    split_ifs <;> rfl
  refine ⟨hbid_fin, fun e he => ?_⟩
  obtain ⟨hnS₀, hm₀⟩ := hst₀ e he
  refine ⟨?_, ?_⟩
  · simpa only [arrive, bid_S] using hnS₀
  · simp only [arrive]
    change (bid d v tie j st₀).m e.1 = some e.2
    unfold bid
    dsimp only
    split_ifs with hpos
    · have hs_mem : tie j st₀.S (margins d v j st₀) ∈ st₀.S := by
        by_contra hs_nmem
        have hzero : margins d v j st₀ (tie j st₀.S (margins d v j st₀)) = 0 := by
          simp [margins, hs_nmem]
        linarith
      have hne_s : e.1 ≠ tie j st₀.S (margins d v j st₀) := by
        intro h_eq
        rw [← h_eq] at hs_mem
        exact hnS₀ hs_mem
      simp only [Function.update_of_ne hne_s, hm₀]
    · exact hm₀

private theorem critical_finalized_inv {n : ℕ} (d : ℕ) (ω : Fin n → Bool)
    (t : ℕ) (hc : d ≤ t ∧ t - d < n) (st₁ : State n)
    (hnd : (st₁.finalized.map Prod.fst).Nodup)
    (hlt : ∀ e ∈ st₁.finalized, (e.1 : ℕ) + d < t)
    (hmS₁ : ∀ e ∈ st₁.finalized, e.1 ∉ st₁.S ∧ st₁.m e.1 = some e.2) :
    ((critical ω ⟨t - d, hc.2⟩ st₁).finalized.map Prod.fst).Nodup ∧
    (∀ e ∈ (critical ω ⟨t - d, hc.2⟩ st₁).finalized, (e.1 : ℕ) + d < t + 1) ∧
    (∀ e ∈ (critical ω ⟨t - d, hc.2⟩ st₁).finalized,
      e.1 ∉ (critical ω ⟨t - d, hc.2⟩ st₁).S ∧
      (critical ω ⟨t - d, hc.2⟩ st₁).m e.1 = some e.2) := by
  set k : Fin n := ⟨t - d, hc.2⟩
  unfold critical
  cases hmk : st₁.m k with
  | none =>
    exact ⟨hnd, fun e he => Nat.lt_succ_of_lt (hlt e he), hmS₁⟩
  | some l =>
    dsimp only
    split_ifs with hsel
    · dsimp only
      refine ⟨?_, ?_, ?_⟩
      · rw [List.map_append, List.map_singleton, List.nodup_append]
        refine ⟨hnd, List.nodup_singleton k, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy
        subst hy
        rw [List.mem_map] at hx
        obtain ⟨e, he, rfl⟩ := hx
        intro h_eq
        have h1 := hlt e he
        have h2 : (e.1 : ℕ) = t - d := congrArg Fin.val h_eq
        omega
      · intro e he
        rw [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact Nat.lt_succ_of_lt (hlt e he)
        · dsimp only [k]
          omega
      · intro e he
        rw [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · obtain ⟨hnS, hm⟩ := hmS₁ e he
          exact ⟨fun hmem => hnS (Finset.erase_subset k st₁.S hmem), hm⟩
        · exact ⟨by simp, hmk⟩
    · dsimp only
      refine ⟨hnd, fun e he => Nat.lt_succ_of_lt (hlt e he), fun e he => ?_⟩
      obtain ⟨hnS, hm⟩ := hmS₁ e he
      exact ⟨fun hmem => hnS (Finset.erase_subset k st₁.S hmem), hm⟩

private theorem finalized_inv {n : ℕ} (d : ℕ) (v : Sym2 (Fin n) → ℝ) (tie : TieRule n)
    (ω : Fin n → Bool) :
    ∀ t : ℕ,
      ((stateAfter d v tie ω t).finalized.map Prod.fst).Nodup ∧
      (∀ e ∈ (stateAfter d v tie ω t).finalized, (e.1 : ℕ) + d < t) ∧
      (∀ e ∈ (stateAfter d v tie ω t).finalized,
        e.1 ∉ (stateAfter d v tie ω t).S ∧ (stateAfter d v tie ω t).m e.1 = some e.2)
  | 0 => by simp [stateAfter, State.init]
  | t + 1 => by
    obtain ⟨hnd, hlt, hmS⟩ := finalized_inv d v tie ω t
    set st := stateAfter d v tie ω t
    simp only [stateAfter, period]
    have hst₁ :
        let st₁ := if h : t < n then arrive d v tie ⟨t, h⟩ st else st
        (st₁.finalized.map Prod.fst).Nodup ∧
        (∀ e ∈ st₁.finalized, (e.1 : ℕ) + d < t) ∧
        (∀ e ∈ st₁.finalized, e.1 ∉ st₁.S ∧ st₁.m e.1 = some e.2) := by
      dsimp only
      by_cases ht : t < n
      · rw [dif_pos ht]
        obtain ⟨hfin, hmS₁⟩ := arrive_finalized_inv d v tie t ht st hlt hmS
        rw [hfin]
        exact ⟨hnd, hlt, hmS₁⟩
      · rw [dif_neg ht]
        exact ⟨hnd, hlt, hmS⟩
    obtain ⟨hnd₁, hlt₁, hmS₁⟩ := hst₁
    by_cases hc : d ≤ t ∧ t - d < n
    · rw [dif_pos hc]
      exact critical_finalized_inv d ω t hc _ hnd₁ hlt₁ hmS₁
    · rw [dif_neg hc]
      exact ⟨hnd₁, fun e he => Nat.lt_succ_of_lt (hlt₁ e he), hmS₁⟩

private theorem nodup_flatMap_pairs {α : Type*} :
    ∀ (L : List (α × α)),
      (L.map Prod.fst).Nodup →
      (∀ e₁ ∈ L, ∀ e₂ ∈ L, e₁.1 ≠ e₂.2) →
      (∀ e₁ ∈ L, ∀ e₂ ∈ L, e₁.2 = e₂.2 → e₁.1 = e₂.1) →
      (L.flatMap fun e => [e.1, e.2]).Nodup
  | [], _, _, _ => by simp
  | (k, l) :: tl, hnd, hdisj, hinj => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk_nmem, hnd_tl⟩ := hnd
    have hhead : (k, l) ∈ (k, l) :: tl := by simp
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.mem_flatMap]
    refine ⟨?_, ?_, nodup_flatMap_pairs tl hnd_tl
      (fun e₁ h₁ e₂ h₂ => hdisj e₁ (by simp [h₁]) e₂ (by simp [h₂]))
      (fun e₁ h₁ e₂ h₂ => hinj e₁ (by simp [h₁]) e₂ (by simp [h₂]))⟩
    · rintro (hkl | ⟨e, he, he_mem⟩)
      · exact hdisj (k, l) hhead (k, l) hhead hkl
      · simp only [List.not_mem_nil, or_false] at he_mem
        rcases he_mem with hke | hke
        · apply hk_nmem
          rw [hke, List.mem_map]
          exact ⟨e, he, rfl⟩
        · exact hdisj (k, l) hhead e (by simp [he]) hke
    · rintro ⟨e, he, he_mem⟩
      simp only [List.not_mem_nil, or_false] at he_mem
      rcases he_mem with hle | hle
      · exact hdisj e (by simp [he]) (k, l) hhead hle.symm
      · have hke : k = e.1 := hinj (k, l) hhead e (by simp [he]) hle
        apply hk_nmem
        rw [hke, List.mem_map]
        exact ⟨e, he, rfl⟩

end WindowedMatching

open WindowedMatching

theorem solution {n : ℕ} (d : ℕ) (hd : 1 ≤ d) (v : Sym2 (Fin n) → ℝ) (hv : ∀ e, 0 ≤ v e)
    (tie : TieRule n) (hTie : IsArgmaxRule tie) :
    (∀ ω, ∀ e ∈ (finalState d v tie ω).finalized, (windowGraph n d).Adj e.1 e.2) ∧
    (∀ ω, ((finalState d v tie ω).finalized.flatMap fun e => [e.1, e.2]).Nodup) ∧
    (1 / 4 : ℝ) * offlineOpt d v ≤ expectedReward d v tie ∧
    (∀ t ≤ n + d, ∀ v' : Sym2 (Fin n) → ℝ, (∀ e, 0 ≤ v' e) →
      (∀ i j : Fin n, (i : ℕ) < t → (j : ℕ) < t → v s(i, j) = v' s(i, j)) →
      ∀ ω ω' : Fin n → Bool, (∀ k : Fin n, (k : ℕ) + d < t → ω k = ω' k) →
        stateAfter d v tie ω t = stateAfter d v' tie ω' t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω e he
    have hm : (finalState d v tie ω).m e.1 = some e.2 :=
      ((finalized_inv d v tie ω (n + d)).2.2 e he).2
    exact ((disjoint_paths d hd v hv tie hTie ω).1 e.1 e.2 hm).2
  · intro ω
    obtain ⟨hnd, _, hmS⟩ := finalized_inv d v tie ω (n + d)
    have hdp := disjoint_paths d hd v hv tie hTie ω
    have hstat : ∀ e ∈ (finalState d v tie ω).finalized,
        (finalState d v tie ω).status e.1 = .seller ∧
        (finalState d v tie ω).status e.2 = .buyer := by
      intro e he
      have hm := (hmS e he).2
      rcases status_alternates d hd v hv tie hTie ω e.1 e.2 hm with
        ⟨hs₁, hs₂, _⟩ | ⟨_, _, hnmem⟩
      · exact ⟨hs₁, hs₂⟩
      · exact absurd he hnmem
    refine nodup_flatMap_pairs (finalState d v tie ω).finalized hnd ?_ ?_
    · intro e₁ h₁ e₂ h₂ h_eq
      have hs₁ := (hstat e₁ h₁).1
      have hs₂ := (hstat e₂ h₂).2
      rw [h_eq, hs₂] at hs₁
      cases hs₁
    · intro e₁ h₁ e₂ h₂ h_eq
      have hm₁ : (finalState d v tie ω).m e₁.1 = some e₁.2 := (hmS e₁ h₁).2
      have hm₂ : (finalState d v tie ω).m e₂.1 = some e₁.2 := by
        rw [h_eq]
        exact (hmS e₂ h₂).2
      exact hdp.2 e₁.1 e₂.1 e₁.2 hm₁ hm₂
  · let ω₀ : Fin n → Bool := fun _ => false
    have hexp := expected_reward_eq d hd v hv tie hTie ω₀
    have hsum := sum_price_eq_sum_margin d hd v hv tie hTie ω₀
    have hdual := dual_feasible d hd v hv tie hTie ω₀
    have hwd : offlineOpt d v ≤
        ∑ k : Fin n, ((finalState d v tie ω₀).p k + (finalState d v tie ω₀).q k) :=
      weak_duality (windowGraph n d) (fun e => v e.1)
        (fun k => (finalState d v tie ω₀).p k + (finalState d v tie ω₀).q k)
        hdual.1 (fun a b hab => hdual.2 a b hab)
    rw [Finset.sum_add_distrib] at hwd
    linarith
  · intro t _ v' _ hv_eq ω ω' hω_eq
    exact online_stateAfter d v v' tie ω ω' t hv_eq hω_eq
