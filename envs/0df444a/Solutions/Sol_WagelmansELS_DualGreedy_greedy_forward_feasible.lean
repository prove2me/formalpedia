-- Prove2me | solution 1 for WagelmansELS.DualGreedy.greedy_forward_feasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:17:57.552009+00:00
-- url     : https://prove2.me/submissions/c459d089-4a87-4a24-a343-85e94209afda

import Mathlib
import Definitions.Def_WagelmansELS_DualGreedy_Greedy



namespace WagelmansELS.DualGreedy

noncomputable def Rf (P : Instance) (j : ℕ) : ℕ → ℝ :=
  (Nat.rec (motive := fun _ => ℕ → ℝ) (fun _ => (0 : ℝ)) (fun k hist =>
    fun t => if t = k + 1 then
      if k + 1 ≤ P.n then
        if P.d (k + 1) = 0 then hist k
        else (Finset.Icc 1 (k + 1)).inf' (by
          refine ⟨1, Finset.mem_Icc.mpr ?_⟩
          omega) (fun i => P.f i + P.c i * demand P i (k + 1) + hist (i - 1))
      else 0
    else hist t) j)

lemma F_eq_Rf (P : Instance) (j : ℕ) : F P j = Rf P j j := rfl

lemma Rf_succ_ne (P : Instance) (k t : ℕ) (h : t ≠ k + 1) : Rf P (k+1) t = Rf P k t := by
  show (if t = k + 1 then _ else _) = _
  rw [if_neg h]
  rfl

lemma Rf_hist (P : Instance) : ∀ k t, t ≤ k → Rf P k t = F P t := by
  intro k
  induction k with
  | zero =>
    intro t ht
    have : t = 0 := by omega
    subst this; rfl
  | succ k ih =>
    intro t ht
    rcases Nat.lt_or_ge t (k+1) with h | h
    · rw [Rf_succ_ne P k t (by omega), ih t (by omega)]
    · have : t = k + 1 := by omega
      subst this; rfl

lemma F_zero (P : Instance) : F P 0 = 0 := rfl

lemma F_succ_zero (P : Instance) (j : ℕ) (hj : j + 1 ≤ P.n) (h : P.d (j+1) = 0) :
    F P (j+1) = F P j := by
  have h1 : F P (j+1) = Rf P (j+1) (j+1) := rfl
  rw [h1]
  show (if j + 1 = j + 1 then _ else _) = _
  rw [if_pos rfl, if_pos hj, if_pos h]
  exact Rf_hist P j j le_rfl

lemma F_succ_pos (P : Instance) (j : ℕ) (hj : j + 1 ≤ P.n) (h : P.d (j+1) ≠ 0) :
    ∃ hne, F P (j+1) = (Finset.Icc 1 (j + 1)).inf' hne
      (fun i => P.f i + P.c i * demand P i (j + 1) + F P (i - 1)) := by
  refine ⟨⟨1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩, ?_⟩
  have h1 : F P (j+1) = Rf P (j+1) (j+1) := rfl
  rw [h1]
  show (if j + 1 = j + 1 then _ else _) = _
  rw [if_pos rfl, if_pos hj, if_neg h]
  apply Finset.inf'_congr _ rfl
  intro i hi
  have := (Finset.mem_Icc.mp hi)
  have h2 := Rf_hist P j (i-1) (by omega)
  show P.f i + P.c i * demand P i (j + 1) + Rf P j (i - 1) = _
  rw [h2]

lemma F_le_block (P : Instance) (j i : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) (hdj : 0 < P.d j)
    (hi1 : 1 ≤ i) (hij : i ≤ j) :
    F P j ≤ P.f i + P.c i * demand P i j + F P (i - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hne, h⟩ := F_succ_pos P m hjn hdj.ne'
  rw [h]
  exact Finset.inf'_le (fun i => P.f i + P.c i * demand P i (m + 1) + F P (i - 1))
    (Finset.mem_Icc.mpr ⟨hi1, hij⟩)

lemma F_exists_block (P : Instance) (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) (hdj : 0 < P.d j) :
    ∃ i, 1 ≤ i ∧ i ≤ j ∧ F P j = P.f i + P.c i * demand P i j + F P (i - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨hne, h⟩ := F_succ_pos P m hjn hdj.ne'
  obtain ⟨i, hi, hi2⟩ := Finset.exists_mem_eq_inf' hne
    (fun i => P.f i + P.c i * demand P i (m + 1) + F P (i - 1))
  have := Finset.mem_Icc.mp hi
  exact ⟨i, this.1, this.2, by rw [h, hi2]⟩

lemma objective_succ (P : Instance) (v : ℕ → ℝ) (j : ℕ) :
    objective P v (j+1) = objective P v j + P.d (j+1) * v (j+1) := by
  unfold objective
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma objective_split (P : Instance) (v : ℕ → ℝ) (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j + 1) :
    objective P v j = objective P v (i - 1) + ∑ t ∈ Finset.Icc i j, P.d t * v t := by
  unfold objective
  have : Finset.Icc 1 j = Finset.Icc 1 (i-1) ∪ Finset.Icc i j := by
    ext x; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  rw [this, Finset.sum_union]
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_Icc] at hx hx'
  omega

lemma demand_nonneg (P : Instance) (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t) (i j : ℕ)
    (hi : 1 ≤ i) (hj : j ≤ P.n) : 0 ≤ demand P i j := by
  unfold demand
  apply Finset.sum_nonneg
  intro t ht
  have := Finset.mem_Icc.mp ht
  exact hd t (by omega) (by omega)

lemma weak_duality_core (P : Instance) (u : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hu : IsFeasible P u)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) :
    objective P u j ≤ F P j := by
  have main : ∀ j, j ≤ P.n → objective P u j ≤ F P j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hjn
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [objective, F_zero]
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      by_cases h0 : P.d (m+1) = 0
      · rw [objective_succ, h0, F_succ_zero P m hjn h0]
        simpa using ih m (by omega) (by omega)
      · have hpos : 0 < P.d (m+1) := lt_of_le_of_ne (hd _ (by omega) hjn) (Ne.symm h0)
        obtain ⟨i, hi1, hij, hFi⟩ := F_exists_block P (m+1) (by omega) hjn hpos
        rw [hFi]
        have ih' := ih (i-1) (by omega) (by omega)
        rw [objective_split P u i (m+1) hi1 (by omega)]
        have hin : i ≤ P.n := by omega
        have hfeas := hu i hi1 hin
        have h1 : ∑ t ∈ Finset.Icc i (m+1), P.d t * u t ≤
            P.c i * demand P i (m+1) + P.f i := by
          have h2 : ∑ t ∈ Finset.Icc i (m+1), P.d t * u t ≤
              ∑ t ∈ Finset.Icc i (m+1), (P.d t * P.c i + P.d t * max 0 (u t - P.c i)) := by
            apply Finset.sum_le_sum
            intro t ht
            have : u t ≤ P.c i + max 0 (u t - P.c i) := by
              have := le_max_right 0 (u t - P.c i); linarith
            have htd := hd t (by have := Finset.mem_Icc.mp ht; omega)
              (by have := Finset.mem_Icc.mp ht; omega)
            nlinarith
          have h3 : ∑ t ∈ Finset.Icc i (m+1), (P.d t * P.c i + P.d t * max 0 (u t - P.c i))
              = P.c i * demand P i (m+1) + constraintUse P u i (m+1) := by
            rw [Finset.sum_add_distrib]
            unfold demand constraintUse
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl; intro t _; ring
          have h4 : constraintUse P u i (m+1) ≤ constraintUse P u i P.n := by
            unfold constraintUse
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro t ht; simp only [Finset.mem_Icc] at ht ⊢; omega
            · intro t ht _
              have := Finset.mem_Icc.mp ht
              exact mul_nonneg (hd t (by omega) this.2) (le_max_left _ _)
          linarith
        linarith
  exact main j hjn

lemma Ico_eq (a b : ℕ) : Finset.Ico a (b+1) = Finset.Icc a b := by
  ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega

lemma pastUse_succ (P : Instance) (v : ℕ → ℝ) (i j : ℕ) (hij : i ≤ j) :
    pastUse P v i (j+1) = pastUse P v i j + P.d j * max 0 (v j - P.c i) := by
  unfold pastUse
  rw [Finset.sum_Ico_succ_top hij]

lemma bound_le (P : Instance) (v : ℕ → ℝ) (hv : IsGreedyForward P v) (i j : ℕ)
    (hi1 : 1 ≤ i) (hij : i ≤ j) (hjn : j ≤ P.n) (hdj : 0 < P.d j) :
    v j ≤ greedyBound P v i j := by
  rw [hv j (by omega) hjn hdj]
  exact Finset.inf'_le (fun i => greedyBound P v i j) (Finset.mem_Icc.mpr ⟨hi1, hij⟩)

lemma bound_mul (P : Instance) (v : ℕ → ℝ) (i j : ℕ) (hdj : 0 < P.d j)
    (h : v j ≤ greedyBound P v i j) :
    P.d j * (v j - P.c i) ≤ P.f i - pastUse P v i j := by
  unfold greedyBound at h
  have h1 : v j - P.c i ≤ (P.f i - pastUse P v i j) / P.d j := by linarith
  rw [le_div_iff₀ hdj] at h1
  linarith

lemma pastUse_le (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v) (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ P.n) :
    ∀ j, i ≤ j → j ≤ P.n + 1 → pastUse P v i j ≤ P.f i := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; simp [pastUse]; exact hf i hi1 hin
  | succ j hij ih =>
    intro hj
    have ih' := ih (by omega)
    rw [pastUse_succ P v i j hij]
    rcases (hd j (by omega) (by omega)).eq_or_lt with h0 | hpos
    · rw [← h0]; simpa using ih'
    · have hb := bound_mul P v i j hpos (bound_le P v hv i j hi1 hij (by omega) hpos)
      rcases le_total (v j - P.c i) 0 with hneg | hnn
      · rw [max_eq_left hneg]; simpa using ih'
      · rw [max_eq_right hnn]; linarith

lemma greedy_forward_feasible_core (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v) : IsFeasible P v := by
  intro i hi1 hin
  have := pastUse_le P v hd hf hv i hi1 hin (P.n + 1) (by omega) le_rfl
  have e : constraintUse P v i P.n = pastUse P v i (P.n + 1) := by
    unfold constraintUse pastUse
    rw [Ico_eq]
  rw [e]; exact this

lemma greedy_forward_monotone_core (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v)
    (t j : ℕ) (ht : 1 ≤ t) (htj : t < j) (hjn : j ≤ P.n)
    (hdt : 0 < P.d t) (hdj : 0 < P.d j) : v j ≤ v t := by
  have htn : t ≤ P.n := by omega
  have hvt := hv t ht htn hdt
  obtain ⟨i, hi, hi2⟩ := Finset.exists_mem_eq_inf' (⟨1, Finset.mem_Icc.mpr ⟨le_refl _, ht⟩⟩ : (Finset.Icc 1 t).Nonempty)
    (fun i => greedyBound P v i t)
  have hi' := Finset.mem_Icc.mp hi
  have hvt' : v t = greedyBound P v i t := by rw [hvt]; exact hi2
  have hpl := pastUse_le P v hd hf hv i hi'.1 (by omega) t hi'.2 (by omega)
  have hbt := bound_mul P v i t hdt (le_of_eq hvt')
  have hge : P.c i ≤ v t := by
    have : 0 ≤ P.d t * (v t - P.c i) := by
      have h1 := hvt'
      unfold greedyBound at h1
      have : v t - P.c i = (P.f i - pastUse P v i t) / P.d t := by linarith
      rw [this]
      rw [mul_div_cancel₀ _ hdt.ne']
      linarith
    have := nonneg_of_mul_nonneg_right this hdt
    linarith
  have heq : P.d t * (v t - P.c i) = P.f i - pastUse P v i t := by
    have h1 := hvt'
    unfold greedyBound at h1
    have : v t - P.c i = (P.f i - pastUse P v i t) / P.d t := by linarith
    rw [this, mul_div_cancel₀ _ hdt.ne']
  have hsplit : pastUse P v i j = pastUse P v i (t+1) + ∑ s ∈ Finset.Ico (t+1) j, P.d s * max 0 (v s - P.c i) := by
    unfold pastUse
    rw [Finset.sum_Ico_consecutive _ (by omega) (by omega)]
  have hrest : 0 ≤ ∑ s ∈ Finset.Ico (t+1) j, P.d s * max 0 (v s - P.c i) := by
    apply Finset.sum_nonneg
    intro s hs
    have := Finset.mem_Ico.mp hs
    exact mul_nonneg (hd s (by omega) (by omega)) (le_max_left _ _)
  rw [pastUse_succ P v i t hi'.2, max_eq_right (by linarith)] at hsplit
  have hbj := bound_le P v hv i j hi'.1 (by omega) hjn hdj
  have hbj2 := bound_mul P v i j hdj hbj
  have hfin : P.d j * (v j - P.c i) ≤ 0 := by linarith
  have : v j - P.c i ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos hdj hcon
    linarith
  linarith

lemma pastUse_ge (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v) (k j : ℕ) (hk1 : 1 ≤ k) (hkj : k ≤ j) (hjn : j ≤ P.n)
    (hdj : 0 < P.d j) (hk : v j = greedyBound P v k j) : P.c k ≤ v j := by
  have h1 := pastUse_le P v hd hf hv k hk1 (by omega) j hkj (by omega)
  unfold greedyBound at hk
  have : 0 ≤ (P.f k - pastUse P v k j) / P.d j := div_nonneg (by linarith) hdj.le
  linarith

lemma equation_2_core (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v)
    (j k : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ P.n) (hdj : 0 < P.d j)
    (hk1 : 1 ≤ k) (hkj : k ≤ j)
    (hk : v j = greedyBound P v k j)
    (hind : objective P v (k - 1) = F P (k - 1)) :
    objective P v j = P.f k + P.c k * demand P k j + F P (k - 1) := by
  have hvj := pastUse_ge P v hd hf hv k j hk1 hkj hjn hdj hk
  rw [objective_split P v k j hk1 (by omega), hind]
  have h1 : ∑ t ∈ Finset.Icc k j, P.d t * v t =
      P.c k * demand P k j + constraintUse P v k j := by
    unfold demand constraintUse
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have htm := Finset.mem_Icc.mp ht
    rcases (hd t (by omega) (by omega)).eq_or_lt with h0 | hpos
    · rw [← h0]; ring
    · have hge : P.c k ≤ v t := by
        rcases Nat.lt_or_ge t j with hlt | hge
        · have := greedy_forward_monotone_core P v hd hf hv t j (by omega) hlt hjn hpos hdj
          linarith
        · have : t = j := by omega
          subst this; exact hvj
      rw [max_eq_right (by linarith)]; ring
  have h2 : constraintUse P v k j = pastUse P v k (j+1) := by
    unfold constraintUse pastUse
    rw [Ico_eq]
  have h3 := pastUse_succ P v k j hkj
  have h4 : P.d j * (v j - P.c k) = P.f k - pastUse P v k j := by
    have h5 := hk
    unfold greedyBound at h5
    have : v j - P.c k = (P.f k - pastUse P v k j) / P.d j := by linarith
    rw [this, mul_div_cancel₀ _ hdj.ne']
  rw [max_eq_right (by linarith)] at h3
  rw [h1, h2, h3]
  linarith

lemma greedy_forward_optimal_core (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v) :
    IsFeasible P v ∧
      (∀ j, 1 ≤ j → j ≤ P.n → objective P v j = F P j) ∧
      (∀ u, IsFeasible P u → objective P u P.n ≤ objective P v P.n) := by
  have hfeas := greedy_forward_feasible_core P v hd hf hv
  have main : ∀ j, j ≤ P.n → objective P v j = F P j := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hjn
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [objective, F_zero]
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      by_cases h0 : P.d (m+1) = 0
      · rw [objective_succ, h0, F_succ_zero P m hjn h0]
        simpa using ih m (by omega) (by omega)
      · have hpos : 0 < P.d (m+1) := lt_of_le_of_ne (hd _ (by omega) hjn) (Ne.symm h0)
        have hle := weak_duality_core P v hd hf hfeas (m+1) (by omega) hjn
        obtain ⟨k, hk, hk2⟩ := Finset.exists_mem_eq_inf'
          (⟨1, Finset.mem_Icc.mpr ⟨le_refl _, by omega⟩⟩ : (Finset.Icc 1 (m+1)).Nonempty)
          (fun i => greedyBound P v i (m+1))
        have hk' := Finset.mem_Icc.mp hk
        have hvk : v (m+1) = greedyBound P v k (m+1) := by
          rw [hv (m+1) (by omega) hjn hpos]; exact hk2
        have hind := ih (k-1) (by omega) (by omega)
        have e2 := equation_2_core P v hd hf hv (m+1) k (by omega) hjn hpos hk'.1 hk'.2 hvk hind
        have hFle := F_le_block P (m+1) k (by omega) hjn hpos hk'.1 hk'.2
        linarith
  refine ⟨hfeas, fun j _ hjn => main j hjn, ?_⟩
  intro u hu
  rcases Nat.eq_zero_or_pos P.n with h | h
  · simp [objective, h]
  · have := weak_duality_core P u hd hf hu P.n h le_rfl
    rw [main P.n le_rfl]; exact this

end WagelmansELS.DualGreedy

open WagelmansELS.DualGreedy


theorem solution (P : Instance) (v : ℕ → ℝ)
    (hd : ∀ t, 1 ≤ t → t ≤ P.n → 0 ≤ P.d t)
    (hf : ∀ i, 1 ≤ i → i ≤ P.n → 0 ≤ P.f i)
    (hv : IsGreedyForward P v) : IsFeasible P v := by
  exact greedy_forward_feasible_core P v hd hf hv
