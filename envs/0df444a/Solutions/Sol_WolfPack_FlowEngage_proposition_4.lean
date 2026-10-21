-- Prove2me | solution 1 for WolfPack.FlowEngage.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T06:16:34.714476+00:00
-- url     : https://prove2.me/submissions/9e81b293-be76-4ffd-9e0c-c1820652867c

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_WolfPack_FlowEngage_Model

namespace WPAux
open Finset WolfPack.FlowEngage

variable {n : ℕ}

noncomputable def oth (σ : Fin n → Bool → ℝ) (i : Fin n) (t : Fin n → Bool) : ℝ :=
  ∏ j ∈ univ.erase i, σ j (t j)

lemma profileProb_eq (σ : Fin n → Bool → ℝ) (i : Fin n) (t : Fin n → Bool) :
    AGT.profileProb σ t = σ i (t i) * oth σ i t := by
  unfold AGT.profileProb oth
  rw [Finset.mul_prod_erase _ (fun j => σ j (t j)) (mem_univ i)]

lemma oth_update (σ : Fin n → Bool → ℝ) (i : Fin n) (τ : Bool → ℝ) (t : Fin n → Bool) :
    oth (Function.update σ i τ) i t = oth σ i t := by
  unfold oth
  refine prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (ne_of_mem_erase hj)]

lemma oth_flip (σ : Fin n → Bool → ℝ) (i : Fin n) (t : Fin n → Bool) (a : Bool) :
    oth σ i (Function.update t i a) = oth σ i t := by
  unfold oth
  refine prod_congr rfl (fun j hj => ?_)
  rw [Function.update_of_ne (ne_of_mem_erase hj)]

lemma oth_nonneg (σ : Fin n → Bool → ℝ) (hσ : AGT.IsMixedProfile σ) (i : Fin n)
    (t : Fin n → Bool) : 0 ≤ oth σ i t :=
  prod_nonneg (fun j _ => (hσ j).1 _)

lemma sum_profileProb (σ : Fin n → Bool → ℝ) (hσ : AGT.IsMixedProfile σ) :
    ∑ t : Fin n → Bool, AGT.profileProb σ t = 1 := by
  unfold AGT.profileProb
  rw [← Fintype.prod_sum (fun j a => σ j a)]
  exact prod_eq_one (fun j _ => (hσ j).2)

lemma profileProb_nonneg (σ : Fin n → Bool → ℝ) (hσ : AGT.IsMixedProfile σ)
    (t : Fin n → Bool) : 0 ≤ AGT.profileProb σ t :=
  prod_nonneg (fun j _ => (hσ j).1 _)

noncomputable def Acoef (u : Fin n → (Fin n → Bool) → ℝ) (σ : Fin n → Bool → ℝ) (i : Fin n)
    (a : Bool) : ℝ :=
  ∑ t : Fin n → Bool, if t i = a then oth σ i t * u i t else 0

lemma expected_update (u : Fin n → (Fin n → Bool) → ℝ) (σ : Fin n → Bool → ℝ) (i : Fin n)
    (τ : Bool → ℝ) :
    AGT.expectedPayoff u (Function.update σ i τ) i =
      τ true * Acoef u σ i true + τ false * Acoef u σ i false := by
  unfold AGT.expectedPayoff Acoef
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl (fun t _ => ?_)
  rw [profileProb_eq _ i, Function.update_self, oth_update]
  cases t i <;> simp <;> ring

lemma expected_self (u : Fin n → (Fin n → Bool) → ℝ) (σ : Fin n → Bool → ℝ) (i : Fin n) :
    AGT.expectedPayoff u σ i =
      σ i true * Acoef u σ i true + σ i false * Acoef u σ i false := by
  rw [← expected_update]
  rw [Function.update_eq_self]

def dirac (a : Bool) : Bool → ℝ := fun b => if b = a then 1 else 0

lemma dirac_lottery (a : Bool) : AGT.IsLottery (dirac a) := by
  refine ⟨fun b => by unfold dirac; split_ifs <;> norm_num, ?_⟩
  cases a <;> simp [dirac]

lemma lottery_sum (τ : Bool → ℝ) (h : AGT.IsLottery τ) : τ true + τ false = 1 := by
  have := h.2
  simpa [Fintype.sum_bool] using this

/-- A strictly dominated action (engage) gets zero weight in a mixed Nash equilibrium. -/
lemma dominated_zero (u : Fin n → (Fin n → Bool) → ℝ) (σ : Fin n → Bool → ℝ)
    (hN : AGT.IsMixedNash u σ) (i : Fin n) (ε : ℝ) (hε : 0 < ε)
    (hdom : ∀ t : Fin n → Bool, t i = false → u i (Function.update t i true) + ε ≤ u i t) :
    σ i true = 0 := by
  have hσ := hN.1
  have hdev := hN.2 i (dirac false) (dirac_lottery false)
  rw [expected_update, expected_self] at hdev
  simp only [dirac] at hdev
  norm_num at hdev
  -- flip the A-coefficient
  have hflip : Acoef u σ i true =
      ∑ t : Fin n → Bool, if t i = false then oth σ i t * u i (Function.update t i true) else 0 := by
    unfold Acoef
    let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
      { toFun := fun t => Function.update t i (!t i)
        invFun := fun t => Function.update t i (!t i)
        left_inv := fun t => by
          funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj]
        right_inv := fun t => by
          funext j
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne hj] }
    rw [← Equiv.sum_comp e]
    refine sum_congr rfl (fun t _ => ?_)
    simp only [e, Equiv.coe_fn_mk, Function.update_self, oth_flip]
    cases h : t i <;> simp [h]
  have hW : (∑ t : Fin n → Bool, if t i = false then oth σ i t else 0) = 1 := by
    have h1 := sum_profileProb (Function.update σ i (dirac false))
      (fun j => by
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact dirac_lottery false
        · rw [Function.update_of_ne hj]; exact hσ j)
    rw [← h1]
    refine sum_congr rfl (fun t _ => ?_)
    rw [profileProb_eq _ i, Function.update_self, oth_update]
    cases t i <;> simp [dirac]
  have hBA : Acoef u σ i true + ε ≤ Acoef u σ i false := by
    rw [hflip]
    unfold Acoef
    have : (∑ t : Fin n → Bool, if t i = false then oth σ i t * u i (Function.update t i true) else 0)
        + ε * (∑ t : Fin n → Bool, if t i = false then oth σ i t else 0)
        = ∑ t : Fin n → Bool, if t i = false then
            oth σ i t * (u i (Function.update t i true) + ε) else 0 := by
      rw [mul_sum, ← sum_add_distrib]
      refine sum_congr rfl (fun t _ => ?_)
      split_ifs <;> ring
    rw [hW, mul_one] at this
    rw [this]
    refine sum_le_sum (fun t _ => ?_)
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left (hdom t h) (oth_nonneg σ hσ i t)
    · exact le_refl _
  have hs := lottery_sum (σ i) (hσ i)
  have h0 := (hσ i).1 true
  have hf : σ i false = 1 - σ i true := by linarith
  rw [hf] at hdev
  by_contra hne
  have hpos : 0 < σ i true := lt_of_le_of_ne h0 (Ne.symm hne)
  have := mul_le_mul_of_nonneg_left hBA h0
  nlinarith [mul_pos hpos hε]

lemma profileProb_pure (s t : Fin n → Bool) :
    AGT.profileProb (pureLottery s) t = if t = s then 1 else 0 := by
  unfold AGT.profileProb pureLottery
  rw [Fintype.prod_boole]
  congr 1
  simp [funext_iff]

lemma expected_pure (u : Fin n → (Fin n → Bool) → ℝ) (s : Fin n → Bool) (i : Fin n) :
    AGT.expectedPayoff u (pureLottery s) i = u i s := by
  unfold AGT.expectedPayoff
  simp [profileProb_pure]

lemma update_pure (s : Fin n → Bool) (i : Fin n) (a : Bool) :
    Function.update (pureLottery s) i (dirac a) = pureLottery (Function.update s i a) := by
  funext j b
  by_cases hj : j = i
  · subst hj; simp [pureLottery, dirac]
  · simp [pureLottery, Function.update_of_ne hj]

lemma pure_isMixed (s : Fin n → Bool) : AGT.IsMixedProfile (pureLottery s) := by
  intro i
  exact dirac_lottery (s i)

lemma pureNash_mixed (u : Fin n → (Fin n → Bool) → ℝ) (s : Fin n → Bool)
    (h : AGT.IsPureNash u s) : AGT.IsMixedNash u (pureLottery s) := by
  refine ⟨pure_isMixed s, fun i τ hτ => ?_⟩
  have hA : ∀ a, Acoef u (pureLottery s) i a = u i (Function.update s i a) := by
    intro a
    have := expected_update u (pureLottery s) i (dirac a)
    rw [update_pure, expected_pure] at this
    cases a <;> simp [dirac] at this <;> linarith
  rw [expected_update, expected_pure, hA, hA]
  have h1 := h i true
  have h2 := h i false
  have hs := lottery_sum τ hτ
  have ht := hτ.1 true
  have hf := hτ.1 false
  have := mul_le_mul_of_nonneg_left h1 ht
  have := mul_le_mul_of_nonneg_left h2 hf
  have : τ true * u i s + τ false * u i s = u i s := by rw [← add_mul, hs, one_mul]
  linarith

end WPAux


namespace WPAux
open Finset WolfPack.FlowEngage

lemma numEngaged_le {n : ℕ} (s : Fin n → Bool) : numEngaged s ≤ n := by
  unfold numEngaged
  exact (card_filter_le _ _).trans (by simp)

lemma numEngaged_update {n : ℕ} (t : Fin n → Bool) (i : Fin n) (h : t i = false) :
    numEngaged (Function.update t i true) = numEngaged t + 1 := by
  unfold numEngaged
  have : (univ.filter (fun j => Function.update t i true j = true)) =
      insert i (univ.filter (fun j => t j = true)) := by
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [Function.update_of_ne hj, hj]
  rw [this, card_insert_of_notMem (by simp [h])]

lemma numEngaged_lt {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    numEngaged (fun j : Fin n => decide (j.val < k)) = k := by
  unfold numEngaged
  have := @Fin.card_filter_val_lt n k
  simp only [decide_eq_true_eq]
  rw [this]; omega

lemma numEngaged_false {n : ℕ} : numEngaged (fun _ : Fin n => false) = 0 := by
  simp [numEngaged]

lemma game_dominated (p : Params) (eta : ℝ) (g : GameKind) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ m : ℕ, m + 1 ≤ p.N → payoff p eta g true (m + 1) + ε ≤ payoff p eta g false m) :
    ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta g) τ → ∀ i, τ i true = 0 := by
  intro τ hτ i
  refine dominated_zero _ τ hτ i ε hε (fun t ht => ?_)
  unfold subgamePayoff
  rw [Function.update_self, numEngaged_update t i ht, ht]
  apply h
  rw [← numEngaged_update t i ht]
  exact numEngaged_le _

lemma success_zero (p : Params) (eta : ℝ) (heta : 0 < eta) (τ : Fin p.N → Bool → ℝ)
    (h : ∀ i, τ i true = 0) : successProb p eta τ = 0 := by
  unfold successProb
  refine sum_eq_zero (fun s _ => ?_)
  by_cases hs : ∃ i, s i = true
  · obtain ⟨i, hi⟩ := hs
    have : AGT.profileProb τ s = 0 := by
      unfold AGT.profileProb
      exact prod_eq_zero (mem_univ i) (by rw [hi]; exact h i)
    rw [this, zero_mul]
  · push_neg at hs
    have : s = fun _ => false := funext (fun j => by simpa using hs j)
    subst this
    rw [numEngaged_false]
    simp [not_le.mpr heta]

lemma success_le_one (p : Params) (eta : ℝ) (τ : Fin p.N → Bool → ℝ)
    (hτ : AGT.IsMixedProfile τ) : successProb p eta τ ≤ 1 := by
  unfold successProb
  calc _ ≤ ∑ s : Fin p.N → Bool, AGT.profileProb τ s := by
        refine sum_le_sum (fun s _ => ?_)
        have := profileProb_nonneg τ hτ s
        split_ifs <;> nlinarith
    _ = 1 := sum_profileProb τ hτ

lemma success_pure (p : Params) (eta : ℝ) (s : Fin p.N → Bool) :
    successProb p eta (pureLottery s) = if eta ≤ (numEngaged s : ℝ) * p.b then 1 else 0 := by
  unfold successProb
  simp only [profileProb_pure]
  rw [Finset.sum_eq_single s]
  · simp
  · intro t _ ht; simp [ht]
  · simp

lemma pure_crit (p : Params) (eta : ℝ) (g : GameKind) (s : Fin p.N → Bool) (k : ℕ)
    (hk : numEngaged s = k)
    (h1 : 1 ≤ k → payoff p eta g false (k - 1) ≤ payoff p eta g true k)
    (h2 : k < p.N → payoff p eta g true (k + 1) ≤ payoff p eta g false k) :
    AGT.IsPureNash (subgamePayoff p eta g) s := by
  intro i a
  unfold subgamePayoff
  rw [Function.update_self]
  by_cases ha : a = s i
  · subst ha; rw [Function.update_eq_self]
  · cases hsi : s i
    · have ha' : a = true := by cases a <;> simp_all
      subst ha'
      rw [numEngaged_update s i hsi, hk]
      apply h2
      have := numEngaged_le (Function.update s i true)
      rw [numEngaged_update s i hsi, hk] at this
      omega
    · have ha' : a = false := by cases a <;> simp_all
      subst ha'
      set t := Function.update s i false with ht
      have hti : t i = false := by simp [t]
      have hst : Function.update t i true = s := by
        rw [ht, Function.update_idem, ← hsi, Function.update_eq_self]
      have hc := numEngaged_update t i hti
      rw [hst, hk] at hc
      rw [hk, show numEngaged t = k - 1 by omega]
      exact h1 (by omega)

lemma alpha_le_U (p : Params) (hp : p.Standing) : alpha p ≤ p.U := by
  unfold alpha
  have h1 := hp.blocks_le_one
  have h2 := hp.one_lt_U
  have h3 : (0 : ℝ) ≤ p.M := by positivity
  have := hp.b_pos
  nlinarith

lemma keta_spec (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p))
    (k : ℕ) : eta ≤ (k : ℝ) * p.b ↔ Keta p eta ≤ k := by
  have hne : p.N ∈ {x : ℕ | eta ≤ (x : ℝ) * p.b} := heta.2
  constructor
  · intro h; exact Nat.sInf_le h
  · intro h
    have hmem : Keta p eta ∈ {x : ℕ | eta ≤ (x : ℝ) * p.b} := Nat.sInf_mem ⟨_, hne⟩
    have : ((Keta p eta : ℕ) : ℝ) ≤ k := by exact_mod_cast h
    have := hp.b_pos
    calc eta ≤ (Keta p eta : ℝ) * p.b := hmem
      _ ≤ k * p.b := by nlinarith

lemma keta_pos (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p)) :
    2 ≤ Keta p eta := by
  by_contra h
  push_neg at h
  have := (keta_spec p hp eta heta (Keta p eta)).2 le_rfl
  have hb := hp.b_pos
  have : ((Keta p eta : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (by omega : Keta p eta ≤ 1)
  have := heta.1
  nlinarith

lemma keta_le_N (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p)) :
    Keta p eta ≤ p.N := (keta_spec p hp eta heta p.N).1 heta.2

lemma chat_eq (p : Params) (x : ℕ) (hx : 1 ≤ x) :
    chat p x = p.w * (1 - p.phi) * p.b * p.Ph * (((p.M : ℝ) + p.N) / x) := by
  unfold chat
  have : (x : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma chat_anti (p : Params) (hp : p.Standing) (x y : ℕ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    chat p y ≤ chat p x := by
  rw [chat_eq p x hx, chat_eq p y (hx.trans hxy)]
  have hc : 0 ≤ p.w * (1 - p.phi) * p.b * p.Ph := by
    have := hp.w_pos; have := hp.phi_lt_one; have := hp.b_pos; have := hp.Ph_pos
    have : 0 < 1 - p.phi := by linarith
    positivity
  apply mul_le_mul_of_nonneg_left _ hc
  apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hx)
  exact_mod_cast hxy

lemma chat_nonneg (p : Params) (hp : p.Standing) (x : ℕ) (hx : 1 ≤ x) : 0 ≤ chat p x := by
  rw [chat_eq p x hx]
  have := hp.w_pos; have := hp.phi_lt_one; have := hp.b_pos; have := hp.Ph_pos
  have : 0 < 1 - p.phi := by linarith
  positivity

/-! Flow-game payoffs. -/

lemma P2_eq (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p)) (k : ℕ) :
    P2 p eta k = if Keta p eta ≤ k then p.Ph else 0 := by
  unfold P2
  by_cases h : Keta p eta ≤ k
  · rw [if_pos ((keta_spec p hp eta heta k).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((keta_spec p hp eta heta k).1 h')), if_neg h]

lemma flow_true_succ (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p))
    (k : ℕ) (hk : Keta p eta ≤ k) :
    payoff p eta .flow true k = (p.phi * p.b * p.Ph + chat p k) * p.RS := by
  unfold payoff
  simp only [delegValue, skin, P2_eq p hp eta heta, if_pos hk, chat]
  simp

lemma flow_true_fail (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p))
    (k : ℕ) (hk : ¬ Keta p eta ≤ k) : payoff p eta .flow true k = 0 := by
  unfold payoff
  simp only [delegValue, skin, P2_eq p hp eta heta, if_neg hk]
  simp

lemma flow_false_succ (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p))
    (k : ℕ) (hk : Keta p eta ≤ k) :
    payoff p eta .flow false k = (p.phi * p.b * p.Ph + p.c) * p.RS := by
  have h2 := keta_pos p hp eta heta
  have hk0 : k ≠ 0 := by omega
  unfold payoff
  simp only [delegValue, skin, P2_eq p hp eta heta, if_pos hk, if_neg hk0]
  simp

lemma flow_false_fail (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p))
    (k : ℕ) (hk : ¬ Keta p eta ≤ k) : payoff p eta .flow false k = p.c * p.RS := by
  unfold payoff
  simp only [delegValue, skin, P2_eq p hp eta heta, if_neg hk]
  simp

/-- Existence of a successful pure Nash equilibrium of the flow subgame. -/
lemma flow_pure_success (p : Params) (hp : p.Standing) (eta : ℝ)
    (heta : eta ∈ Set.Ioc p.b (alpha p)) (hc : p.c ≤ p.phi * p.b * p.Ph + chat p (Keta p eta)) :
    ∃ s : Fin p.N → Bool, Keta p eta ≤ numEngaged s ∧
      AGT.IsPureNash (subgamePayoff p eta .flow) s ∧ eta ≤ (numEngaged s : ℝ) * p.b := by
  classical
  set K := Keta p eta with hKdef
  have hK2 := keta_pos p hp eta heta
  have hKN := keta_le_N p hp eta heta
  have hRS : 0 < p.RS := by linarith [hp.one_lt_RS]
  let S := (Finset.range (p.N + 1)).filter
    (fun k => K ≤ k ∧ p.c ≤ (if k = K then p.phi * p.b * p.Ph else 0) + chat p k)
  have hKS : K ∈ S := by
    simp only [S, mem_filter, mem_range]
    refine ⟨by omega, le_rfl, ?_⟩
    simpa using hc
  set k := S.max' ⟨K, hKS⟩ with hkdef
  have hkS : k ∈ S := max'_mem _ _
  simp only [S, mem_filter, mem_range] at hkS
  obtain ⟨hkN, hKk, hck⟩ := hkS
  have hnext : k + 1 ≤ p.N → chat p (k + 1) < p.c := by
    intro hk1
    by_contra hcon
    push_neg at hcon
    have hmem : k + 1 ∈ S := by
      simp only [S, mem_filter, mem_range]
      refine ⟨by omega, by omega, ?_⟩
      rw [if_neg (by omega)]
      simpa using hcon
    have := le_max' S (k + 1) hmem
    omega
  refine ⟨fun j => decide (j.val < k), ?_, ?_, ?_⟩
  · rw [numEngaged_lt k (by omega)]; exact hKk
  · apply pure_crit p eta .flow _ k (numEngaged_lt k (by omega))
    · intro _
      rw [flow_true_succ p hp eta heta k hKk]
      by_cases hkK : k = K
      · rw [flow_false_fail p hp eta heta (k - 1) (by omega)]
        rw [if_pos hkK] at hck
        rw [hkK]
        rw [hkK] at hck
        exact mul_le_mul_of_nonneg_right hck hRS.le
      · rw [flow_false_succ p hp eta heta (k - 1) (by omega)]
        rw [if_neg hkK] at hck
        apply mul_le_mul_of_nonneg_right _ hRS.le
        linarith
    · intro hk1
      rw [flow_true_succ p hp eta heta (k + 1) (by omega), flow_false_succ p hp eta heta k hKk]
      apply mul_le_mul_of_nonneg_right _ hRS.le
      have := hnext (by omega)
      linarith
  · rw [numEngaged_lt k (by omega)]
    exact (keta_spec p hp eta heta k).2 hKk

lemma flow_dominated_alpha (p : Params) (hp : p.Standing) (eta : ℝ)
    (hα : alpha p < eta) : ∀ τ : Fin p.N → Bool → ℝ,
      AGT.IsMixedNash (subgamePayoff p eta .flow) τ → ∀ i, τ i true = 0 := by
  have hRS : 0 < p.RS := by linarith [hp.one_lt_RS]
  have hb := hp.b_pos
  refine game_dominated p eta .flow (p.c * p.RS) (mul_pos hp.c_pos hRS) (fun m hm => ?_)
  have hP : ∀ k : ℕ, k ≤ p.N → P2 p eta k = 0 := by
    intro k hk
    unfold P2
    rw [if_neg]
    unfold alpha at hα
    have : (k : ℝ) ≤ p.N := by exact_mod_cast hk
    push_neg
    nlinarith
  unfold payoff
  simp only [delegValue, skin, hP (m + 1) hm, hP m (by omega)]
  simp

/-- Engagement is strictly dominated in the flow subgame when `η > α` or `c > φ b Ph + ĉ(Kη)`. -/
lemma flow_dominated (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b p.U)
    (h : alpha p < eta ∨ p.phi * p.b * p.Ph + chat p (Keta p eta) < p.c) :
    ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .flow) τ →
      ∀ i, τ i true = 0 := by
  have hRS : 0 < p.RS := by linarith [hp.one_lt_RS]
  have hb := hp.b_pos
  have hPh := hp.Ph_pos
  have hphi := hp.phi_pos
  by_cases hα : eta ≤ alpha p
  · have hc : p.phi * p.b * p.Ph + chat p (Keta p eta) < p.c := by
      rcases h with h | h
      · exact absurd hα (not_le.mpr h)
      · exact h
    have heta' : eta ∈ Set.Ioc p.b (alpha p) := ⟨heta.1, hα⟩
    set K := Keta p eta
    have hK2 := keta_pos p hp eta heta'
    have hchK := chat_nonneg p hp K (by omega)
    refine game_dominated p eta .flow ((p.c - (p.phi * p.b * p.Ph + chat p K)) * p.RS)
      (mul_pos (by linarith) hRS) (fun m hm => ?_)
    by_cases h1 : K ≤ m + 1
    · rw [flow_true_succ p hp eta heta' _ h1]
      have hch := chat_anti p hp K (m + 1) (by omega) h1
      by_cases h0 : K ≤ m
      · rw [flow_false_succ p hp eta heta' _ h0]
        have : 0 < p.phi * p.b * p.Ph := by positivity
        nlinarith
      · rw [flow_false_fail p hp eta heta' _ h0]
        nlinarith
    · rw [flow_true_fail p hp eta heta' _ h1, flow_false_fail p hp eta heta' _ (by omega)]
      have : 0 < p.phi * p.b * p.Ph := by positivity
      nlinarith
  · push_neg at hα
    exact flow_dominated_alpha p hp eta hα

/-- Dominance in the delegated game without flow and the proprietary game. -/
lemma P2_diff (p : Params) (hp : p.Standing) (eta : ℝ) (m : ℕ) :
    0 ≤ P2 p eta m ∧ P2 p eta (m + 1) ≤ p.Ph ∧ P2 p eta m ≤ P2 p eta (m + 1) := by
  have hPh := hp.Ph_pos
  have hb := hp.b_pos
  unfold P2
  refine ⟨by split_ifs <;> linarith, by split_ifs <;> linarith, ?_⟩
  by_cases h : eta ≤ (m : ℝ) * p.b
  · rw [if_pos h, if_pos]
    push_cast; nlinarith
  · rw [if_neg h]; split_ifs <;> linarith

lemma noFlow_dominated (p : Params) (hp : p.Standing) (eta : ℝ)
    (hc : p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph < p.c) :
    ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .noFlow) τ →
      ∀ i, τ i true = 0 := by
  have hRS : 0 < p.RS := by linarith [hp.one_lt_RS]
  refine game_dominated p eta .noFlow
    ((p.c - (p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph)) * p.RS)
    (mul_pos (by linarith) hRS) (fun m _ => ?_)
  obtain ⟨h0, h1, h2⟩ := P2_diff p hp eta m
  unfold payoff
  simp only [delegValue, skin]
  simp only [Bool.false_eq_true, if_true, if_false]
  apply le_of_sub_nonneg
  have hco : 0 ≤ p.phi * p.b + p.w * (1 - p.phi) * p.b := by
    have := hp.w_pos; have := hp.phi_lt_one; have := hp.b_pos; have := hp.phi_pos
    have : 0 < 1 - p.phi := by linarith
    positivity
  have key : (p.phi * p.b + p.w * (1 - p.phi) * p.b) * (P2 p eta (m + 1) - P2 p eta m) ≤
      (p.phi * p.b + p.w * (1 - p.phi) * p.b) * p.Ph :=
    mul_le_mul_of_nonneg_left (by linarith) hco
  have : 0 ≤ (p.c - (p.phi * p.b + p.w * (1 - p.phi) * p.b) * (P2 p eta (m + 1) - P2 p eta m))
      - (p.c - (p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph)) := by nlinarith
  have := mul_nonneg this hRS.le
  push_cast
  nlinarith

lemma prop_dominated (p : Params) (hp : p.Standing) (eta : ℝ) (hc : p.b * p.Ph < p.c) :
    ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .proprietary) τ →
      ∀ i, τ i true = 0 := by
  have hRS : 0 < p.RS := by linarith [hp.one_lt_RS]
  refine game_dominated p eta .proprietary ((p.c - p.b * p.Ph) * p.RS)
    (mul_pos (by linarith) hRS) (fun m _ => ?_)
  obtain ⟨h0, h1, h2⟩ := P2_diff p hp eta m
  have hb := hp.b_pos
  unfold payoff
  simp only [delegValue, skin]
  simp only [Bool.false_eq_true, if_true, if_false, sub_self, zero_mul, mul_zero, add_zero,
    zero_add, one_mul]
  have : p.b * (P2 p eta (m + 1) - P2 p eta m) ≤ p.b * p.Ph :=
    mul_le_mul_of_nonneg_left (by linarith) hb.le
  push_cast
  nlinarith

/-- Existence of a maximal success equilibrium of the flow game. -/
lemma flow_maxSuccess_exists (p : Params) (hp : p.Standing) :
    ∃ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .flow σ := by
  classical
  let σ : ℝ → Fin p.N → Bool → ℝ := fun eta =>
    if h : ∃ s : Fin p.N → Bool, AGT.IsPureNash (subgamePayoff p eta .flow) s ∧
        eta ≤ (numEngaged s : ℝ) * p.b
    then pureLottery h.choose else pureLottery (fun _ => false)
  refine ⟨σ, fun eta heta => ?_⟩
  have hb := hp.b_pos
  have heta0 : 0 < eta := lt_trans hb heta.1
  by_cases h : ∃ s : Fin p.N → Bool, AGT.IsPureNash (subgamePayoff p eta .flow) s ∧
        eta ≤ (numEngaged s : ℝ) * p.b
  · have hσ : σ eta = pureLottery h.choose := by simp only [σ, dif_pos h]
    rw [hσ]
    refine ⟨pureNash_mixed _ _ h.choose_spec.1, fun τ hτ => ?_⟩
    rw [success_pure, if_pos h.choose_spec.2]
    exact success_le_one p eta τ hτ.1
  · have hσ : σ eta = pureLottery (fun _ => false) := by simp only [σ, dif_neg h]
    rw [hσ]
    have hdom : alpha p < eta ∨ p.phi * p.b * p.Ph + chat p (Keta p eta) < p.c := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨s, -, hs1, hs2⟩ := flow_pure_success p hp eta ⟨heta.1, hcon.1⟩ hcon.2
      exact h ⟨s, hs1, hs2⟩
    refine ⟨pureNash_mixed _ _ ?_, fun τ hτ => ?_⟩
    · apply pure_crit p eta .flow _ 0 numEngaged_false
      · intro h; omega
      · intro _
        have hP : ∀ k : ℕ, k ≤ 1 → P2 p eta k = 0 := by
          intro k hk
          unfold P2
          rw [if_neg]
          have : (k : ℝ) ≤ 1 := by exact_mod_cast hk
          push_neg
          nlinarith [heta.1]
        unfold payoff
        simp only [delegValue, skin, hP 1 le_rfl, hP 0 (by omega)]
        have := hp.c_pos
        have : 0 < p.RS := by linarith [hp.one_lt_RS]
        simp
        positivity
    · rw [success_zero p eta heta0 τ (flow_dominated p hp eta heta hdom τ hτ)]
      rw [success_pure, numEngaged_false]
      simp [not_le.mpr heta0]

end WPAux

namespace WPAux
open WolfPack.FlowEngage

lemma flow_success_one (p : Params) (hp : p.Standing) (σ : ℝ → Fin p.N → Bool → ℝ)
    (hσ : IsMaxSuccessEq p .flow σ) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p))
    (hc : p.c ≤ p.phi * p.b * p.Ph + chat p (Keta p eta)) : successProb p eta (σ eta) = 1 := by
  have hU : eta ∈ Set.Ioc p.b p.U := ⟨heta.1, heta.2.trans (alpha_le_U p hp)⟩
  obtain ⟨hN, hmax⟩ := hσ eta hU
  obtain ⟨s, -, hs, hsucc⟩ := flow_pure_success p hp eta heta hc
  have := hmax _ (pureNash_mixed _ _ hs)
  rw [success_pure, if_pos hsucc] at this
  exact le_antisymm (success_le_one p eta _ hN.1) this

lemma keta_two (p : Params) (hp : p.Standing) (hN : 2 ≤ p.N) : Keta p (2 * p.b) = 2 := by
  have hb := hp.b_pos
  have heta : 2 * p.b ∈ Set.Ioc p.b (alpha p) := by
    refine ⟨by linarith, ?_⟩
    unfold alpha
    have : (2 : ℝ) ≤ p.N := by exact_mod_cast hN
    nlinarith
  have h1 := (keta_spec p hp _ heta 2).1 (by push_cast; linarith)
  have h2 := keta_pos p hp _ heta
  omega

end WPAux


namespace WPAux
open Finset WolfPack.FlowEngage

/-- The pure profile in which the first `k` funds engage. -/
def prof (n k : ℕ) : Fin n → Bool := fun j => decide (j.val < k)

lemma numEngaged_prof (n k : ℕ) (hk : k ≤ n) : numEngaged (prof n k) = k := numEngaged_lt k hk

lemma flow_profile_nash (p : Params) (hp : p.Standing) (eta : ℝ)
    (heta : eta ∈ Set.Ioc p.b (alpha p)) (k : ℕ) (hKk : Keta p eta ≤ k) (hkN : k ≤ p.N)
    (h1 : k = Keta p eta → p.c ≤ p.phi * p.b * p.Ph + chat p k)
    (h1' : k ≠ Keta p eta → p.c ≤ chat p k)
    (h2 : k < p.N → chat p (k + 1) ≤ p.c) :
    AGT.IsPureNash (subgamePayoff p eta .flow) (prof p.N k) := by
  have hK2 := keta_pos p hp eta heta
  have hRS : 0 < p.RS := by linarith [hp.one_lt_RS]
  apply pure_crit p eta .flow _ k (numEngaged_lt k hkN)
  · intro _
    rw [flow_true_succ p hp eta heta k hKk]
    by_cases hkK : k = Keta p eta
    · rw [flow_false_fail p hp eta heta (k - 1) (by omega)]
      exact mul_le_mul_of_nonneg_right (h1 hkK) hRS.le
    · rw [flow_false_succ p hp eta heta (k - 1) (by omega)]
      apply mul_le_mul_of_nonneg_right _ hRS.le
      linarith [h1' hkK]
  · intro hk1
    rw [flow_true_succ p hp eta heta (k + 1) (by omega), flow_false_succ p hp eta heta k hKk]
    apply mul_le_mul_of_nonneg_right _ hRS.le
    linarith [h2 hk1]

/-! The flow maximal success equilibrium, explicitly. -/

noncomputable def flowSigma (p : Params) : ℝ → Fin p.N → Bool → ℝ := fun eta =>
  by classical exact
    if h : ∃ s : Fin p.N → Bool, AGT.IsPureNash (subgamePayoff p eta .flow) s ∧
        eta ≤ (numEngaged s : ℝ) * p.b
    then pureLottery h.choose else pureLottery (fun _ => false)

lemma allFalse_nash (p : Params) (hp : p.Standing) (eta : ℝ) (heta : p.b < eta) (g : GameKind) :
    AGT.IsPureNash (subgamePayoff p eta g) (fun _ => false) := by
  have hb := hp.b_pos
  apply pure_crit p eta g _ 0 numEngaged_false
  · intro h; omega
  · intro _
    have hP : ∀ k : ℕ, k ≤ 1 → P2 p eta k = 0 := by
      intro k hk
      unfold P2
      rw [if_neg]
      have : (k : ℝ) ≤ 1 := by exact_mod_cast hk
      push_neg
      nlinarith
    have := hp.c_pos
    have : 0 < p.RS := by linarith [hp.one_lt_RS]
    unfold payoff
    cases g <;> simp only [delegValue, skin, hP 1 le_rfl, hP 0 (by omega)] <;> simp <;> positivity

lemma flowSigma_max (p : Params) (hp : p.Standing) : IsMaxSuccessEq p .flow (flowSigma p) := by
  classical
  intro eta heta
  have hb := hp.b_pos
  have heta0 : 0 < eta := lt_trans hb heta.1
  by_cases h : ∃ s : Fin p.N → Bool, AGT.IsPureNash (subgamePayoff p eta .flow) s ∧
        eta ≤ (numEngaged s : ℝ) * p.b
  · have hσ : flowSigma p eta = pureLottery h.choose := by
      simp only [flowSigma]; rw [dif_pos h]
    rw [hσ]
    refine ⟨pureNash_mixed _ _ h.choose_spec.1, fun τ hτ => ?_⟩
    rw [success_pure, if_pos h.choose_spec.2]
    exact success_le_one p eta τ hτ.1
  · have hσ : flowSigma p eta = pureLottery (fun _ => false) := by
      simp only [flowSigma]; rw [dif_neg h]
    rw [hσ]
    have hdom : alpha p < eta ∨ p.phi * p.b * p.Ph + chat p (Keta p eta) < p.c := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨s, -, hs1, hs2⟩ := flow_pure_success p hp eta ⟨heta.1, hcon.1⟩ hcon.2
      exact h ⟨s, hs1, hs2⟩
    refine ⟨pureNash_mixed _ _ (allFalse_nash p hp eta heta.1 .flow), fun τ hτ => ?_⟩
    rw [success_zero p eta heta0 τ (flow_dominated p hp eta heta hdom τ hτ)]
    rw [success_pure, numEngaged_false]
    simp [not_le.mpr heta0]

lemma flowSigma_pure (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p))
    (hc : p.c ≤ p.phi * p.b * p.Ph + chat p (Keta p eta)) :
    ∃ s : Fin p.N → Bool, Keta p eta ≤ numEngaged s ∧ flowSigma p eta = pureLottery s ∧
      successProb p eta (flowSigma p eta) = 1 := by
  classical
  have h : ∃ s : Fin p.N → Bool, AGT.IsPureNash (subgamePayoff p eta .flow) s ∧
        eta ≤ (numEngaged s : ℝ) * p.b := by
    obtain ⟨s, -, hs1, hs2⟩ := flow_pure_success p hp eta heta hc
    exact ⟨s, hs1, hs2⟩
  have hσ : flowSigma p eta = pureLottery h.choose := by
    simp only [flowSigma]; rw [dif_pos h]
  refine ⟨h.choose, (keta_spec p hp eta heta _).1 h.choose_spec.2, hσ, ?_⟩
  rw [hσ, success_pure, if_pos h.choose_spec.2]

/-! Games without competition for flow (no-flow and proprietary). -/

noncomputable def kap (p : Params) (g : GameKind) : ℝ := skin p g + p.w * (1 - skin p g)

lemma nf_payoff (p : Params) (eta : ℝ) (g : GameKind) (hg : g ≠ .flow) (a : Bool) (k : ℕ) :
    payoff p eta g a k = (kap p g * p.b * P2 p eta k + if a then 0 else p.c) * p.RS := by
  unfold payoff kap
  cases g
  · exact absurd rfl hg
  · simp only [delegValue]; ring
  · simp only [delegValue]; ring

lemma kap_pos (p : Params) (hp : p.Standing) (g : GameKind) (hg : g ≠ .flow) : 0 < kap p g := by
  unfold kap
  have := hp.w_pos; have := hp.phi_lt_one; have := hp.phi_pos
  cases g
  · exact absurd rfl hg
  · simp only [skin]; nlinarith
  · simp only [skin]; nlinarith

lemma nf_dominated (p : Params) (hp : p.Standing) (eta : ℝ) (g : GameKind) (hg : g ≠ .flow)
    (h : alpha p < eta ∨ kap p g * p.b * p.Ph < p.c) :
    ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta g) τ → ∀ i, τ i true = 0 := by
  have hRS : 0 < p.RS := by linarith [hp.one_lt_RS]
  have hb := hp.b_pos
  have hk := kap_pos p hp g hg
  have hkb : 0 < kap p g * p.b := mul_pos hk hb
  rcases h with hα | hc
  · refine game_dominated p eta g (p.c * p.RS) (mul_pos hp.c_pos hRS) (fun m hm => ?_)
    have hP : ∀ k : ℕ, k ≤ p.N → P2 p eta k = 0 := by
      intro k hk
      unfold P2
      rw [if_neg]
      unfold alpha at hα
      have : (k : ℝ) ≤ p.N := by exact_mod_cast hk
      push_neg
      nlinarith
    rw [nf_payoff p eta g hg, nf_payoff p eta g hg, hP (m + 1) hm, hP m (by omega)]
    simp
  · refine game_dominated p eta g ((p.c - kap p g * p.b * p.Ph) * p.RS)
      (mul_pos (by linarith) hRS) (fun m _ => ?_)
    obtain ⟨h0, h1, h2⟩ := P2_diff p hp eta m
    rw [nf_payoff p eta g hg, nf_payoff p eta g hg]
    simp only [Bool.false_eq_true, if_true, if_false]
    have key : kap p g * p.b * (P2 p eta (m + 1) - P2 p eta m) ≤ kap p g * p.b * p.Ph :=
      mul_le_mul_of_nonneg_left (by linarith) hkb.le
    have : 0 ≤ (p.c - kap p g * p.b * (P2 p eta (m + 1) - P2 p eta m))
        - (p.c - kap p g * p.b * p.Ph) := by linarith
    have := mul_nonneg this hRS.le
    nlinarith

lemma nf_K_nash (p : Params) (hp : p.Standing) (eta : ℝ) (g : GameKind) (hg : g ≠ .flow)
    (heta : eta ∈ Set.Ioc p.b (alpha p)) (hc : p.c ≤ kap p g * p.b * p.Ph) :
    AGT.IsPureNash (subgamePayoff p eta g) (prof p.N (Keta p eta)) := by
  have hK2 := keta_pos p hp eta heta
  have hKN := keta_le_N p hp eta heta
  have hRS : 0 < p.RS := by linarith [hp.one_lt_RS]
  have hc0 := hp.c_pos
  apply pure_crit p eta g _ _ (numEngaged_lt _ hKN)
  · intro _
    rw [nf_payoff p eta g hg, nf_payoff p eta g hg, P2_eq p hp eta heta, P2_eq p hp eta heta,
      if_pos le_rfl, if_neg (by omega)]
    simp only [Bool.false_eq_true, if_true, if_false]
    apply mul_le_mul_of_nonneg_right _ hRS.le
    linarith
  · intro _
    rw [nf_payoff p eta g hg, nf_payoff p eta g hg, P2_eq p hp eta heta, P2_eq p hp eta heta,
      if_pos (by omega), if_pos le_rfl]
    simp only [Bool.false_eq_true, if_true, if_false]
    apply mul_le_mul_of_nonneg_right _ hRS.le
    linarith

lemma success_prof_K (p : Params) (hp : p.Standing) (eta : ℝ) (heta : eta ∈ Set.Ioc p.b (alpha p)) :
    successProb p eta (pureLottery (prof p.N (Keta p eta))) = 1 := by
  rw [success_pure, numEngaged_prof _ _ (keta_le_N p hp eta heta),
    if_pos ((keta_spec p hp eta heta _).2 le_rfl)]

noncomputable def nfSigma (p : Params) (g : GameKind) : ℝ → Fin p.N → Bool → ℝ := fun eta =>
  by classical exact
    if p.b < eta ∧ eta ≤ alpha p ∧ p.c ≤ kap p g * p.b * p.Ph
    then pureLottery (prof p.N (Keta p eta)) else pureLottery (fun _ => false)

lemma nfSigma_max (p : Params) (hp : p.Standing) (g : GameKind) (hg : g ≠ .flow) :
    IsMaxSuccessEq p g (nfSigma p g) := by
  classical
  intro eta heta
  have hb := hp.b_pos
  have heta0 : 0 < eta := lt_trans hb heta.1
  by_cases h : p.b < eta ∧ eta ≤ alpha p ∧ p.c ≤ kap p g * p.b * p.Ph
  · have hσ : nfSigma p g eta = pureLottery (prof p.N (Keta p eta)) := by
      simp only [nfSigma]; rw [if_pos h]
    rw [hσ]
    refine ⟨pureNash_mixed _ _ (nf_K_nash p hp eta g hg ⟨h.1, h.2.1⟩ h.2.2), fun τ hτ => ?_⟩
    rw [success_prof_K p hp eta ⟨h.1, h.2.1⟩]
    exact success_le_one p eta τ hτ.1
  · have hσ : nfSigma p g eta = pureLottery (fun _ => false) := by
      simp only [nfSigma]; rw [if_neg h]
    rw [hσ]
    have hdom : alpha p < eta ∨ kap p g * p.b * p.Ph < p.c := by
      by_contra hcon
      push_neg at hcon
      exact h ⟨heta.1, hcon.1, hcon.2⟩
    refine ⟨pureNash_mixed _ _ (allFalse_nash p hp eta heta.1 g), fun τ hτ => ?_⟩
    rw [success_zero p eta heta0 τ (nf_dominated p hp eta g hg hdom τ hτ)]
    rw [success_pure, numEngaged_false]
    simp [not_le.mpr heta0]

lemma nf_success_one (p : Params) (hp : p.Standing) (g : GameKind) (hg : g ≠ .flow)
    (σ : ℝ → Fin p.N → Bool → ℝ) (hσ : IsMaxSuccessEq p g σ) (eta : ℝ)
    (heta : eta ∈ Set.Ioc p.b (alpha p)) (hc : p.c ≤ kap p g * p.b * p.Ph) :
    successProb p eta (σ eta) = 1 := by
  have hU : eta ∈ Set.Ioc p.b p.U := ⟨heta.1, heta.2.trans (alpha_le_U p hp)⟩
  obtain ⟨hN, hmax⟩ := hσ eta hU
  have := hmax _ (pureNash_mixed _ _ (nf_K_nash p hp eta g hg heta hc))
  rw [success_prof_K p hp eta heta] at this
  exact le_antisymm (success_le_one p eta _ hN.1) this

/-- A generic version of a "maximal success equilibrium" proposition for the two games
without competition for flow. -/
lemma nf_prop (p : Params) (hp : p.Standing) (g : GameKind) (hg : g ≠ .flow) :
    (∃ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p g σ ∧ ∀ eta ∈ Set.Ioc p.b (alpha p),
      p.c ≤ kap p g * p.b * p.Ph → ∃ s : Fin p.N → Bool, numEngaged s = Keta p eta ∧
        σ eta = pureLottery s ∧ successProb p eta (σ eta) = 1) ∧
    (∀ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p g σ → ∀ eta ∈ Set.Ioc p.b (alpha p),
      p.c ≤ kap p g * p.b * p.Ph → successProb p eta (σ eta) = 1) ∧
    (∀ eta ∈ Set.Ioc p.b p.U, (alpha p < eta ∨ kap p g * p.b * p.Ph < p.c) →
      ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta g) τ → ∀ i, τ i true = 0) := by
  classical
  refine ⟨⟨nfSigma p g, nfSigma_max p hp g hg, fun eta heta hc => ?_⟩,
    fun σ hσ eta heta hc => nf_success_one p hp g hg σ hσ eta heta hc,
    fun eta _ h => nf_dominated p hp eta g hg h⟩
  have h : p.b < eta ∧ eta ≤ alpha p ∧ p.c ≤ kap p g * p.b * p.Ph := ⟨heta.1, heta.2, hc⟩
  have hσ : nfSigma p g eta = pureLottery (prof p.N (Keta p eta)) := by
    simp only [nfSigma]; rw [if_pos h]
  refine ⟨prof p.N (Keta p eta), numEngaged_prof _ _ (keta_le_N p hp eta heta), hσ, ?_⟩
  rw [hσ, success_prof_K p hp eta heta]

lemma kap_noFlow (p : Params) : kap p .noFlow * p.b * p.Ph =
    p.phi * p.b * p.Ph + p.w * (1 - p.phi) * p.b * p.Ph := by
  unfold kap skin; ring

lemma kap_prop (p : Params) : kap p .proprietary * p.b * p.Ph = p.b * p.Ph := by
  unfold kap skin; ring

end WPAux


open WolfPack.FlowEngage WPAux

theorem solution (p : Params) (hp : p.Standing) : (∃ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .flow σ ∧ ∀ eta ∈ Set.Ioc p.b (alpha p), p.c ≤ p.phi * p.b * p.Ph + chat p (Keta p eta) → ∃ s : Fin p.N → Bool, Keta p eta ≤ numEngaged s ∧ σ eta = pureLottery s ∧ successProb p eta (σ eta) = 1) ∧ (∀ σ : ℝ → Fin p.N → Bool → ℝ, IsMaxSuccessEq p .flow σ → ∀ eta ∈ Set.Ioc p.b (alpha p), p.c ≤ p.phi * p.b * p.Ph + chat p (Keta p eta) → successProb p eta (σ eta) = 1) ∧ (∀ eta ∈ Set.Ioc p.b p.U, (alpha p < eta ∨ p.phi * p.b * p.Ph + chat p (Keta p eta) < p.c) → ∀ τ : Fin p.N → Bool → ℝ, AGT.IsMixedNash (subgamePayoff p eta .flow) τ → ∀ i, τ i true = 0) :=
  ⟨⟨flowSigma p, flowSigma_max p hp, fun eta heta hc => flowSigma_pure p hp eta heta hc⟩,
    fun σ hσ eta heta hc => flow_success_one p hp σ hσ eta heta hc,
    fun eta heta h => flow_dominated p hp eta heta h⟩
