-- Prove2me | solution 1 for VeinottWagnerSS.Bounds.lemma4_SLow_rule
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T03:12:32.392249+00:00
-- url     : https://prove2.me/submissions/7beffdd4-b4ab-41c7-8d5a-b7644b2ce775

import Mathlib
import Definitions.Def_VeinottWagnerSS_Bounds_Model
import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers

open scoped ENNReal


namespace VeinottWagnerSS.Bounds

section GFacts
variable (G : ℤ → ℝ)

lemma vw_incr_mono (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (a b : ℤ) (hab : a ≤ b) : G (a + 1) - G a ≤ G (b + 1) - G b := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hconv (a + k)
    have e1 : a + (k : ℤ) + 2 = a + ((k + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    have e2 : a + (k : ℤ) + 1 = a + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e1, e2] at h
    rw [e2] at ih
    linarith [ih (by omega)]

lemma vw_bdd_below (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) (c : ℝ) :
    ∃ N : ℤ, ∀ y, G y ≤ c → N < y := by
  have := Filter.tendsto_atTop.1 hG_bot (c + 1)
  obtain ⟨N, hN⟩ := Filter.eventually_atBot.1 this
  refine ⟨N, fun y hy => ?_⟩
  by_contra h
  have := hN y (by omega)
  linarith

lemma vw_exists_min (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) :
    ∃ m : ℤ, ∀ z, G m ≤ G z := by
  obtain ⟨N1, hN1⟩ := Filter.eventually_atBot.1 (Filter.tendsto_atTop.1 hG_bot (G 0 + 1))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hG_top (G 0 + 1))
  obtain ⟨m, hm, hmin⟩ := (Finset.Icc (min N1 0) (max N2 0)).exists_min_image G
    ⟨0, by simp⟩
  refine ⟨m, fun z => ?_⟩
  have h0 : G m ≤ G 0 := hmin 0 (by simp)
  by_cases hz : z ∈ Finset.Icc (min N1 0) (max N2 0)
  · exact hmin z hz
  · simp only [Finset.mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · have := hN1 z (by omega); linarith
    · have := hN2 z (by omega); linarith

variable (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
  (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
  (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
include hG_top hG_bot

lemma vw_SLow_min : ∀ z, G (SLow G) ≤ G z := by
  obtain ⟨m, hm⟩ := vw_exists_min G hG_top hG_bot
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G m)
  have hmem : SLow G ∈ {y : ℤ | ∀ z : ℤ, G y ≤ G z} :=
    Int.csInf_mem ⟨m, hm⟩ ⟨N, fun y hy => (hN y (hy m)).le⟩
  exact hmem

lemma vw_SLow_strict (y : ℤ) (hy : y < SLow G) : G (SLow G) < G y := by
  obtain ⟨m, hm⟩ := vw_exists_min G hG_top hG_bot
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G m)
  by_contra h
  push_neg at h
  have hmin := vw_SLow_min G hG_top hG_bot
  have : SLow G ≤ y := csInf_le ⟨N, fun y hy => (hN y (hy m)).le⟩
    (show ∀ z, G y ≤ G z from fun z => h.trans (hmin z))
  omega

include hconv

lemma vw_anti (a b : ℤ) (hab : a ≤ b) (hb : b ≤ SLow G) : G b ≤ G a := by
  have hmin := vw_SLow_min G hG_top hG_bot
  have hd : ∀ y, y < SLow G → G (y + 1) - G y ≤ 0 := by
    intro y hy
    have := vw_incr_mono G hconv y (SLow G - 1) (by omega)
    have e : SLow G - 1 + 1 = SLow G := by ring
    rw [e] at this
    linarith [hmin (SLow G - 1)]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have := hd (a + k) (by push_cast at hb; omega)
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rw [e]
    linarith [ih (by push_cast at hb ⊢; omega) (by omega)]

lemma vw_mono (a b : ℤ) (hab : a ≤ b) (ha : SLow G ≤ a) : G a ≤ G b := by
  have hmin := vw_SLow_min G hG_top hG_bot
  have hd : ∀ y, SLow G ≤ y → 0 ≤ G (y + 1) - G y := by
    intro y hy
    have := vw_incr_mono G hconv (SLow G) y hy
    linarith [hmin (SLow G + 1)]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = a + k := ⟨(b - a).toNat, by omega⟩
  induction k with
  | zero => simp
  | succ k ih =>
    have := hd (a + k) (by omega)
    have e : a + ((k + 1 : ℕ) : ℤ) = a + k + 1 := by push_cast; ring
    rw [e]
    linarith [ih (by omega)]

omit hconv in
lemma vw_sHigh_mem (K α : ℝ) (hα₁ : α ≤ 1) (hK : 0 ≤ K) :
    G (sHigh G K α) ≤ G (SLow G) + (1 - α) * K := by
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G (SLow G) + (1 - α) * K)
  have hmem : sHigh G K α ∈ {y : ℤ | G y ≤ G (SLow G) + (1 - α) * K} :=
    Int.csInf_mem ⟨SLow G, by
      show G (SLow G) ≤ G (SLow G) + (1 - α) * K
      nlinarith⟩ ⟨N, fun y hy => (hN y hy).le⟩
  exact hmem

omit hconv in
lemma vw_sHigh_le_SLow (K α : ℝ) (hα₁ : α ≤ 1) (hK : 0 ≤ K) :
    sHigh G K α ≤ SLow G := by
  obtain ⟨N, hN⟩ := vw_bdd_below G hG_bot (G (SLow G) + (1 - α) * K)
  exact csInf_le ⟨N, fun y hy => (hN y hy).le⟩
    (show G (SLow G) ≤ G (SLow G) + (1 - α) * K by nlinarith)

omit hconv in
lemma vw_SHigh_mem (K α : ℝ) :
    SLow G ≤ SHigh G K α ∧ G (SLow G) + α * K ≤ G (SHigh G K α + 1) := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (Filter.tendsto_atTop.1 hG_top (G (SLow G) + α * K))
  have hmem : SHigh G K α ∈ {y : ℤ | SLow G ≤ y ∧ G (SLow G) + α * K ≤ G (y + 1)} :=
    Int.csInf_mem ⟨max N (SLow G), le_max_right _ _, hN _ (by omega)⟩
      ⟨SLow G, fun y hy => hy.1⟩
  exact hmem

end GFacts

/-! ## cost computations -/

lemma vw_ofReal_sub (g : ℝ) :
    ((ENNReal.ofReal g : ℝ≥0∞) : EReal) - ((ENNReal.ofReal (-g) : ℝ≥0∞) : EReal) = (g : EReal) := by
  rw [EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, ← EReal.coe_sub]
  congr 1
  rcases le_total 0 g with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma vw_pc0 (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (Z : Policy) (x : ℤ) :
    periodCost φ G K Z x 0 =
      (K : EReal) * (((if x < Z 0 x finZeroElim then 1 else 0 : ℝ≥0∞)) : EReal) +
        (G (Z 0 x finZeroElim) : EReal) := by
  have hu : ∀ f : (Fin 0 → ℕ) → ℝ≥0∞, ∑' h, f h = f finZeroElim := fun f =>
    tsum_eq_single _ (fun h hh => absurd (Subsingleton.elim h _) hh)
  have hw : weight φ (finZeroElim : Fin 0 → ℕ) = 1 := by simp [weight]
  unfold periodCost orderProb expectedG
  rw [hu, hu, hu, hw, one_mul, one_mul, one_mul, vw_ofReal_sub]
  rfl

lemma vw_op1_le (φ : PMF ℕ) (Z : Policy) (x : ℤ) : orderProb φ Z x 1 ≤ 1 := by
  unfold orderProb
  calc ∑' h : Fin 1 → ℕ, weight φ h * (if state Z x 1 h < Z 1 x h then 1 else 0)
      ≤ ∑' h : Fin 1 → ℕ, φ ((Equiv.funUnique (Fin 1) ℕ) h) := by
        refine ENNReal.tsum_le_tsum fun h => ?_
        have : weight φ h = φ ((Equiv.funUnique (Fin 1) ℕ) h) := by
          simp [weight, Equiv.funUnique]
        rw [this]
        split_ifs <;> simp
    _ = 1 := by rw [(Equiv.funUnique (Fin 1) ℕ).tsum_eq (fun k => φ k), PMF.tsum_coe]

lemma vw_cost_congr (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (n : ℕ) (x : ℤ) (Y Y' : Policy)
    (h : ∀ t hh, Y' t x hh = Y t x hh) : cost φ G K α n x Y' = cost φ G K α n x Y := by
  have hs : ∀ t hh, state Y' x t hh = state Y x t hh := by
    intro t hh; cases t <;> simp [state, h]
  unfold cost periodCost orderProb expectedG
  simp only [hs, h]

/-- modification of a policy in period 0 only -/
def vwMod (Y : Policy) (r : ℤ → ℤ) : Policy := fun t x h => if t = 0 then r x else Y t x h

lemma vw_key (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hK : 0 ≤ K) (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (r : ℤ → ℤ) (x : ℤ)
    (hreal : K * (if x < r x then 1 else 0) + G (r x) + α * K ≤
      K * (if x < Y 0 x finZeroElim then 1 else 0) + G (Y 0 x finZeroElim)) :
    cost φ G K α n x (vwMod Y r) ≤ cost φ G K α n x Y := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold cost
  rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ' _ (m + 1),
    Finset.sum_range_succ']
  have hrest : ∀ t, periodCost φ G K (vwMod Y r) x (t + 2) = periodCost φ G K Y x (t + 2) := by
    intro t
    have hs : ∀ hh, state (vwMod Y r) x (t + 2) hh = state Y x (t + 2) hh := by
      intro hh; simp [state, vwMod]
    unfold periodCost orderProb expectedG
    simp only [hs]
    simp [vwMod]
  simp only [hrest]
  rw [add_assoc, add_assoc]
  refine add_le_add le_rfl ?_
  have hE : expectedG φ G (vwMod Y r) x 1 = expectedG φ G Y x 1 := by
    unfold expectedG; simp [vwMod]
  rw [vw_pc0, vw_pc0]
  unfold periodCost
  rw [hE]
  simp only [zero_add, pow_zero, EReal.coe_one, one_mul, pow_one]
  have hvm : vwMod Y r 0 x finZeroElim = r x := by simp [vwMod]
  rw [hvm]
  have hαne : ((α : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hα0 : (0 : EReal) ≤ (α : EReal) := by exact_mod_cast hα₀
  rw [EReal.left_distrib_of_nonneg_of_ne_top hα0 hαne,
    EReal.left_distrib_of_nonneg_of_ne_top hα0 hαne]
  set E := expectedG φ G Y x 1
  have hp1 : (K : EReal) * ((orderProb φ (vwMod Y r) x 1 : ℝ≥0∞) : EReal) ≤ (K : EReal) := by
    have : ((orderProb φ (vwMod Y r) x 1 : ℝ≥0∞) : EReal) ≤ 1 := by
      exact_mod_cast vw_op1_le φ (vwMod Y r) x
    calc (K : EReal) * ((orderProb φ (vwMod Y r) x 1 : ℝ≥0∞) : EReal) ≤ (K : EReal) * 1 :=
          mul_le_mul_of_nonneg_left this (by exact_mod_cast hK)
      _ = K := mul_one _
  have hp0 : (0 : EReal) ≤ (K : EReal) * ((orderProb φ Y x 1 : ℝ≥0∞) : EReal) :=
    mul_nonneg (by exact_mod_cast hK) (EReal.coe_ennreal_nonneg _)
  have hind : ∀ (b : Prop) [Decidable b], ((K : EReal) * (((if b then 1 else 0 : ℝ≥0∞)) : EReal)) =
      ((K * (if b then 1 else 0 : ℝ) : ℝ) : EReal) := by
    intro b _; split_ifs <;> simp
  rw [hind, hind]
  calc (α : EReal) * ((K : EReal) * ((orderProb φ (vwMod Y r) x 1 : ℝ≥0∞) : EReal)) + α * E +
        (((K * (if x < r x then 1 else 0 : ℝ) : ℝ) : EReal) + (G (r x) : EReal))
      ≤ (α : EReal) * K + α * E +
        (((K * (if x < r x then 1 else 0 : ℝ) : ℝ) : EReal) + (G (r x) : EReal)) := by
        gcongr
    _ = α * E + ((K * (if x < r x then 1 else 0 : ℝ) + G (r x) + α * K : ℝ) : EReal) := by
        push_cast
        abel
    _ ≤ α * E + ((K * (if x < Y 0 x finZeroElim then 1 else 0 : ℝ) + G (Y 0 x finZeroElim) : ℝ) :
          EReal) := by
        gcongr
    _ ≤ (α : EReal) * ((K : EReal) * ((orderProb φ Y x 1 : ℝ≥0∞) : EReal)) + α * E +
        (((K * (if x < Y 0 x finZeroElim then 1 else 0 : ℝ) : ℝ) : EReal) +
          (G (Y 0 x finZeroElim) : EReal)) := by
        rw [add_assoc]
        push_cast
        have : (0 : EReal) ≤ (α : EReal) * ((K : EReal) * ((orderProb φ Y x 1 : ℝ≥0∞) : EReal)) :=
          mul_nonneg hα0 hp0
        calc (α : EReal) * E + (((K * (if x < Y 0 x finZeroElim then 1 else 0 : ℝ) : ℝ) : EReal) +
              (G (Y 0 x finZeroElim) : EReal)) = 0 + ((α : EReal) * E +
              (((K * (if x < Y 0 x finZeroElim then 1 else 0 : ℝ) : ℝ) : EReal) +
              (G (Y 0 x finZeroElim) : EReal))) := (zero_add _).symm
          _ ≤ _ := add_le_add this le_rfl

lemma vw_mod_adm (Y : Policy) (hY : Admissible Y) (r : ℤ → ℤ) (h1 : ∀ x, x ≤ r x)
    (h2 : ∀ x, r x ≤ Y 0 x finZeroElim) : Admissible (vwMod Y r) := by
  intro t x h
  rcases t with _ | _ | t
  · simpa [state, vwMod] using h1 x
  · have := hY 1 x h
    have e : (Fin.init h : Fin 0 → ℕ) = finZeroElim := Subsingleton.elim _ _
    simp only [state, vwMod, e] at this ⊢
    simp
    rw [show (Fin.last 0) = (0 : Fin 1) from rfl] at this
    have := h2 x
    omega
  · simpa [state, vwMod] using hY (t + 2) x h

lemma vw_mod_rule (Y : Policy) (s S : ℤ) : UsesRule (vwMod Y (sSRule s S)) 0 s S := by
  intro x h; simp [vwMod, state]

lemma vw_mod_eq (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (n : ℕ) (Y : Policy) (r : ℤ → ℤ) (x : ℤ)
    (h : r x = Y 0 x finZeroElim) : cost φ G K α n x (vwMod Y r) = cost φ G K α n x Y := by
  apply vw_cost_congr
  intro t hh
  rcases t with _ | t
  · have e : hh = finZeroElim := Subsingleton.elim _ _
    subst e; simpa [vwMod] using h
  · simp [vwMod]

lemma vw_Y0 (Y : Policy) (s S : ℤ) (hrule : UsesRule Y 0 s S) (x : ℤ) :
    Y 0 x finZeroElim = sSRule s S x := hrule x finZeroElim

theorem lemma3_core (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) (hlt : sHigh G K α < sn) :
    ∃ Y' : Policy, Admissible Y' ∧ UsesRule Y' 0 (sHigh G K α) Sn ∧
      ∀ x : ℤ, cost φ G K α n x Y' ≤ cost φ G K α n x Y := by
  set sb := sHigh G K α with hsb
  have hY0 := vw_Y0 Y sn Sn hrule
  refine ⟨vwMod Y (sSRule sb Sn), vw_mod_adm Y hY.1 _ ?_ ?_, vw_mod_rule Y sb Sn, ?_⟩
  · intro x; unfold sSRule; split_ifs <;> omega
  · intro x; rw [hY0]; unfold sSRule; split_ifs <;> omega
  · intro x
    by_cases hx : sb ≤ x ∧ x < sn
    · apply vw_key φ G K α hα₀ hK n hn
      rw [hY0]
      have e1 : sSRule sb Sn x = x := by unfold sSRule; rw [if_neg (by omega)]
      have e2 : sSRule sn Sn x = Sn := by unfold sSRule; rw [if_pos hx.2]
      rw [e1, e2, if_neg (lt_irrefl x), if_pos (by omega)]
      have hmem := vw_sHigh_mem G hG_top hG_bot K α hα₁ hK
      have hmin := vw_SLow_min G hG_top hG_bot
      have hle := vw_sHigh_le_SLow G hG_top hG_bot K α hα₁ hK
      rcases le_or_gt x (SLow G) with h | h
      · have := vw_anti G hconv hG_top hG_bot sb x hx.1 h
        have := hmin Sn
        nlinarith
      · have := vw_mono G hconv hG_top hG_bot x Sn (by omega) h.le
        nlinarith
    · apply le_of_eq
      apply vw_mod_eq
      rw [hY0]; unfold sSRule; split_ifs <;> omega

theorem lemma4_core (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) (hs : sn ≤ sHigh G K α) (hlt : SHigh G K α < Sn) :
    ∃ Y' : Policy, Admissible Y' ∧ UsesRule Y' 0 sn (SLow G) ∧
      ∀ x : ℤ, cost φ G K α n x Y' ≤ cost φ G K α n x Y := by
  have hY0 := vw_Y0 Y sn Sn hrule
  have hle := vw_sHigh_le_SLow G hG_top hG_bot K α hα₁ hK
  obtain ⟨hSS, hSH⟩ := vw_SHigh_mem G hG_top hG_bot K α
  refine ⟨vwMod Y (sSRule sn (SLow G)), vw_mod_adm Y hY.1 _ ?_ ?_, vw_mod_rule Y sn (SLow G), ?_⟩
  · intro x; unfold sSRule; split_ifs <;> omega
  · intro x; rw [hY0]; unfold sSRule; split_ifs <;> omega
  · intro x
    by_cases hx : x < sn
    · apply vw_key φ G K α hα₀ hK n hn
      rw [hY0]
      have e1 : sSRule sn (SLow G) x = SLow G := by unfold sSRule; rw [if_pos hx]
      have e2 : sSRule sn Sn x = Sn := by unfold sSRule; rw [if_pos hx]
      rw [e1, e2, if_pos (by omega : x < Sn)]
      have := vw_mono G hconv hG_top hG_bot (SHigh G K α + 1) Sn (by omega) (by omega)
      have hi : K * (if x < SLow G then (1:ℝ) else 0) ≤ K := by
        split_ifs <;> linarith
      nlinarith
    · apply le_of_eq
      apply vw_mod_eq
      rw [hY0]; unfold sSRule; split_ifs <;> omega

end VeinottWagnerSS.Bounds

open VeinottWagnerSS.Bounds


theorem solution (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop)
    (φ : PMF ℕ) (hμ : ∑' k : ℕ, (k : ℝ≥0∞) * φ k ≠ ⊤)
    (n : ℕ) (hn : 2 ≤ n)
    (Y : Policy) (sn Sn : ℤ) (hY : IsOptimal φ G K α n Y) (hsS : sn ≤ Sn)
    (hrule : UsesRule Y 0 sn Sn) (hs : sn ≤ sHigh G K α) (hlt : SHigh G K α < Sn) :
    ∃ Y' : Policy, Admissible Y' ∧ UsesRule Y' 0 sn (SLow G) ∧
      ∀ x : ℤ, cost φ G K α n x Y' ≤ cost φ G K α n x Y := by
  exact lemma4_core G K α hα₀ hα₁ hK hconv hG_top hG_bot φ n hn Y sn Sn hY hsS hrule hs hlt
