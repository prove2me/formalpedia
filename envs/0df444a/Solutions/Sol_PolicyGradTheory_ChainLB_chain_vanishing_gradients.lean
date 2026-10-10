-- Prove2me | solution 1 for PolicyGradTheory.ChainLB.chain_vanishing_gradients
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T02:23:48.673888+00:00
-- url     : https://prove2.me/submissions/f572c0e0-2da3-4c60-8cba-c9c8502ce5e8

import Mathlib
import Definitions.Def_PolicyGradTheory_ChainLB_Chain
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy

set_option autoImplicit false

namespace P325c

open FoundationsML.ReinforcementLearning PolicyGradTheory.ChainLB

/-- Value of the deterministic successor of state value `v` under action `a`. -/
def nxtv (H v : ℕ) (a : Fin 4) : ℕ :=
  if v = 0 then 1 else if v = H + 1 then v else if a.val = 0 then v + 1 else v - 1

lemma nxtv_lt (H v : ℕ) (a : Fin 4) (hv : v < H + 2) : nxtv H v a < H + 2 := by
  unfold nxtv; split_ifs <;> omega

lemma nxtv_ne (H v : ℕ) (a : Fin 4) (ha : a.val ≠ 0) : nxtv H v a = nxtv H v 1 := by
  unfold nxtv; simp [ha]

lemma chainP_eq (H : ℕ) (s : Fin (H + 2)) (a : Fin 4) (s' : Fin (H + 2)) :
    chainP H s a s' = if s'.val = nxtv H s.val a then 1 else 0 := by
  have hs := s.isLt
  unfold chainP nxtv
  by_cases h0 : s.val = 0
  · simp [h0]
  · by_cases h1 : s.val = H + 1
    · simp [h1, Fin.ext_iff]
    · by_cases ha : a.val = 0
      · simp [h0, h1, ha]
      · simp only [h0, h1, ha, if_false]
        congr 1
        apply propext; omega

lemma sum_ind (H n : ℕ) (hn : n < H + 2) (g : ℕ → ℝ) :
    ∑ s : Fin (H + 2), (if s.val = n then (1 : ℝ) else 0) * g s.val = g n := by
  rw [Finset.sum_eq_single ⟨n, hn⟩]
  · simp
  · intro b _ hb
    have : b.val ≠ n := fun h => hb (Fin.ext h)
    simp [this]
  · simp

lemma IT_eq (H : ℕ) (π : Fin (H + 2) → Fin 4 → ℝ) (hπ : ∀ s, ∑ a, π s a = 1)
    (s s' : Fin (H + 2)) :
    InducedTransition π (chainP H) s s' =
      π s 0 * (if s'.val = nxtv H s.val 0 then 1 else 0) +
      (1 - π s 0) * (if s'.val = nxtv H s.val 1 then 1 else 0) := by
  have h := hπ s
  rw [Fin.sum_univ_four] at h
  unfold InducedTransition
  rw [Fin.sum_univ_four, chainP_eq, chainP_eq, chainP_eq, chainP_eq,
    nxtv_ne H s.val 2 (by decide), nxtv_ne H s.val 3 (by decide)]
  linear_combination (if s'.val = nxtv H s.val 1 then (1 : ℝ) else 0) * h

lemma IT_sum (H : ℕ) (π : Fin (H + 2) → Fin 4 → ℝ) (hπ : ∀ s, ∑ a, π s a = 1)
    (s : Fin (H + 2)) (g : ℕ → ℝ) :
    ∑ s', InducedTransition π (chainP H) s s' * g s'.val =
      π s 0 * g (nxtv H s.val 0) + (1 - π s 0) * g (nxtv H s.val 1) := by
  simp_rw [IT_eq H π hπ, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [sum_ind H _ (nxtv_lt H _ _ s.isLt), sum_ind H _ (nxtv_lt H _ _ s.isLt)]

lemma step_sum (H : ℕ) (π : Fin (H + 2) → Fin 4 → ℝ) (hπ : ∀ s, ∑ a, π s a = 1)
    (s0 : Fin (H + 2)) (t : ℕ) (g : ℕ → ℝ) :
    ∑ s', OccupationDist π (chainP H) s0 (t + 1) s' * g s'.val =
      ∑ s, OccupationDist π (chainP H) s0 t s *
        (π s 0 * g (nxtv H s.val 0) + (1 - π s 0) * g (nxtv H s.val 1)) := by
  show ∑ s', (∑ s, OccupationDist π (chainP H) s0 t s * InducedTransition π (chainP H) s s')
      * g s'.val = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [IT_sum H π hπ s g]

lemma occ_nonneg (H : ℕ) (π : Fin (H + 2) → Fin 4 → ℝ) (hπ : ∀ s, ∑ a, π s a = 1)
    (h0 : ∀ s, 0 ≤ π s 0 ∧ π s 0 ≤ 1) (s0 : Fin (H + 2)) :
    ∀ t s, 0 ≤ OccupationDist π (chainP H) s0 t s := by
  intro t
  induction t with
  | zero =>
    intro s
    show 0 ≤ (if s = s0 then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  | succ t ih =>
    intro s'
    show 0 ≤ ∑ s, OccupationDist π (chainP H) s0 t s * InducedTransition π (chainP H) s s'
    apply Finset.sum_nonneg
    intro s _
    apply mul_nonneg (ih s)
    rw [IT_eq H π hπ]
    have := h0 s
    exact add_nonneg (mul_nonneg this.1 (by split_ifs <;> norm_num))
      (mul_nonneg (by linarith [this.2]) (by split_ifs <;> norm_num))

lemma occ_mass (H : ℕ) (π : Fin (H + 2) → Fin 4 → ℝ) (hπ : ∀ s, ∑ a, π s a = 1)
    (s0 : Fin (H + 2)) : ∀ t, ∑ s, OccupationDist π (chainP H) s0 t s = 1 := by
  intro t
  induction t with
  | zero =>
    show ∑ s, (if s = s0 then (1 : ℝ) else 0) = 1
    simp
  | succ t ih =>
    have := step_sum H π hπ s0 t (fun _ => 1)
    simp only [mul_one] at this
    rw [this]
    simpa using ih

lemma IR_sum (H : ℕ) (π : Fin (H + 2) → Fin 4 → ℝ) (w : Fin (H + 2) → ℝ) :
    ∑ s', w s' * InducedReward π (chainR H) s' = w (Fin.last (H + 1)) * π (Fin.last (H + 1)) 0 := by
  have hIR : ∀ s', InducedReward π (chainR H) s' =
      if s' = Fin.last (H + 1) then π s' 0 else 0 := by
    intro s'
    unfold InducedReward chainR
    rw [Fin.sum_univ_four]
    by_cases h : s' = Fin.last (H + 1) <;> simp [h]
  simp_rw [hIR, mul_ite, mul_zero]
  simp

/-! ### The chain policy -/

lemma cp_sum (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2)) :
    ∑ a, chainPolicy H θ s a = 1 := by
  rw [Fin.sum_univ_four]
  by_cases hs : 0 < s.val ∧ s.val ≤ H
  · simp [chainPolicy, hs]
  · simp only [chainPolicy, dif_neg hs]
    simp

lemma cp_out (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2))
    (hs : ¬ (0 < s.val ∧ s.val ≤ H)) : chainPolicy H θ s 0 = 1 := by
  simp only [chainPolicy, dif_neg hs]
  simp

lemma cp_in (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2))
    (hs : 0 < s.val ∧ s.val ≤ H) :
    chainPolicy H θ s 0 = θ (⟨s.val - 1, by omega⟩, (0 : Fin 3)) := by
  simp [chainPolicy, hs]

lemma cp_bounds (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1) (s : Fin (H + 2)) :
    0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1 := by
  by_cases hs : 0 < s.val ∧ s.val ≤ H
  · rw [cp_in H θ s hs]
    have := hθ ⟨s.val - 1, by omega⟩ 0
    constructor <;> linarith [this.1, this.2]
  · rw [cp_out H θ s hs]; norm_num

lemma pot_step (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4) (s : Fin (H + 2)) :
    chainPolicy H θ s 0 * (3 : ℝ) ^ (nxtv H s.val 0) +
      (1 - chainPolicy H θ s 0) * (3 : ℝ) ^ (nxtv H s.val 1) ≤ (3 : ℝ) ^ s.val + 2 := by
  have hlt := s.isLt
  by_cases h0 : s.val = 0
  · simp only [nxtv, h0, if_true, pow_zero, pow_one]
    linarith
  · by_cases h1 : s.val = H + 1
    · have hne : H + 1 ≠ 0 := by omega
      simp only [nxtv, h1, hne, if_false, if_true]
      linarith
    · have hs : 0 < s.val ∧ s.val ≤ H := ⟨by omega, by omega⟩
      rw [cp_in H θ s hs]
      set q := θ (⟨s.val - 1, by omega⟩, (0 : Fin 3))
      have hq0 : 0 < q := (hθ _ _).1
      have hq1 : q < 1 / 4 := hθ1 _
      obtain ⟨w, hw⟩ : ∃ w, s.val = w + 1 := ⟨s.val - 1, by omega⟩
      have e0 : nxtv H s.val 0 = w + 2 := by unfold nxtv; simp [h0, h1]; omega
      have e1 : nxtv H s.val 1 = w := by unfold nxtv; simp [h0, h1]; omega
      rw [e0, e1, hw, pow_add, pow_add]
      have hp : (0 : ℝ) < 3 ^ w := by positivity
      nlinarith [mul_le_mul_of_nonneg_right (le_of_lt hq1) hp.le]

lemma pot_bound (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4) :
    ∀ t : ℕ, ∑ s, OccupationDist (chainPolicy H θ) (chainP H) 0 t s * (3 : ℝ) ^ s.val
      ≤ 1 + 2 * t := by
  intro t
  induction t with
  | zero =>
    show ∑ s, (if s = (0 : Fin (H + 2)) then (1 : ℝ) else 0) * (3 : ℝ) ^ s.val ≤ _
    simp
  | succ t ih =>
    rw [step_sum H _ (cp_sum H θ) 0 t (fun n => (3 : ℝ) ^ n)]
    have hnn := occ_nonneg H _ (cp_sum H θ) (cp_bounds H θ hθ) 0 t
    have hm := occ_mass H _ (cp_sum H θ) 0 t
    calc ∑ s, OccupationDist (chainPolicy H θ) (chainP H) 0 t s *
          (chainPolicy H θ s 0 * (3 : ℝ) ^ (nxtv H s.val 0) +
            (1 - chainPolicy H θ s 0) * (3 : ℝ) ^ (nxtv H s.val 1))
        ≤ ∑ s, OccupationDist (chainPolicy H θ) (chainP H) 0 t s * ((3 : ℝ) ^ s.val + 2) :=
          Finset.sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left
            (pot_step H θ hθ hθ1 s) (hnn s))
      _ = ∑ s, OccupationDist (chainPolicy H θ) (chainP H) 0 t s * (3 : ℝ) ^ s.val +
            2 * ∑ s, OccupationDist (chainPolicy H θ) (chainP H) 0 t s := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun s _ => ?_); ring
      _ ≤ 1 + 2 * ((t + 1 : ℕ) : ℝ) := by rw [hm]; push_cast; linarith

lemma occ_last_le (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4) (t : ℕ) :
    OccupationDist (chainPolicy H θ) (chainP H) 0 t (Fin.last (H + 1)) ≤
      (1 + 2 * t) / (3 : ℝ) ^ (H + 1) := by
  have hnn := occ_nonneg H _ (cp_sum H θ) (cp_bounds H θ hθ) 0 t
  have h1 := Finset.single_le_sum
    (f := fun s => OccupationDist (chainPolicy H θ) (chainP H) 0 t s * (3 : ℝ) ^ s.val)
    (fun s _ => mul_nonneg (hnn s) (by positivity)) (Finset.mem_univ (Fin.last (H + 1)))
  have h2 := pot_bound H θ hθ hθ1 t
  simp only [Fin.val_last] at h1
  rw [le_div_iff₀ (by positivity)]
  linarith

lemma gamma_facts (H : ℕ) (hH : 1 ≤ H) :
    0 ≤ chainGamma H ∧ chainGamma H < 1 ∧ 1 - chainGamma H = 1 / (H + 1) := by
  unfold chainGamma
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]; linarith
  · field_simp; ring

lemma part2 (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4) :
    chainValue H θ ≤ (H + 1 : ℝ) ^ 2 / (3 : ℝ) ^ H := by
  obtain ⟨hg0, hg1, hg2⟩ := gamma_facts H hH
  set γ := chainGamma H with hγ
  unfold chainValue PolicyValue
  simp_rw [IR_sum, cp_out H θ (Fin.last (H + 1)) (by simp), mul_one]
  rw [← hγ]
  set c : ℝ := (3 : ℝ) ^ (H + 1) with hc
  have hcpos : 0 < c := by positivity
  have hn : ‖γ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hg0]; exact hg1
  have HS : HasSum (fun t : ℕ => γ ^ t * ((1 + 2 * (t : ℝ)) / c))
      (((1 - γ)⁻¹ + 2 * (γ / (1 - γ) ^ 2)) / c) := by
    have := ((hasSum_geometric_of_lt_one hg0 hg1).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left 2)).div_const c
    have e : (fun t : ℕ => γ ^ t * ((1 + 2 * (t : ℝ)) / c)) =
        fun i : ℕ => (γ ^ i + 2 * ((i : ℝ) * γ ^ i)) / c := by
      funext t; ring
    rw [e]; exact this
  have hnn := occ_nonneg H _ (cp_sum H θ) (cp_bounds H θ hθ) 0
  have hle : ∀ t : ℕ, γ ^ t * OccupationDist (chainPolicy H θ) (chainP H) 0 t (Fin.last (H + 1))
      ≤ γ ^ t * ((1 + 2 * (t : ℝ)) / c) :=
    fun t => mul_le_mul_of_nonneg_left (occ_last_le H θ hθ hθ1 t) (by positivity)
  have hsum : Summable (fun t : ℕ =>
      γ ^ t * OccupationDist (chainPolicy H θ) (chainP H) 0 t (Fin.last (H + 1))) :=
    Summable.of_nonneg_of_le (fun t => mul_nonneg (by positivity) (hnn t _)) hle HS.summable
  refine le_trans (hasSum_le hle hsum.hasSum HS) ?_
  have e1 : (1 - γ)⁻¹ = (H + 1 : ℝ) := by rw [hg2]; simp
  have e2 : γ / (1 - γ) ^ 2 = (H : ℝ) * (H + 1) := by
    rw [hg2, hγ]; unfold chainGamma; field_simp
  rw [e1, e2, hc, pow_succ, div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (0 : ℝ) < 3 ^ H := by positivity
  have hH0 : (0 : ℝ) ≤ H := by positivity
  nlinarith [mul_pos h3 (by positivity : (0 : ℝ) < ((H : ℝ) + 1) * ((H : ℝ) + 2))]

/-! ### The always-forward policy -/

def fwd (H : ℕ) : Fin (H + 2) → Fin 4 → ℝ := fun _ a => if a.val = 0 then 1 else 0

lemma fwd_sum (H : ℕ) (s : Fin (H + 2)) : ∑ a, fwd H s a = 1 := by
  rw [Fin.sum_univ_four]; simp [fwd]

lemma fwd_policy (H : ℕ) : IsPolicy (fwd H) := by
  intro s
  refine ⟨fun a => ?_, fwd_sum H s⟩
  unfold fwd; split_ifs <;> norm_num

lemma occ_fwd (H : ℕ) : ∀ (t : ℕ) (s : Fin (H + 2)),
    OccupationDist (fwd H) (chainP H) 0 t s = if s.val = min t (H + 1) then 1 else 0 := by
  intro t
  induction t with
  | zero =>
    intro s
    show (if s = (0 : Fin (H + 2)) then (1 : ℝ) else 0) = _
    have e : (s = (0 : Fin (H + 2))) ↔ (s.val = min 0 (H + 1)) := by
      rw [Nat.zero_min]; exact ⟨fun h => by rw [h]; rfl, fun h => Fin.ext h⟩
    exact if_congr e rfl rfl
  | succ t ih =>
    intro s'
    show ∑ s, OccupationDist (fwd H) (chainP H) 0 t s * InducedTransition (fwd H) (chainP H) s s' = _
    have h1 : ∀ s : Fin (H + 2), fwd H s 0 = 1 := fun s => by simp [fwd]
    simp_rw [ih, IT_eq H (fwd H) (fwd_sum H), h1, sub_self, zero_mul, add_zero, one_mul]
    have key := sum_ind H (min t (H + 1)) (by omega)
      (fun n => if s'.val = nxtv H n 0 then (1 : ℝ) else 0)
    rw [key]
    have : nxtv H (min t (H + 1)) 0 = min (t + 1) (H + 1) := by
      unfold nxtv; split_ifs <;> simp_all <;> omega
    rw [this]

lemma gamma_pow (H : ℕ) (hH : 1 ≤ H) : (1 : ℝ) / 8 ≤ chainGamma H ^ (H + 1) := by
  have hH' : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hHp : (0 : ℝ) < H := by linarith
  have hb : (1 + 1 / (H : ℝ)) ^ (H + 1) ≤ 8 := by
    have h1 : 1 + 1 / (H : ℝ) ≤ Real.exp (1 / H) := by
      have := Real.add_one_le_exp (1 / (H : ℝ)); linarith
    have h2 : (1 + 1 / (H : ℝ)) ^ (H + 1) ≤ Real.exp (1 / H) ^ (H + 1) :=
      pow_le_pow_left₀ (by positivity) h1 _
    rw [← Real.exp_nat_mul] at h2
    have h3 : ((H + 1 : ℕ) : ℝ) * (1 / H) ≤ 2 := by
      push_cast; rw [add_mul, mul_one_div_cancel hHp.ne']
      have : 1 * (1 / (H : ℝ)) ≤ 1 := by rw [one_mul, div_le_one hHp]; exact hH'
      linarith
    have h4 : Real.exp 2 ≤ 8 := by
      have := Real.exp_one_lt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have h0 : 0 < Real.exp 1 := Real.exp_pos 1
      nlinarith
    calc _ ≤ _ := h2
      _ ≤ Real.exp 2 := Real.exp_le_exp.mpr h3
      _ ≤ 8 := h4
  have hprod : chainGamma H ^ (H + 1) * (1 + 1 / (H : ℝ)) ^ (H + 1) = 1 := by
    rw [← mul_pow]
    have : chainGamma H * (1 + 1 / (H : ℝ)) = 1 := by
      unfold chainGamma; field_simp
    rw [this, one_pow]
  have hpos : 0 < (1 + 1 / (H : ℝ)) ^ (H + 1) := by positivity
  have hg : 0 ≤ chainGamma H ^ (H + 1) := by unfold chainGamma; positivity
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
  nlinarith

lemma part1 (H : ℕ) (hH : 1 ≤ H) :
    (H + 1 : ℝ) / 8 ≤ PolicyValue (fwd H) (chainP H) (chainR H) (chainGamma H) 0 := by
  obtain ⟨hg0, hg1, hg2⟩ := gamma_facts H hH
  unfold PolicyValue
  have hl : fwd H (Fin.last (H + 1)) 0 = 1 := by simp [fwd]
  simp_rw [IR_sum, hl, mul_one, occ_fwd H, Fin.val_last]
  set γ := chainGamma H with hγ
  set f : ℕ → ℝ := fun t => γ ^ t * (if H + 1 = min t (H + 1) then 1 else 0) with hf
  have hshift : HasSum (fun n => f (n + (H + 1))) (γ ^ (H + 1) * (1 - γ)⁻¹) := by
    have e : (fun n => f (n + (H + 1))) = fun n => γ ^ (H + 1) * γ ^ n := by
      funext n
      simp only [hf]
      rw [if_pos (by omega), pow_add]; ring
    rw [e]
    exact (hasSum_geometric_of_lt_one hg0 hg1).mul_left (γ ^ (H + 1))
  have hzero : ∑ i ∈ Finset.range (H + 1), f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [hf]
    rw [if_neg (by omega), mul_zero]
  have HS : HasSum f (γ ^ (H + 1) * (1 - γ)⁻¹) := by
    rw [← hasSum_nat_add_iff' (H + 1), hzero, sub_zero]
    exact hshift
  rw [HS.tsum_eq, hg2]
  have := gamma_pow H hH
  rw [← hγ] at this
  have hpos : (0 : ℝ) < H + 1 := by positivity
  rw [one_div, inv_inv]
  nlinarith

end P325c

/-! ## Vanishing gradients (conjunct I) -/

namespace P0226

open FoundationsML.ReinforcementLearning PolicyGradTheory.ChainLB P325c

/-- The open parameter box on which the value is a resolvent entry. -/
def Ubox (H : ℕ) : Set (EuclideanSpace ℝ (Fin H × Fin 3)) :=
  {θ | ∀ i, 0 < θ (i, 0) ∧ θ (i, 0) < 1 / 4}

lemma isOpen_Ubox (H : ℕ) : IsOpen (Ubox H) := by
  have : Ubox H = ⋂ i : Fin H,
      (fun θ : EuclideanSpace ℝ (Fin H × Fin 3) => θ (i, 0)) ⁻¹' Set.Ioo 0 (1 / 4) := by
    ext θ; simp [Ubox, Set.mem_iInter]
  rw [this]
  refine isOpen_iInter_of_finite fun i => ?_
  exact isOpen_Ioo.preimage (PiLp.continuous_apply 2 _ (i, 0))

lemma cpU (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (hθ : θ ∈ Ubox H)
    (s : Fin (H + 2)) : 0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1 := by
  by_cases hs : 0 < s.val ∧ s.val ≤ H
  · rw [cp_in H θ s hs]
    have := hθ ⟨s.val - 1, by omega⟩
    constructor <;> linarith [this.1, this.2]
  · rw [cp_out H θ s hs]; norm_num

lemma pot_step' (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (hθ : θ ∈ Ubox H)
    (s : Fin (H + 2)) :
    chainPolicy H θ s 0 * (3 : ℝ) ^ (nxtv H s.val 0) +
      (1 - chainPolicy H θ s 0) * (3 : ℝ) ^ (nxtv H s.val 1) ≤ (3 : ℝ) ^ s.val + 2 := by
  have hlt := s.isLt
  by_cases h0 : s.val = 0
  · simp only [nxtv, h0, if_true, pow_zero, pow_one]
    linarith
  · by_cases h1 : s.val = H + 1
    · have hne : H + 1 ≠ 0 := by omega
      simp only [nxtv, h1, hne, if_false, if_true]
      linarith
    · have hs : 0 < s.val ∧ s.val ≤ H := ⟨by omega, by omega⟩
      rw [cp_in H θ s hs]
      set q := θ (⟨s.val - 1, by omega⟩, (0 : Fin 3))
      have hq0 : 0 < q := (hθ _).1
      have hq1 : q < 1 / 4 := (hθ _).2
      obtain ⟨w, hw⟩ : ∃ w, s.val = w + 1 := ⟨s.val - 1, by omega⟩
      have e0 : nxtv H s.val 0 = w + 2 := by unfold nxtv; simp [h0, h1]; omega
      have e1 : nxtv H s.val 1 = w := by unfold nxtv; simp [h0, h1]; omega
      rw [e0, e1, hw, pow_add, pow_add]
      have hp : (0 : ℝ) < 3 ^ w := by positivity
      nlinarith [mul_le_mul_of_nonneg_left (le_of_lt hq1) hp.le]

/-! ### The stochastic matrix and its resolvent -/

noncomputable def Pm (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ :=
  Matrix.of fun s s' => InducedTransition (chainPolicy H θ) (chainP H) s s'

noncomputable def Am (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ :=
  1 - chainGamma H • Pm H θ

noncomputable def Mm (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ :=
  Ring.inverse (Am H θ)

lemma IT_nonneg (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hc : ∀ s, 0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1) (s s' : Fin (H + 2)) :
    0 ≤ InducedTransition (chainPolicy H θ) (chainP H) s s' := by
  rw [IT_eq H _ (cp_sum H θ)]
  have := hc s
  exact add_nonneg (mul_nonneg this.1 (by split_ifs <;> norm_num))
    (mul_nonneg (by linarith [this.2]) (by split_ifs <;> norm_num))

lemma IT_row (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2)) :
    ∑ s', InducedTransition (chainPolicy H θ) (chainP H) s s' = 1 := by
  have := IT_sum H _ (cp_sum H θ) s (fun _ => 1)
  simp only [mul_one] at this
  rw [this]; ring

lemma Am_mulVec (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (x : Fin (H + 2) → ℝ)
    (s : Fin (H + 2)) :
    (Matrix.mulVec (Am H θ) x) s = x s - chainGamma H *
      ∑ s', InducedTransition (chainPolicy H θ) (chainP H) s s' * x s' := by
  have e1 : ∀ i, (Am H θ) s i = (if s = i then 1 else 0) -
      chainGamma H * InducedTransition (chainPolicy H θ) (chainP H) s i := by
    intro i; simp [Am, Pm, Matrix.one_apply]
  simp only [Matrix.mulVec, dotProduct, e1, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc, Finset.mul_sum]

lemma cmp (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hc : ∀ s, 0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1)
    (x : Fin (H + 2) → ℝ) (hx : ∀ s, 0 ≤ (Matrix.mulVec (Am H θ) x) s) : ∀ s, 0 ≤ x s := by
  obtain ⟨hg0, hg1, -⟩ := gamma_facts H hH
  obtain ⟨m, -, hm⟩ := Finset.exists_min_image Finset.univ x Finset.univ_nonempty
  have key : x m ≤ ∑ s', InducedTransition (chainPolicy H θ) (chainP H) m s' * x s' := by
    calc x m = ∑ s', InducedTransition (chainPolicy H θ) (chainP H) m s' * x m := by
          rw [← Finset.sum_mul, IT_row, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun s' _ =>
          mul_le_mul_of_nonneg_left (hm s' (Finset.mem_univ _)) (IT_nonneg H θ hc m s')
  have h := hx m
  rw [Am_mulVec] at h
  have hxm : 0 ≤ x m := by nlinarith [mul_le_mul_of_nonneg_left key hg0]
  intro s
  exact le_trans hxm (hm s (Finset.mem_univ _))

lemma isUnit_Am (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hc : ∀ s, 0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1) : IsUnit (Am H θ) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hz : Matrix.mulVec (Am H θ) (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have h1 := cmp H hH θ hc (x - y) (fun s => by rw [hz]; rfl)
  have h2 := cmp H hH θ hc (y - x) (fun s => by
    rw [← neg_sub, Matrix.mulVec_neg, hz]; simp)
  funext s
  have a := h1 s
  have b := h2 s
  simp only [Pi.sub_apply] at a b
  linarith

lemma Mm_nonneg (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hc : ∀ s, 0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1) (a b : Fin (H + 2)) :
    0 ≤ Mm H θ a b := by
  have hu := isUnit_Am H hH θ hc
  have := cmp H hH θ hc (Matrix.mulVec (Mm H θ) (Pi.single b 1)) (by
    intro s
    rw [Matrix.mulVec_mulVec, Mm, Ring.mul_inverse_cancel _ hu, Matrix.one_mulVec]
    by_cases h : s = b <;> simp [Pi.single_apply, h]) a
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

lemma gamma_mul (H : ℕ) : chainGamma H * ((H : ℝ) + 1) = H := by
  unfold chainGamma; field_simp

lemma Mm_weight (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : θ ∈ Ubox H) (a : Fin (H + 2)) :
    ∑ b, Mm H θ a b * (3 : ℝ) ^ b.val ≤
      ((H : ℝ) + 1) * 3 ^ a.val + 2 * H * ((H : ℝ) + 1) := by
  have hc := cpU H θ hθ
  have hu := isUnit_Am H hH θ hc
  set g : ℕ → ℝ := fun n => ((H : ℝ) + 1) * 3 ^ n + 2 * H * ((H : ℝ) + 1) with hg
  have := cmp H hH θ hc ((fun s => g s.val) - Matrix.mulVec (Mm H θ) (fun s => (3 : ℝ) ^ s.val)) (by
    intro s
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Mm, Ring.mul_inverse_cancel _ hu,
      Matrix.one_mulVec, Pi.sub_apply, Am_mulVec, IT_sum H _ (cp_sum H θ) s g]
    have hp := pot_step' H θ hθ s
    have hcs := hc s
    have hgm := gamma_mul H
    simp only [hg]
    have h3 : chainGamma H * ((H : ℝ) + 1) * 3 ^ s.val = H * 3 ^ s.val := by rw [hgm]
    have h4 : chainGamma H * ((H : ℝ) + 1) * H = H * H := by rw [hgm]
    have h5 := mul_le_mul_of_nonneg_left hp
      (by rw [hgm]; positivity : (0 : ℝ) ≤ chainGamma H * ((H : ℝ) + 1))
    linarith [h3, h4, h5, hgm]) a
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, hg] at this
  linarith

/-! ### The value is a resolvent entry -/

lemma value_eq (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hc : ∀ s, 0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1) :
    chainValue H θ = Mm H θ 0 (Fin.last (H + 1)) := by
  have hv0 : chainValue H θ = ∑' t : ℕ, chainGamma H ^ t *
      OccupationDist (chainPolicy H θ) (chainP H) 0 t (Fin.last (H + 1)) := by
    unfold chainValue PolicyValue
    simp_rw [IR_sum, cp_out H θ (Fin.last (H + 1)) (by simp), mul_one]
  rw [hv0]
  obtain ⟨hg0, hg1, -⟩ := gamma_facts H hH
  have hu := isUnit_Am H hH θ hc
  set γ := chainGamma H with hγ
  set O := OccupationDist (chainPolicy H θ) (chainP H) 0 with hO
  set T := InducedTransition (chainPolicy H θ) (chainP H) with hT
  have hnn := occ_nonneg H _ (cp_sum H θ) hc 0
  have hle1 : ∀ t s, O t s ≤ 1 := by
    intro t s
    have := Finset.single_le_sum (fun s _ => hnn t s) (Finset.mem_univ s)
    rw [occ_mass H _ (cp_sum H θ) 0 t] at this
    exact this
  have hsum : ∀ s, Summable (fun t => γ ^ t * O t s) := by
    intro s
    refine Summable.of_nonneg_of_le (fun t => mul_nonneg (pow_nonneg hg0 t) (hnn t s))
      (fun t => ?_) (summable_geometric_of_lt_one hg0 hg1)
    simpa using mul_le_mul_of_nonneg_left (hle1 t s) (pow_nonneg hg0 t)
  set u : Fin (H + 2) → ℝ := fun s => ∑' t, γ ^ t * O t s with hu_def
  have hrec : ∀ s', u s' = (if s' = 0 then 1 else 0) + γ * ∑ s, u s * T s s' := by
    intro s'
    have h1 : HasSum (fun t => γ ^ (t + 1) * O (t + 1) s') (γ * ∑ s, u s * T s s') := by
      have h := hasSum_sum (s := Finset.univ)
        (fun s _ => ((hsum s).hasSum.mul_right (T s s')).mul_left γ)
      have e1 : (fun t => γ ^ (t + 1) * O (t + 1) s') =
          fun t => ∑ s, γ * (γ ^ t * O t s * T s s') := by
        funext t
        show γ ^ (t + 1) * (∑ s, O t s * T s s') = _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        ring
      rw [e1, Finset.mul_sum]
      exact h
    have h2 : HasSum (fun t => γ ^ t * O t s') (γ * ∑ s, u s * T s s' + γ ^ 0 * O 0 s') :=
      (hasSum_nat_add_iff' 1).mp (by rw [Finset.sum_range_one, add_sub_cancel_right]; exact h1)
    rw [hu_def]
    simp only
    rw [h2.tsum_eq]
    have : O 0 s' = if s' = 0 then 1 else 0 := rfl
    rw [this, pow_zero, one_mul]
    ring
  have hv : Matrix.vecMul u (Am H θ) = Pi.single 0 1 := by
    funext s'
    have e : (Matrix.vecMul u (Am H θ)) s' = u s' - γ * ∑ s, u s * T s s' := by
      have e2 : ∀ i, (Am H θ) i s' = (if i = s' then 1 else 0) - γ * T i s' := by
        intro i; simp [Am, Pm, Matrix.one_apply, hT, hγ]
      simp only [Matrix.vecMul, dotProduct, e2, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one,
        mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, hrec s']
    by_cases h : s' = 0 <;> simp [Pi.single_apply, h]
  have hu2 : u = Matrix.vecMul (Pi.single 0 1) (Mm H θ) := by
    rw [← hv, Matrix.vecMul_vecMul, Mm, Ring.mul_inverse_cancel _ hu, Matrix.vecMul_one]
  have : u (Fin.last (H + 1)) = Mm H θ 0 (Fin.last (H + 1)) := by
    rw [hu2]; simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  exact this

/-! ### Matrices acting as operators on `(Fin (H+2) → ℝ, sup norm)` -/

/-- A matrix as a continuous linear operator on the sup-normed space; the operator norm is
the maximal absolute row sum. -/
noncomputable def L (H : ℕ) (X : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) :
    (Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' X)

lemma L_apply (H : ℕ) (X : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) (x : Fin (H + 2) → ℝ) :
    L H X x = Matrix.mulVec X x := by
  simp [L, Matrix.toLin'_apply]

lemma L_mul (H : ℕ) (X Y : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) :
    L H (X * Y) = L H X * L H Y := by
  ext1 x
  show L H (X * Y) x = L H X (L H Y x)
  rw [L_apply, L_apply, L_apply, Matrix.mulVec_mulVec]

lemma L_one (H : ℕ) : L H 1 = 1 := by
  ext1 x
  rw [L_apply, Matrix.one_mulVec]; rfl

lemma L_add (H : ℕ) (X Y : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) :
    L H (X + Y) = L H X + L H Y := by
  ext1 x
  rw [ContinuousLinearMap.add_apply, L_apply, L_apply, L_apply, Matrix.add_mulVec]

lemma L_sub (H : ℕ) (X Y : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) :
    L H (X - Y) = L H X - L H Y := by
  ext1 x
  rw [ContinuousLinearMap.sub_apply, L_apply, L_apply, L_apply, Matrix.sub_mulVec]

lemma L_smul (H : ℕ) (c : ℝ) (X : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) :
    L H (c • X) = c • L H X := by
  ext1 x
  rw [ContinuousLinearMap.smul_apply, L_apply, L_apply]
  funext a
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

lemma L_norm (H : ℕ) (X : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ a, ∑ b, |X a b| ≤ C) : ‖L H X‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  rw [L_apply]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  rw [Real.norm_eq_abs]
  calc |Matrix.mulVec X x a| = |∑ b, X a b * x b| := rfl
    _ ≤ ∑ b, |X a b * x b| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, |X a b| * ‖x‖ := Finset.sum_le_sum fun b _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_le_pi_norm x b) (abs_nonneg _)
    _ = (∑ b, |X a b|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (h a) (norm_nonneg _)

/-! ### Conjugation by `diag(3^s)` -/

noncomputable def Wm (H : ℕ) : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ :=
  Matrix.diagonal fun s => (3 : ℝ) ^ s.val

noncomputable def Wi (H : ℕ) : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ :=
  Matrix.diagonal fun s => ((3 : ℝ) ^ s.val)⁻¹

lemma W_Wi (H : ℕ) : Wm H * Wi H = 1 := by
  rw [Wm, Wi, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext s
  exact mul_inv_cancel₀ (by positivity)

lemma LW_LWi (H : ℕ) : L H (Wm H) * L H (Wi H) = 1 := by
  rw [← L_mul, W_Wi, L_one]

lemma conj_entry (H : ℕ) (X : Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ) (a b : Fin (H + 2)) :
    (Wi H * X * Wm H) a b = ((3 : ℝ) ^ a.val)⁻¹ * X a b * 3 ^ b.val := by
  simp [Wi, Wm, Matrix.mul_diagonal, Matrix.diagonal_mul]

lemma conj_mul (H : ℕ) (X Y : (Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) :
    (L H (Wi H) * X * L H (Wm H)) * (L H (Wi H) * Y * L H (Wm H)) =
      L H (Wi H) * (X * Y) * L H (Wm H) := by
  calc (L H (Wi H) * X * L H (Wm H)) * (L H (Wi H) * Y * L H (Wm H))
      = L H (Wi H) * X * (L H (Wm H) * L H (Wi H)) * Y * L H (Wm H) := by
        simp only [mul_assoc]
    _ = _ := by rw [LW_LWi, mul_one]; simp only [mul_assoc]

noncomputable def Cj (H : ℕ) :
    ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) →L[ℝ]
      ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) :=
  ContinuousLinearMap.mulLeftRight ℝ _ (L H (Wi H)) (L H (Wm H))

lemma Cj_apply (H : ℕ) (X : (Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) :
    Cj H X = L H (Wi H) * X * L H (Wm H) := rfl

/-! ### The operator family -/

noncomputable def Aop (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    (Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ) :=
  L H (Am H θ)

noncomputable def Gop (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    (Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ) :=
  Cj H (Ring.inverse (Aop H θ))

/-- The explicit unit `Aop θ` with inverse `L (Mm θ)`. -/
noncomputable def uA (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (hu : IsUnit (Am H θ)) :
    ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ))ˣ :=
  ⟨Aop H θ, L H (Mm H θ),
    by rw [Aop, ← L_mul, Mm, Ring.mul_inverse_cancel _ hu, L_one],
    by rw [Aop, ← L_mul, Mm, Ring.inverse_mul_cancel _ hu, L_one]⟩

lemma inv_Aop (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (hu : IsUnit (Am H θ)) :
    Ring.inverse (Aop H θ) = L H (Mm H θ) :=
  Ring.inverse_unit (uA H θ hu)

lemma Gop_eq (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (hu : IsUnit (Am H θ)) :
    Gop H θ = L H (Wi H * Mm H θ * Wm H) := by
  rw [Gop, inv_Aop H θ hu, Cj_apply, L_mul, L_mul]

noncomputable def Kc (H : ℕ) : ℝ := ((H : ℝ) + 1) * (2 * H + 1)

lemma Gop_norm (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : θ ∈ Ubox H) : ‖Gop H θ‖ ≤ Kc H := by
  have hc := cpU H θ hθ
  rw [Gop_eq H θ (isUnit_Am H hH θ hc)]
  apply L_norm _ _ _ (by unfold Kc; positivity)
  intro a
  have hw := Mm_weight H hH θ hθ a
  have e : ∀ b, |(Wi H * Mm H θ * Wm H) a b| =
      ((3 : ℝ) ^ a.val)⁻¹ * (Mm H θ a b * 3 ^ b.val) := by
    intro b
    rw [conj_entry, abs_of_nonneg (by
      have := Mm_nonneg H hH θ hc a b; positivity)]
    ring
  simp_rw [e]
  rw [← Finset.mul_sum]
  have h3 : (0 : ℝ) < 3 ^ a.val := by positivity
  have h3' : ((3 : ℝ) ^ a.val)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hH0 : (0 : ℝ) ≤ H := by positivity
  calc ((3 : ℝ) ^ a.val)⁻¹ * ∑ b, Mm H θ a b * 3 ^ b.val
      ≤ ((3 : ℝ) ^ a.val)⁻¹ * (((H : ℝ) + 1) * 3 ^ a.val + 2 * H * ((H : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
    _ = ((H : ℝ) + 1) + ((3 : ℝ) ^ a.val)⁻¹ * (2 * H * ((H : ℝ) + 1)) := by
        field_simp
    _ ≤ ((H : ℝ) + 1) + 1 * (2 * H * ((H : ℝ) + 1)) := by
        gcongr
    _ = Kc H := by unfold Kc; ring

/-! ### The affine dependence on θ -/

noncomputable def lp (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2)) : ℝ :=
  if hs : 0 < s.val ∧ s.val ≤ H then θ (⟨s.val - 1, by omega⟩, 0) else 0

lemma lp_add (H : ℕ) (θ θ' : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2)) :
    lp H (θ + θ') s = lp H θ s + lp H θ' s := by
  unfold lp; split_ifs <;> simp

lemma lp_smul (H : ℕ) (c : ℝ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2)) :
    lp H (c • θ) s = c * lp H θ s := by
  unfold lp; split_ifs <;> simp

lemma lp_le (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2)) :
    |lp H θ s| ≤ ‖θ‖ := by
  unfold lp
  split_ifs
  · rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le θ _
  · simp

lemma cp_split (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s : Fin (H + 2)) :
    chainPolicy H θ s 0 = chainPolicy H 0 s 0 + lp H θ s := by
  by_cases hs : 0 < s.val ∧ s.val ≤ H
  · rw [cp_in H θ s hs, cp_in H 0 s hs]; simp [lp, hs]
  · rw [cp_out H θ s hs, cp_out H 0 s hs]
    unfold lp
    rw [dif_neg hs]; ring

/-- The (matrix) direction of the transition matrix in parameter space. -/
noncomputable def dPl (H : ℕ) :
    EuclideanSpace ℝ (Fin H × Fin 3) →ₗ[ℝ] Matrix (Fin (H + 2)) (Fin (H + 2)) ℝ where
  toFun θ := Matrix.of fun s s' => lp H θ s *
    ((if s'.val = nxtv H s.val 0 then (1 : ℝ) else 0) - (if s'.val = nxtv H s.val 1 then 1 else 0))
  map_add' θ θ' := by
    ext s s'
    simp only [Matrix.of_apply, Matrix.add_apply, lp_add]
    ring
  map_smul' c θ := by
    ext s s'
    simp only [Matrix.of_apply, Matrix.smul_apply, lp_smul, RingHom.id_apply, smul_eq_mul]
    ring

lemma dPl_apply (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (s s' : Fin (H + 2)) :
    dPl H θ s s' = lp H θ s *
      ((if s'.val = nxtv H s.val 0 then (1 : ℝ) else 0) -
        (if s'.val = nxtv H s.val 1 then 1 else 0)) := rfl

lemma Am_affine (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    Am H θ = Am H 0 - chainGamma H • dPl H θ := by
  ext s s'
  simp only [Am, Pm, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, dPl_apply,
    smul_eq_mul]
  rw [IT_eq H _ (cp_sum H θ), IT_eq H _ (cp_sum H 0), cp_split H θ s]
  ring

/-- The operator direction, as a continuous linear map of the parameter. -/
noncomputable def dPop (H : ℕ) :
    EuclideanSpace ℝ (Fin H × Fin 3) →L[ℝ] ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun θ => L H (dPl H θ)
      map_add' := fun θ θ' => by rw [map_add, L_add]
      map_smul' := fun c θ => by rw [map_smul, L_smul]; rfl }

lemma dPop_apply (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    dPop H θ = L H (dPl H θ) := rfl

lemma Aop_affine (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    Aop H θ = Aop H 0 + (-(chainGamma H • dPop H)) θ := by
  rw [Aop, Aop, Am_affine H θ, L_sub, L_smul, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smul_apply, dPop_apply, sub_eq_add_neg]

lemma hasFDerivAt_Aop (H : ℕ) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) :
    HasFDerivAt (Aop H) (-(chainGamma H • dPop H)) θ := by
  have e : Aop H = fun θ => Aop H 0 + (-(chainGamma H • dPop H)) θ := funext (Aop_affine H)
  rw [e]
  exact (ContinuousLinearMap.hasFDerivAt _).const_add _

lemma contDiff_Aop (H : ℕ) : ContDiff ℝ ⊤ (Aop H) := by
  have e : Aop H = fun θ => Aop H 0 + (-(chainGamma H • dPop H)) θ := funext (Aop_affine H)
  rw [e]
  exact contDiff_const.add (ContinuousLinearMap.contDiff _)

/-! ### The conjugated derivative direction and the bilinear form -/

noncomputable def Dc (H : ℕ) :
    EuclideanSpace ℝ (Fin H × Fin 3) →L[ℝ] ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) :=
  chainGamma H • (Cj H).comp (dPop H)

lemma Dc_apply (H : ℕ) (h : EuclideanSpace ℝ (Fin H × Fin 3)) :
    Dc H h = chainGamma H • (L H (Wi H) * dPop H h * L H (Wm H)) := rfl

lemma Dc_eq (H : ℕ) (h : EuclideanSpace ℝ (Fin H × Fin 3)) :
    Dc H h = L H (chainGamma H • (Wi H * dPl H h * Wm H)) := by
  rw [Dc_apply, dPop_apply, L_smul, L_mul, L_mul]

lemma sum_ind_abs (H : ℕ) (s : Fin (H + 2)) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) :
    ∑ s' : Fin (H + 2), |(if s'.val = nxtv H s.val 0 then (1 : ℝ) else 0) -
        (if s'.val = nxtv H s.val 1 then 1 else 0)| * g s'.val ≤
      g (nxtv H s.val 0) + g (nxtv H s.val 1) := by
  have hlt := s.isLt
  calc _ ≤ ∑ s' : Fin (H + 2), ((if s'.val = nxtv H s.val 0 then (1 : ℝ) else 0) * g s'.val +
        (if s'.val = nxtv H s.val 1 then (1 : ℝ) else 0) * g s'.val) := by
        refine Finset.sum_le_sum fun s' _ => ?_
        have := hg s'.val
        split_ifs <;> norm_num <;> linarith
    _ = _ := by
        rw [Finset.sum_add_distrib, sum_ind H _ (nxtv_lt H _ _ hlt),
          sum_ind H _ (nxtv_lt H _ _ hlt)]

lemma Dc_norm (H : ℕ) (hH : 1 ≤ H) : ‖Dc H‖ ≤ 10 / 3 := by
  obtain ⟨hg0, hg1, -⟩ := gamma_facts H hH
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun h => ?_
  rw [Dc_eq]
  apply L_norm _ _ _ (by positivity)
  intro a
  have e : ∀ b, |(chainGamma H • (Wi H * dPl H h * Wm H)) a b| =
      chainGamma H * ((3 : ℝ) ^ a.val)⁻¹ * |lp H h a| *
        (|(if b.val = nxtv H a.val 0 then (1 : ℝ) else 0) -
          (if b.val = nxtv H a.val 1 then 1 else 0)| * 3 ^ b.val) := by
    intro b
    rw [Matrix.smul_apply, conj_entry, dPl_apply, smul_eq_mul, abs_mul, abs_mul, abs_mul,
      abs_mul, abs_of_nonneg hg0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((3 : ℝ) ^ a.val)⁻¹),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ b.val)]
    ring
  simp_rw [e]
  rw [← Finset.mul_sum]
  have hs := sum_ind_abs H a (fun n => (3 : ℝ) ^ n) (fun n => by positivity)
  have hl := lp_le H h a
  by_cases hin : 0 < a.val ∧ a.val ≤ H
  · obtain ⟨w, hw⟩ : ∃ w, a.val = w + 1 := ⟨a.val - 1, by omega⟩
    have e0 : nxtv H a.val 0 = w + 2 := by unfold nxtv; simp [hw]; omega
    have e1 : nxtv H a.val 1 = w := by unfold nxtv; simp [hw]; omega
    rw [e0, e1] at hs ⊢
    have hk : ((3 : ℝ) ^ a.val)⁻¹ * ((3 : ℝ) ^ (w + 2) + 3 ^ w) = 10 / 3 := by
      rw [hw]; field_simp; ring
    calc chainGamma H * ((3 : ℝ) ^ a.val)⁻¹ * |lp H h a| * _
        ≤ 1 * ((3 : ℝ) ^ a.val)⁻¹ * ‖h‖ * ((3 : ℝ) ^ (w + 2) + 3 ^ w) := by
          gcongr
      _ = 10 / 3 * ‖h‖ := by rw [← hk]; ring
  · have : lp H h a = 0 := by unfold lp; rw [dif_neg hin]
    rw [this]; simp

/-! ### Derivative of the conjugated resolvent -/

lemma fderiv_Gop (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hc : ∀ s, 0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1)
    (h : EuclideanSpace ℝ (Fin H × Fin 3)) :
    fderiv ℝ (Gop H) θ h = Gop H θ * (Dc H h * Gop H θ) := by
  have hu := isUnit_Am H hH θ hc
  have h1 : HasFDerivAt (𝕜 := ℝ) Ring.inverse
      (-(ContinuousLinearMap.mulLeftRight ℝ ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ))
        (L H (Mm H θ)) (L H (Mm H θ)))) (Aop H θ) :=
    hasFDerivAt_ringInverse (uA H θ hu)
  have h3 : HasFDerivAt (Gop H) ((Cj H).comp
      ((-(ContinuousLinearMap.mulLeftRight ℝ ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ))
        (L H (Mm H θ)) (L H (Mm H θ)))).comp
        (-(chainGamma H • dPop H)))) θ :=
    (Cj H).hasFDerivAt.comp θ (h1.comp θ (hasFDerivAt_Aop H θ))
  have hG : Gop H θ = L H (Wi H) * L H (Mm H θ) * L H (Wm H) := by
    rw [Gop, inv_Aop H θ hu, Cj_apply]
  rw [h3.fderiv, hG]
  ext1 x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight_apply,
    Dc_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, Cj_apply,
    mul_apply_eq_comp, map_neg, map_smul, neg_neg]
  have hWW : ∀ v, L H (Wm H) (L H (Wi H) v) = v := fun v => by
    rw [← mul_apply_eq_comp, LW_LWi]; rfl
  simp only [hWW, smul_neg, neg_neg]

lemma contDiffAt_Gop (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hc : ∀ s, 0 ≤ chainPolicy H θ s 0 ∧ chainPolicy H θ s 0 ≤ 1) :
    ContDiffAt ℝ ⊤ (Gop H) θ := by
  have hu := isUnit_Am H hH θ hc
  have h1 : ContDiffAt ℝ ⊤ (Ring.inverse :
      ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) → _) (Aop H θ) :=
    contDiffAt_ringInverse (𝕜 := ℝ) (uA H θ hu)
  exact (Cj H).contDiff.contDiffAt.comp θ (h1.comp θ (contDiff_Aop H).contDiffAt)

/-! ### The derivative bound by induction -/

lemma deriv_bound (H : ℕ) (hH : 1 ≤ H) : ∀ k : ℕ, ∀ θ ∈ Ubox H,
    ‖iteratedFDerivWithin ℝ k (Gop H) (Ubox H) θ‖ ≤
      (k.factorial : ℝ) * (10 / 3 : ℝ) ^ k * Kc H ^ (k + 1) := by
  have hUo := isOpen_Ubox H
  have hs := hUo.uniqueDiffOn (𝕜 := ℝ)
  have hGcd : ContDiffOn ℝ ⊤ (Gop H) (Ubox H) := fun y hy =>
    (contDiffAt_Gop H hH y (cpU H y hy)).contDiffWithinAt
  have hF : ContDiffOn ℝ ⊤ (fun y => fderivWithin ℝ (Gop H) (Ubox H) y) (Ubox H) :=
    hGcd.fderivWithin hs le_top
  have hK : 0 ≤ Kc H := by unfold Kc; positivity
  have hDc := Dc_norm H hH
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro θ hθ
    rcases k with _ | k
    · simp only [norm_iteratedFDerivWithin_zero, Nat.factorial_zero, Nat.cast_one, pow_zero,
        one_mul, zero_add, pow_one]
      exact Gop_norm H hH θ hθ
    · refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
      rw [iteratedFDerivWithin_succ_apply_right hs hθ m]
      set h := m (Fin.last k) with hh
      have hEq : Set.EqOn
          (⇑(ContinuousLinearMap.apply ℝ ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) h) ∘
            (fun y => fderivWithin ℝ (Gop H) (Ubox H) y))
          (fun y => Gop H y * (Dc H h * Gop H y)) (Ubox H) := by
        intro y hy
        simp only [Function.comp_apply, ContinuousLinearMap.apply_apply]
        rw [fderivWithin_of_isOpen hUo hy]
        exact fderiv_Gop H hH y (cpU H y hy) h
      have hcomp := (ContinuousLinearMap.apply ℝ
        ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) h).iteratedFDerivWithin_comp_left
          (hF θ hθ) hs hθ (i := k) le_top
      have e1 : iteratedFDerivWithin ℝ k (fun y => fderivWithin ℝ (Gop H) (Ubox H) y) (Ubox H) θ
            (Fin.init m) h =
          iteratedFDerivWithin ℝ k (fun y => Gop H y * (Dc H h * Gop H y)) (Ubox H) θ
            (Fin.init m) := by
        rw [← iteratedFDerivWithin_congr hEq hθ k, hcomp]
        rfl
      rw [e1]
      have hD : ∀ j, ‖iteratedFDerivWithin ℝ j (fun y => Dc H h * Gop H y) (Ubox H) θ‖ ≤
          ‖Dc H h‖ * ‖iteratedFDerivWithin ℝ j (Gop H) (Ubox H) θ‖ := fun j =>
        le_trans ((ContinuousLinearMap.mul ℝ ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ))
          (Dc H h)).norm_iteratedFDerivWithin_comp_left (hGcd θ hθ) hs hθ le_top)
          (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_apply_le ℝ _ _)
            (norm_nonneg _))
      have hmul := norm_iteratedFDerivWithin_mul_le (f := Gop H)
        (g := fun y => Dc H h * Gop H y) hGcd (contDiffOn_const.mul hGcd) hs hθ (n := k) le_top
      have hterm : ∀ i ∈ Finset.range (k + 1),
          (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (Gop H) (Ubox H) θ‖ *
            ‖iteratedFDerivWithin ℝ (k - i) (fun y => Dc H h * Gop H y) (Ubox H) θ‖ ≤
          ‖Dc H h‖ * ((k.factorial : ℝ) * (10 / 3 : ℝ) ^ k * Kc H ^ (k + 2)) := by
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have b1 := ih i (by omega) θ hθ
        have b2 := ih (k - i) (by omega) θ hθ
        have b3 := hD (k - i)
        have e1 : i + (k - i) = k := by omega
        have e2 : i + 1 + (k - i + 1) = k + 2 := by omega
        calc (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i (Gop H) (Ubox H) θ‖ *
              ‖iteratedFDerivWithin ℝ (k - i) (fun y => Dc H h * Gop H y) (Ubox H) θ‖
            ≤ (k.choose i : ℝ) * ((i.factorial : ℝ) * (10 / 3 : ℝ) ^ i * Kc H ^ (i + 1)) *
              (‖Dc H h‖ * (((k - i).factorial : ℝ) * (10 / 3 : ℝ) ^ (k - i) *
                Kc H ^ (k - i + 1))) := by
              gcongr
              exact b3.trans (mul_le_mul_of_nonneg_left b2 (norm_nonneg _))
          _ = ‖Dc H h‖ * (((k.choose i * i.factorial * (k - i).factorial : ℕ) : ℝ) *
              ((10 / 3 : ℝ) ^ i * (10 / 3 : ℝ) ^ (k - i)) *
              (Kc H ^ (i + 1) * Kc H ^ (k - i + 1))) := by
              push_cast; ring
          _ = _ := by
              rw [Nat.choose_mul_factorial_mul_factorial hik, ← pow_add, ← pow_add, e1, e2]
      have hsum := Finset.sum_le_sum hterm
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      have hDh : ‖Dc H h‖ ≤ 10 / 3 * ‖h‖ :=
        ((Dc H).le_opNorm h).trans (mul_le_mul_of_nonneg_right hDc (norm_nonneg _))
      have hbound : ‖iteratedFDerivWithin ℝ k (fun y => Gop H y * (Dc H h * Gop H y))
          (Ubox H) θ‖ ≤ ((k + 1).factorial : ℝ) * (10 / 3 : ℝ) ^ (k + 1) * Kc H ^ (k + 1 + 1) *
            ‖h‖ := by
        refine hmul.trans (hsum.trans ?_)
        have hX : 0 ≤ (k.factorial : ℝ) * (10 / 3 : ℝ) ^ k * Kc H ^ (k + 2) := by positivity
        calc ((k + 1 : ℕ) : ℝ) * (‖Dc H h‖ * ((k.factorial : ℝ) * (10 / 3 : ℝ) ^ k *
              Kc H ^ (k + 2)))
            ≤ ((k + 1 : ℕ) : ℝ) * ((10 / 3 * ‖h‖) * ((k.factorial : ℝ) * (10 / 3 : ℝ) ^ k *
              Kc H ^ (k + 2))) := by gcongr
          _ = _ := by rw [Nat.factorial_succ]; push_cast; ring
      calc ‖iteratedFDerivWithin ℝ k (fun y => Gop H y * (Dc H h * Gop H y)) (Ubox H) θ
            (Fin.init m)‖
          ≤ ‖iteratedFDerivWithin ℝ k (fun y => Gop H y * (Dc H h * Gop H y)) (Ubox H) θ‖ *
              ∏ i : Fin k, ‖Fin.init m i‖ := ContinuousMultilinearMap.le_opNorm _ _
        _ ≤ (((k + 1).factorial : ℝ) * (10 / 3 : ℝ) ^ (k + 1) * Kc H ^ (k + 1 + 1) * ‖h‖) *
              ∏ i : Fin k, ‖Fin.init m i‖ :=
            mul_le_mul_of_nonneg_right hbound (Finset.prod_nonneg fun i _ => norm_nonneg _)
        _ = ((k + 1).factorial : ℝ) * (10 / 3 : ℝ) ^ (k + 1) * Kc H ^ (k + 1 + 1) *
              ∏ i, ‖m i‖ := by
            rw [Fin.prod_univ_castSucc, hh]
            simp only [Fin.init]
            ring

/-! ### Assembly of conjunct I -/

noncomputable def ent (H : ℕ) :
    ((Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) →L[ℝ] ℝ :=
  ((3 : ℝ) ^ (H + 1))⁻¹ • ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (H + 2) => ℝ)
    (0 : Fin (H + 2))).comp
      (ContinuousLinearMap.apply ℝ (Fin (H + 2) → ℝ) (Pi.single (Fin.last (H + 1)) 1)))

lemma ent_apply (H : ℕ) (T : (Fin (H + 2) → ℝ) →L[ℝ] (Fin (H + 2) → ℝ)) :
    ent H T = ((3 : ℝ) ^ (H + 1))⁻¹ * T (Pi.single (Fin.last (H + 1)) 1) 0 := rfl

lemma ent_norm (H : ℕ) : ‖ent H‖ ≤ ((3 : ℝ) ^ (H + 1))⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun T => ?_
  rw [ent_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h1 : ‖(Pi.single (Fin.last (H + 1)) (1 : ℝ) : Fin (H + 2) → ℝ)‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun s => ?_
    by_cases h : s = Fin.last (H + 1) <;> simp [Pi.single_apply, h]
  calc |T (Pi.single (Fin.last (H + 1)) 1) 0|
      ≤ ‖T (Pi.single (Fin.last (H + 1)) 1)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_le_pi_norm _ 0
    _ ≤ ‖T‖ * ‖(Pi.single (Fin.last (H + 1)) (1 : ℝ) : Fin (H + 2) → ℝ)‖ := T.le_opNorm _
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖T‖ := mul_one _

lemma conj1 (H : ℕ) (hH : 1 ≤ H) (θ : EuclideanSpace ℝ (Fin H × Fin 3)) (hθ : θ ∈ Ubox H)
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k (chainValue H) θ‖ ≤
      ((3 : ℝ) ^ (H + 1))⁻¹ * ((k.factorial : ℝ) * (10 / 3 : ℝ) ^ k * Kc H ^ (k + 1)) := by
  have hUo := isOpen_Ubox H
  have hev : chainValue H =ᶠ[nhds θ] (ent H) ∘ (Gop H) := by
    filter_upwards [hUo.mem_nhds hθ] with y hy
    have hc := cpU H y hy
    rw [value_eq H hH y hc, Function.comp_apply, ent_apply,
      Gop_eq H y (isUnit_Am H hH y hc), L_apply]
    have e : Matrix.mulVec (Wi H * Mm H y * Wm H) (Pi.single (Fin.last (H + 1)) 1) 0 =
        (Wi H * Mm H y * Wm H) 0 (Fin.last (H + 1)) := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [e, conj_entry]
    simp only [Fin.val_zero, Fin.val_last, pow_zero, inv_one, one_mul]
    field_simp
  rw [(hev.iteratedFDeriv ℝ k).eq_of_nhds, ← iteratedFDerivWithin_of_isOpen k hUo hθ]
  refine le_trans ((ent H).norm_iteratedFDerivWithin_comp_left
    (contDiffAt_Gop H hH θ (cpU H θ hθ)).contDiffWithinAt hUo.uniqueDiffOn hθ le_top) ?_
  exact mul_le_mul (ent_norm H) (deriv_bound H hH k θ hθ) (norm_nonneg _) (by positivity)

/-! ### The final arithmetic -/

lemma arith (H : ℕ) (hH : 1 ≤ H) (k : ℕ)
    (hk : (k : ℝ) ≤ (H : ℝ) / (40 * Real.log (2 * H)) - 1) :
    ((3 : ℝ) ^ (H + 1))⁻¹ * ((k.factorial : ℝ) * (10 / 3 : ℝ) ^ k * Kc H ^ (k + 1)) ≤
      (1 / 3 : ℝ) ^ ((H : ℝ) / 4) := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set L := Real.log (2 * H) with hL
  have hl2 := Real.log_two_gt_d9
  have hL0 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hLpos : 0 < L := by linarith
  have hk1 : ((k : ℝ) + 1) * (40 * L) ≤ H := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 40 * L)).mp
      (by linarith : (k : ℝ) + 1 ≤ H / (40 * L))
    linarith
  have hkH : (k : ℝ) + 1 ≤ H := by nlinarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hfac : (k.factorial : ℝ) ≤ (2 * H) ^ k := by
    have h : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by exact_mod_cast Nat.factorial_le_pow k
    exact h.trans (pow_le_pow_left₀ hk0 (by linarith) k)
  have hc : (10 / 3 : ℝ) ≤ (2 * H) ^ 2 := by nlinarith
  have hK : Kc H ≤ (2 * H) ^ 3 := by unfold Kc; nlinarith
  have hK0 : 0 ≤ Kc H := by unfold Kc; positivity
  have hX : (k.factorial : ℝ) * (10 / 3 : ℝ) ^ k * Kc H ^ (k + 1) ≤
      (2 * (H : ℝ)) ^ (6 * (k + 1)) := by
    calc (k.factorial : ℝ) * (10 / 3 : ℝ) ^ k * Kc H ^ (k + 1)
        ≤ (2 * (H : ℝ)) ^ k * ((2 * H) ^ 2) ^ k * ((2 * H) ^ 3) ^ (k + 1) := by
          gcongr
      _ = (2 * (H : ℝ)) ^ (6 * (k + 1) - 3) := by
          rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; omega
      _ ≤ (2 * (H : ℝ)) ^ (6 * (k + 1)) :=
          pow_le_pow_right₀ (by linarith) (by omega)
  have hexp : (2 * (H : ℝ)) ^ (6 * (k + 1)) = Real.exp (6 * ((k : ℝ) + 1) * L) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 * H), ← Real.exp_nat_mul, ← hL]
    push_cast; ring_nf
  have h3 : ((3 : ℝ) ^ (H + 1))⁻¹ = Real.exp (-(((H : ℝ) + 1) * Real.log 3)) := by
    rw [Real.exp_neg, ← Real.exp_log (by norm_num : (0 : ℝ) < 3), ← Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    push_cast; ring_nf
  have hr : (1 / 3 : ℝ) ^ ((H : ℝ) / 4) = Real.exp (-(Real.log 3) * ((H : ℝ) / 4)) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]
  have hl3 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  calc ((3 : ℝ) ^ (H + 1))⁻¹ * ((k.factorial : ℝ) * (10 / 3 : ℝ) ^ k * Kc H ^ (k + 1))
      ≤ ((3 : ℝ) ^ (H + 1))⁻¹ * Real.exp (6 * ((k : ℝ) + 1) * L) := by
        rw [← hexp]; exact mul_le_mul_of_nonneg_left hX (by positivity)
    _ = Real.exp (-(((H : ℝ) + 1) * Real.log 3) + 6 * ((k : ℝ) + 1) * L) := by
        rw [h3, Real.exp_add]
    _ ≤ Real.exp (-(Real.log 3) * ((H : ℝ) / 4)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left (le_trans (le_of_lt hl2) hl3)
          (by positivity : (0 : ℝ) ≤ H)]
    _ = _ := hr.symm

end P0226

open PolicyGradTheory.ChainLB FoundationsML.ReinforcementLearning in
theorem solution (H : ℕ) (hH : 1 ≤ H)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4)
    (πstar : Fin (H + 2) → Fin 4 → ℝ) (hπstar : IsPolicy πstar)
    (hopt : IsOptimalPolicy πstar (chainP H) (chainR H) (chainGamma H)) :
    (∀ k : ℕ, (k : ℝ) ≤ (H : ℝ) / (40 * Real.log (2 * H)) - 1 →
      ‖iteratedFDeriv ℝ k (chainValue H) θ‖ ≤ (1 / 3 : ℝ) ^ ((H : ℝ) / 4)) ∧
    (H + 1 : ℝ) / 8 - (H + 1 : ℝ) ^ 2 / (3 : ℝ) ^ H ≤
      PolicyValue πstar (chainP H) (chainR H) (chainGamma H) 0 - chainValue H θ := by
  refine ⟨fun k hk => ?_, ?_⟩
  · have hU : θ ∈ P0226.Ubox H := fun i => ⟨(hθ i 0).1, hθ1 i⟩
    exact (P0226.conj1 H hH θ hU k).trans (P0226.arith H hH k hk)
  · have h1 := le_trans (P325c.part1 H hH) (hopt _ (P325c.fwd_policy H) 0)
    have h2 := P325c.part2 H hH θ hθ hθ1
    linarith
