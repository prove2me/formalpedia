-- Prove2me | solution 1 for PolicyGradTheory.ChainLB.chain_suboptimality
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:32:39.464388+00:00
-- url     : https://prove2.me/submissions/0d16157d-1afc-4829-83d7-7fdb1e3ceb52

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

open PolicyGradTheory.ChainLB FoundationsML.ReinforcementLearning in
theorem solution (H : ℕ) (hH : 1 ≤ H)
    (θ : EuclideanSpace ℝ (Fin H × Fin 3))
    (hθ : ∀ i j, 0 < θ (i, j) ∧ θ (i, j) < 1)
    (hθ1 : ∀ i, θ (i, (0 : Fin 3)) < 1 / 4)
    (πstar : Fin (H + 2) → Fin 4 → ℝ) (hπstar : IsPolicy πstar)
    (hopt : IsOptimalPolicy πstar (chainP H) (chainR H) (chainGamma H)) :
    (H + 1 : ℝ) / 8 ≤ PolicyValue πstar (chainP H) (chainR H) (chainGamma H) 0 ∧
    chainValue H θ ≤ (H + 1 : ℝ) ^ 2 / (3 : ℝ) ^ H := by
  exact ⟨le_trans (P325c.part1 H hH) (hopt _ (P325c.fwd_policy H) 0),
    P325c.part2 H hH θ hθ hθ1⟩
