-- Prove2me | solution 1 for VehicleSharePricing.Static.eq_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:00:30.038444+00:00
-- url     : https://prove2.me/submissions/aff0f7a3-8e99-46fd-bd85-a5e8dd26228f

import Mathlib
import Definitions.Def_VehicleSharePricing_Static_Model
import Definitions.Def_VehicleSharePricing_Static_Availability

set_option autoImplicit false

section PFCore
open Finset

def pfStates (S T : Type*) [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T] (K : ℕ) :
    Finset (S ⊕ T → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (K + 1)).filter fun x => ∑ k, x k = K

noncomputable def pfW {S T : Type*} [Fintype S] [Fintype T] (a : S → ℝ) (b : T → ℝ)
    (x : S ⊕ T → ℕ) : ℝ :=
  (∏ s, a s ^ x (Sum.inl s)) * ∏ t, b t ^ x (Sum.inr t) / ((x (Sum.inr t)).factorial : ℝ)

noncomputable def pfG {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (a : S → ℝ) (b : T → ℝ) (K : ℕ) : ℝ :=
  ∑ x ∈ pfStates S T K, pfW a b x

noncomputable def pfAv {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (a : S → ℝ) (b : T → ℝ) (K : ℕ) (s : S) : ℝ :=
  (∑ x ∈ (pfStates S T K).filter (fun x => 1 ≤ x (Sum.inl s)), pfW a b x) / pfG a b K

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

def pfE (s : S) : S ⊕ T → ℕ := fun k => if k = Sum.inl s then 1 else 0

lemma pfE_apply (s : S) (k : S ⊕ T) : (pfE s : S ⊕ T → ℕ) k = if k = Sum.inl s then 1 else 0 := rfl

lemma pfW_nonneg (a : S → ℝ) (b : T → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ t, 0 ≤ b t)
    (x : S ⊕ T → ℕ) : 0 ≤ pfW a b x := by
  unfold pfW
  refine mul_nonneg (Finset.prod_nonneg fun s _ => pow_nonneg (ha s) _)
    (Finset.prod_nonneg fun t _ => ?_)
  exact div_nonneg (pow_nonneg (hb t) _) (Nat.cast_nonneg _)

lemma pfW_add_single (a : S → ℝ) (b : T → ℝ) (s : S) (y : S ⊕ T → ℕ) :
    pfW a b (y + (pfE s : S ⊕ T → ℕ)) = a s * pfW a b y := by
  unfold pfW
  have h1 : (∏ s', a s' ^ (y + (pfE s : S ⊕ T → ℕ)) (Sum.inl s')) =
      a s * ∏ s', a s' ^ y (Sum.inl s') := by
    have : ∀ s', a s' ^ (y + (pfE s : S ⊕ T → ℕ)) (Sum.inl s') =
        a s' ^ y (Sum.inl s') * (if s' = s then a s else 1) := by
      intro s'
      by_cases h : s' = s
      · subst h; simp [pfE_apply, pow_succ]
      · have : (Sum.inl s' : S ⊕ T) ≠ Sum.inl s := fun e => h (Sum.inl_injective e)
        simp [pfE_apply, this, h]
    rw [Finset.prod_congr rfl (fun s' _ => this s'), Finset.prod_mul_distrib]
    simp [mul_comm]
  have h2 : (∏ t, b t ^ (y + (pfE s : S ⊕ T → ℕ)) (Sum.inr t) /
      (((y + (pfE s : S ⊕ T → ℕ)) (Sum.inr t)).factorial : ℝ)) =
      ∏ t, b t ^ y (Sum.inr t) / ((y (Sum.inr t)).factorial : ℝ) := by
    apply Finset.prod_congr rfl
    intro t _
    simp [pfE_apply]
  rw [h1, h2]; ring

lemma pfE_sum (s : S) : ∑ k, (pfE s : S ⊕ T → ℕ) k = 1 := by
  simp [pfE_apply]

lemma pf_decomp (s : S) (x : S ⊕ T → ℕ) (hx : 1 ≤ x (Sum.inl s)) :
    x = (x - (pfE s : S ⊕ T → ℕ)) + (pfE s : S ⊕ T → ℕ) := by
  funext k
  by_cases hk : k = Sum.inl s
  · subst hk; simp [pfE_apply]; omega
  · simp [pfE_apply, hk]

lemma pf_shift (a : S → ℝ) (b : T → ℝ) (K : ℕ) (s : S) :
    ∑ x ∈ (pfStates S T (K + 1)).filter (fun x => 1 ≤ x (Sum.inl s)), pfW a b x =
      a s * pfG a b K := by
  unfold pfG
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun x => x - (pfE s : S ⊕ T → ℕ))
    (fun y => y + (pfE s : S ⊕ T → ℕ)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [pfStates, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hx ⊢
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    have hsum : ∑ k, (x - (pfE s : S ⊕ T → ℕ)) k + 1 = ∑ k, x k := by
      conv_rhs => rw [pf_decomp s x h3]
      simp only [Pi.add_apply, Finset.sum_add_distrib, pfE_sum]
    have hK : ∑ k, (x - (pfE s : S ⊕ T → ℕ)) k = K := by omega
    refine ⟨fun k => ?_, hK⟩
    have : (x - (pfE s : S ⊕ T → ℕ)) k ≤ ∑ j, (x - (pfE s : S ⊕ T → ℕ)) j :=
      Finset.single_le_sum (f := fun j => (x - (pfE s : S ⊕ T → ℕ)) j) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    omega
  · intro y hy
    simp only [pfStates, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hy ⊢
    obtain ⟨h1, h2⟩ := hy
    have hs : ∑ k, (y + (pfE s : S ⊕ T → ℕ)) k = K + 1 := by
      simp only [Pi.add_apply, Finset.sum_add_distrib, pfE_sum, h2]
    refine ⟨⟨fun k => ?_, hs⟩, ?_⟩
    · have : (y + (pfE s : S ⊕ T → ℕ)) k ≤ ∑ j, (y + (pfE s : S ⊕ T → ℕ)) j :=
        Finset.single_le_sum (f := fun j => (y + (pfE s : S ⊕ T → ℕ)) j) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ k)
      omega
    · simp [pfE_apply]
  · intro x hx
    simp only [pfStates, Finset.mem_filter] at hx
    exact (pf_decomp s x hx.2).symm
  · intro y _
    funext k
    simp
  · intro x hx
    simp only [pfStates, Finset.mem_filter] at hx
    conv_lhs => rw [pf_decomp s x hx.2]
    rw [pfW_add_single]

lemma pfAv_succ (a : S → ℝ) (b : T → ℝ) (K : ℕ) (s : S) :
    pfAv a b (K + 1) s = a s * pfG a b K / pfG a b (K + 1) := by
  unfold pfAv
  rw [pf_shift]

lemma pfAv_zero (a : S → ℝ) (b : T → ℝ) (s : S) : pfAv a b 0 s = 0 := by
  unfold pfAv
  have : (pfStates S T 0).filter (fun x => 1 ≤ x (Sum.inl s)) = ∅ := by
    apply Finset.filter_eq_empty_iff.2
    intro x hx
    simp only [pfStates, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range] at hx
    have : x (Sum.inl s) ≤ ∑ k, x k :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    omega
  rw [this]; simp

end PFCore

section PFPow
open Finset

lemma pf_coeff {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → PowerSeries ℝ) (K : ℕ) :
    PowerSeries.coeff K (∏ i, f i) =
      ∑ x ∈ (Fintype.piFinset fun _ : ι => range (K + 1)).filter (fun x => ∑ i, x i = K),
        ∏ i, PowerSeries.coeff (x i) (f i) := by
  rw [PowerSeries.coeff_prod]
  refine Finset.sum_bij' (fun l _ => ⇑l) (fun x _ => Finsupp.equivFunOnFinite.symm x) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    rw [Finset.mem_finsuppAntidiag] at hl
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    have h1 : ∑ j, l j = K := hl.1
    refine ⟨fun i => ?_, h1⟩
    have : l i ≤ ∑ j, l j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  · intro x hx
    simp only [Finset.mem_filter] at hx
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨by simpa using hx.2, ?_⟩
    intro i _; exact Finset.mem_univ i
  · intro l _
    ext i; simp
  · intro x _
    ext i; simp
  · intro l _
    rfl

noncomputable def pfGeo (ρ : ℝ) : PowerSeries ℝ := PowerSeries.mk (fun n => ρ ^ n)
noncomputable def pfExp (β : ℝ) : PowerSeries ℝ := PowerSeries.mk (fun n => β ^ n / (n.factorial : ℝ))

lemma pfExp_eq (β : ℝ) : pfExp β = PowerSeries.rescale β (PowerSeries.exp ℝ) := by
  ext n
  simp [pfExp, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  ring

lemma pfExp_mul (c d : ℝ) : pfExp c * pfExp d = pfExp (c + d) := by
  rw [pfExp_eq, pfExp_eq, pfExp_eq, PowerSeries.exp_mul_exp_eq_exp_add]

lemma pfExp_zero : pfExp 0 = 1 := by
  rw [pfExp_eq]; simp

lemma pfExp_prod {T : Type*} [Fintype T] (b : T → ℝ) :
    ∏ t, pfExp (b t) = pfExp (∑ t, b t) := by
  classical
  induction (Finset.univ : Finset T) using Finset.induction_on with
  | empty => simp [pfExp_zero]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, pfExp_mul]

lemma pfGeo_inv (ρ : ℝ) : (1 - PowerSeries.C ρ * PowerSeries.X) * pfGeo ρ = 1 := by
  ext n
  rcases n with _ | n
  · simp [pfGeo]
  · simp [pfGeo, sub_mul, PowerSeries.coeff_succ_X_mul, mul_assoc]
    ring

end PFPow

section PFRec
open Finset PowerSeries

lemma pfGeo_deriv (ρ : ℝ) : d⁄dX ℝ (pfGeo ρ) = C ρ * pfGeo ρ ^ 2 := by
  have h := congrArg (d⁄dX ℝ) (pfGeo_inv ρ)
  have hinv := pfGeo_inv ρ
  rw [Derivation.leibniz, derivative_one] at h
  simp at h
  have h' : (1 - C ρ * X) * d⁄dX ℝ (pfGeo ρ) = pfGeo ρ * C ρ := by
    linear_combination h
  linear_combination (pfGeo ρ) * h' - (d⁄dX ℝ (pfGeo ρ)) * hinv

lemma pfExp_deriv (β : ℝ) : d⁄dX ℝ (pfExp β) = C β * pfExp β := by
  ext n
  rw [coeff_derivative]
  simp only [pfExp, coeff_mk, coeff_C_mul]
  rw [Nat.factorial_succ]
  push_cast
  have : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end PFRec

section PFRec2
open Finset PowerSeries

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

lemma pfG_coeff (a : S → ℝ) (b : T → ℝ) (K : ℕ) :
    pfG a b K = coeff K (∏ i : S ⊕ T,
      (Sum.elim (fun s => pfGeo (a s)) (fun t => pfExp (b t)) i)) := by
  rw [pf_coeff]
  unfold pfG pfStates
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_sum_type]
  simp [pfW, pfGeo, pfExp, coeff_mk]

lemma pfG_sym (ρ : ℝ) (b : T → ℝ) (K : ℕ) :
    pfG (fun _ : S => ρ) b K = coeff K (pfGeo ρ ^ (Fintype.card S) * pfExp (∑ t, b t)) := by
  rw [pfG_coeff, Fintype.prod_sum_type]
  simp [pfExp_prod]

lemma coeff_A_mul (ρ : ℝ) (F : PowerSeries ℝ) (K : ℕ) :
    coeff (K + 1) ((1 - C ρ * X) * F) = coeff (K + 1) F - ρ * coeff K F := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_succ_X_mul]

lemma coeff_A_mul_zero (ρ : ℝ) (F : PowerSeries ℝ) :
    coeff 0 ((1 - C ρ * X) * F) = coeff 0 F := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul, coeff_zero_X_mul]; simp

lemma pf_main_identity (ρ : ℝ) (β : ℝ) (N : ℕ) :
    (1 - C ρ * X) * d⁄dX ℝ (pfGeo ρ ^ N * pfExp β) =
      (C ((N : ℝ) * ρ) + C β * (1 - C ρ * X)) * (pfGeo ρ ^ N * pfExp β) := by
  have hinv := pfGeo_inv ρ
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_pow, pfGeo_deriv, pfExp_deriv]
  have e : C ((N : ℝ) * ρ) = (N : PowerSeries ℝ) * C ρ := by simp
  rw [e]
  rcases N with _ | n
  · simp
    ring
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    linear_combination ((n + 1 : PowerSeries ℝ) * C ρ * pfGeo ρ ^ (n + 1) * pfExp β) * hinv

lemma pf_recurrence (ρ : ℝ) (b : T → ℝ) :
    pfG (fun _ : S => ρ) b 0 = 1 ∧
    pfG (fun _ : S => ρ) b 1 = (Fintype.card S : ℝ) * ρ + ∑ t, b t ∧
    ∀ K : ℕ, ((K : ℝ) + 2) * pfG (fun _ : S => ρ) b (K + 2) =
      ρ * ((K : ℝ) + 1 + Fintype.card S) * pfG (fun _ : S => ρ) b (K + 1) +
        (∑ t, b t) * (pfG (fun _ : S => ρ) b (K + 1) - ρ * pfG (fun _ : S => ρ) b K) := by
  have hH := pf_main_identity ρ (∑ t, b t) (Fintype.card S)
  set Gs := pfGeo ρ ^ (Fintype.card S) * pfExp (∑ t, b t) with hGs
  have hg : ∀ K, pfG (fun _ : S => ρ) b K = coeff K Gs := fun K => pfG_sym ρ b K
  have g0 : pfG (fun _ : S => ρ) b 0 = 1 := by
    rw [hg]
    simp [hGs, pfGeo, pfExp, coeff_zero_eq_constantCoeff]
  have hrhs : ∀ n : ℕ, coeff n ((C ((Fintype.card S : ℝ) * ρ) + C (∑ t, b t) * (1 - C ρ * X)) * Gs) =
      (Fintype.card S : ℝ) * ρ * coeff n Gs + (∑ t, b t) * coeff n ((1 - C ρ * X) * Gs) := by
    intro n
    simp only [add_mul, map_add, mul_assoc, coeff_C_mul]
  refine ⟨g0, ?_, ?_⟩
  · have := congrArg (coeff 0) hH
    rw [coeff_A_mul_zero, hrhs, coeff_A_mul_zero, coeff_derivative] at this
    have g0' : coeff 0 Gs = 1 := by rw [← hg 0]; exact g0
    rw [hg 1]
    simp only [zero_add, Nat.cast_one, mul_one, Nat.cast_zero] at this
    rw [g0'] at this
    linarith
  · intro K
    have := congrArg (coeff (K + 1)) hH
    rw [coeff_A_mul, hrhs, coeff_A_mul, coeff_derivative, coeff_derivative] at this
    simp only [hg]
    push_cast at this ⊢
    linarith

end PFRec2

section PFMain
open Finset

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

lemma pfG_nonneg (a : S → ℝ) (b : T → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ t, 0 ≤ b t) (K : ℕ) :
    0 ≤ pfG a b K :=
  Finset.sum_nonneg fun x _ => pfW_nonneg a b ha hb x

lemma pfAv_mem (a : S → ℝ) (b : T → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ t, 0 ≤ b t) (K : ℕ) (s : S) :
    0 ≤ pfAv a b K s ∧ pfAv a b K s ≤ 1 := by
  unfold pfAv pfG
  have hsub : (∑ x ∈ (pfStates S T K).filter (fun x => 1 ≤ x (Sum.inl s)), pfW a b x) ≤
      ∑ x ∈ pfStates S T K, pfW a b x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun x _ _ => pfW_nonneg a b ha hb x)
  have hnum : 0 ≤ ∑ x ∈ (pfStates S T K).filter (fun x => 1 ≤ x (Sum.inl s)), pfW a b x :=
    Finset.sum_nonneg fun x _ => pfW_nonneg a b ha hb x
  refine ⟨div_nonneg hnum (le_trans hnum hsub), ?_⟩
  rcases (le_trans hnum hsub).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · rw [div_le_one h0]; exact hsub

lemma pfG_pos (ρ : ℝ) (hρ : 0 < ρ) (b : T → ℝ) (hb : ∀ t, 0 ≤ b t) (s0 : S) (K : ℕ) :
    0 < pfG (fun _ : S => ρ) b K := by
  have hx0 : (fun k : S ⊕ T => if k = Sum.inl s0 then K else 0) ∈ pfStates S T K := by
    simp only [pfStates, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
    refine ⟨fun k => ?_, ?_⟩
    · by_cases h : k = Sum.inl s0 <;> simp [h]
    · simp
  have hw : pfW (fun _ : S => ρ) b (fun k : S ⊕ T => if k = Sum.inl s0 then K else 0) = ρ ^ K := by
    unfold pfW
    have h1 : ∏ s : S, ρ ^ (if (Sum.inl s : S ⊕ T) = Sum.inl s0 then K else 0) = ρ ^ K := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      simp
    have h2 : ∏ t : T, b t ^ (if (Sum.inr t : S ⊕ T) = Sum.inl s0 then K else 0) /
        (((if (Sum.inr t : S ⊕ T) = Sum.inl s0 then K else 0).factorial : ℕ) : ℝ) = 1 := by
      apply Finset.prod_eq_one
      intro t _
      simp
    rw [h1, h2, mul_one]
  have hle : pfW (fun _ : S => ρ) b (fun k : S ⊕ T => if k = Sum.inl s0 then K else 0) ≤
      pfG (fun _ : S => ρ) b K :=
    Finset.single_le_sum (f := pfW (fun _ : S => ρ) b)
      (fun x _ => pfW_nonneg _ b (fun _ => hρ.le) hb x) hx0
  rw [hw] at hle
  exact lt_of_lt_of_le (pow_pos hρ K) hle

theorem pf_eq5 [Nonempty S] (ρ : ℝ) (hρ : 0 < ρ) (b : T → ℝ) (hb : ∀ t, 0 ≤ b t)
    (K : ℕ) (hK : 1 ≤ K) (s : S) :
    pfAv (fun _ : S => ρ) b K s =
      (K : ℝ) / ((K : ℝ) + (Fintype.card S : ℝ) - 1 +
        ((∑ t, b t) / ρ) * (1 - pfAv (fun _ : S => ρ) b (K - 1) s)) := by
  obtain ⟨g0, g1, hrec⟩ := pf_recurrence (S := S) ρ b
  have hpos := pfG_pos ρ hρ b hb s
  have hav := pfAv_mem (fun _ : S => ρ) b (fun _ => hρ.le) hb
  have hβ : 0 ≤ ∑ t, b t := Finset.sum_nonneg fun t _ => hb t
  have hN : (1 : ℝ) ≤ Fintype.card S := by
    have : 0 < Fintype.card S := Fintype.card_pos
    exact_mod_cast this
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases k with _ | j
  · rw [pfAv_succ, pfAv_zero, g1, g0]
    simp
    have hNb : 0 < (Fintype.card S : ℝ) * ρ + ∑ t, b t := by nlinarith
    field_simp
  · rw [pfAv_succ, pfAv_succ]
    have hu := hpos j
    have hv := hpos (j + 1)
    have hw := hpos (j + 2)
    have hα := (hav (j + 1) s).2
    rw [pfAv_succ] at hα
    have hD : 0 < ((j + 1 + 1 : ℕ) : ℝ) + (Fintype.card S : ℝ) - 1 +
        ((∑ t, b t) / ρ) * (1 - ρ * pfG (fun _ : S => ρ) b j / pfG (fun _ : S => ρ) b (j + 1)) := by
      have : 0 ≤ ((∑ t, b t) / ρ) * (1 - ρ * pfG (fun _ : S => ρ) b j / pfG (fun _ : S => ρ) b (j + 1)) :=
        mul_nonneg (div_nonneg hβ hρ.le) (by linarith)
      push_cast
      linarith
    have hr := hrec j
    set u := pfG (fun _ : S => ρ) b j
    set v := pfG (fun _ : S => ρ) b (j + 1)
    set w := pfG (fun _ : S => ρ) b (j + 1 + 1)
    rw [div_eq_div_iff hw.ne' hD.ne']
    push_cast
    field_simp
    nlinarith [hr]

end PFMain

section PFUniq
open Finset

lemma pf_path_comp {V ι : Type*} (comp : V → ι) (f : V → V → ℝ)
    (hcomp : ∀ i j, 0 < f i j → comp i = comp j) {a b : V}
    (h : Relation.TransGen (fun a b => 0 < f a b) a b) : comp a = comp b := by
  induction h with
  | single hab => exact hcomp _ _ hab
  | tail _ hbc ih => exact ih.trans (hcomp _ _ hbc)

lemma pf_const_ratio {V ι : Type*} [Fintype V] (comp : V → ι) (f : V → V → ℝ) (lam r : V → ℝ)
    (hf : ∀ i j, 0 ≤ f i j)
    (hcomp : ∀ i j, 0 < f i j → comp i = comp j)
    (hlam_pos : ∀ i, 0 < lam i)
    (hbal : ∀ i, ∑ j, f j i = lam i)
    (htr : ∀ i, ∑ j, r j * f j i / lam j = r i)
    (hconn : ∀ i j, comp i = comp j → Relation.TransGen (fun a b => 0 < f a b) i j) :
    ∀ i j, comp i = comp j → r i / lam i = r j / lam j := by
  classical
  set h : V → ℝ := fun i => r i / lam i with hh
  have hr_eq : ∀ i, r i = lam i * h i := by
    intro i; simp only [hh]; field_simp [(hlam_pos i).ne']
  have hsum : ∀ i, ∑ j, f j i * (h i - h j) = 0 := by
    intro i
    have h1 : ∑ j, f j i * h j = r i := by
      rw [← htr i]
      apply Finset.sum_congr rfl
      intro j _
      simp only [hh]; field_simp [(hlam_pos j).ne']
    have h2 : ∑ j, f j i * (h i - h j) = (∑ j, f j i) * h i - ∑ j, f j i * h j := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [h2, h1, hbal i, hr_eq i]; ring
  intro i j hij
  obtain ⟨i0, hi0mem, hi0max⟩ := Finset.exists_max_image (Finset.univ.filter (fun k => comp k = comp i))
    h ⟨i, by simp⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi0mem hi0max
  -- predecessor lemma
  have pred : ∀ i', comp i' = comp i → h i' = h i0 → ∀ k, 0 < f k i' → h k = h i0 := by
    intro i' hi' hhi' k hk
    have hterm : ∀ j ∈ (Finset.univ : Finset V), 0 ≤ f j i' * (h i' - h j) := by
      intro j _
      rcases (hf j i').eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · have hc : comp j = comp i := (hcomp j i' h0).trans hi'
        have := hi0max j hc
        exact mul_nonneg h0.le (by rw [hhi']; linarith)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).1 (hsum i') k (Finset.mem_univ k)
    rcases mul_eq_zero.1 hz with h0 | h0
    · exact absurd h0 hk.ne'
    · rw [← hhi']; linarith
  have key : ∀ k, comp k = comp i → h k = h i0 := by
    intro k hk
    have hpath := hconn k i0 (hk.trans hi0mem.symm)
    induction hpath using Relation.TransGen.head_induction_on with
    | single hab =>
      exact pred _ hi0mem rfl _ hab
    | head hab hbc ih =>
      rename_i a c
      have hc : comp c = comp i := by
        have := pf_path_comp comp f hcomp hbc
        rw [this]; exact hi0mem
      exact pred c hc (ih hc) a hab
  have hj : comp j = comp i := hij.symm
  show h i = h j
  rw [key i rfl, key j hj]

end PFUniq

section VSSWrap
open Finset VehicleSharePricing.Static

variable {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]

lemma vss_avail_eq (P : Instance L) (q : L → L → ℝ) (r : L → ℝ) (K : ℕ) (i : L) :
    availability P q r K i =
      pfAv (fun i => r i / outRate P q i)
        (fun p : L × L => r p.1 * effRate P q p.1 p.2 / (outRate P q p.1 * P.rate p.1 p.2)) K i := by
  unfold availability pfBusyProb pfAv pfProb pfNormConst pfG
  have hs : popStates (Station L) K = pfStates L (L × L) K := rfl
  have hw : ∀ x : Station L → ℕ, pfWeight (stationLoad P q r) stationIsIS x =
      pfW (fun i => r i / outRate P q i)
        (fun p : L × L => r p.1 * effRate P q p.1 p.2 / (outRate P q p.1 * P.rate p.1 p.2)) x := by
    intro x
    unfold pfWeight pfW
    rw [Fintype.prod_sum_type]
    simp [stationIsIS, stationLoad]
  rw [hs, ← Finset.sum_div]
  simp only [hw]

lemma vss_lq_nonneg (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (i j : L) :
    0 ≤ effRate P q i j := by
  unfold effRate
  rcases (P.demand_nonneg i j).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · exact mul_nonneg h0.le (hq i j h0).1

lemma vss_b_nonneg (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (ρ : ℝ) (hρ : 0 < ρ)
    (p : L × L) : 0 ≤ ρ * (P.demand p.1 p.2 * q p.1 p.2 / P.rate p.1 p.2) := by
  rcases (P.demand_nonneg p.1 p.2).eq_or_lt with h0 | h0
  · rw [← h0]; simp
  · have hμ := P.rate_pos _ _ h0
    have := (hq _ _ h0).1
    positivity

lemma vss_sum_b (P : Instance L) (q : L → L → ℝ) (ρ : ℝ) :
    ∑ p : L × L, ρ * (P.demand p.1 p.2 * q p.1 p.2 / P.rate p.1 p.2) = ρ * workload P q := by
  rw [← Finset.mul_sum, Fintype.sum_prod_type]
  rfl

lemma vss_key (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (K : ℕ) (i : L), availability P q r K i =
      pfAv (fun _ : L => ρ) (fun p : L × L => ρ * (P.demand p.1 p.2 * q p.1 p.2 / P.rate p.1 p.2)) K i := by
  have hf := vss_lq_nonneg P q hq
  have hlam_pos : ∀ i, 0 < outRate P q i := by
    intro i
    obtain ⟨c, hc, _⟩ := (Relation.TransGen.head'_iff.1 (hconn i i))
    unfold outRate
    calc (0 : ℝ) < effRate P q i c := hc
      _ ≤ _ := Finset.single_le_sum (f := fun j => effRate P q i j) (fun j _ => hf i j) (Finset.mem_univ c)
  have hbal' : ∀ i, ∑ j, effRate P q j i = outRate P q i := by
    intro i
    have := hbal i
    unfold outRate effRate
    exact this.symm
  have hconst := pf_const_ratio (fun _ : L => ()) (effRate P q) (outRate P q) r
    hf (fun _ _ _ => rfl) hlam_pos hbal' hr.2 (fun i j _ => hconn i j)
  obtain ⟨i0⟩ := ‹Nonempty L›
  have hρ : 0 < r i0 / outRate P q i0 := div_pos (hr.1 i0) (hlam_pos i0)
  refine ⟨r i0 / outRate P q i0, hρ, ?_⟩
  intro K i
  have hρi : ∀ i, r i / outRate P q i = r i0 / outRate P q i0 := fun i => hconst i i0 rfl
  have ha : (fun i => r i / outRate P q i) = fun _ : L => r i0 / outRate P q i0 :=
    funext hρi
  have hb : (fun p : L × L => r p.1 * effRate P q p.1 p.2 / (outRate P q p.1 * P.rate p.1 p.2)) =
      fun p : L × L => r i0 / outRate P q i0 *
        (P.demand p.1 p.2 * q p.1 p.2 / P.rate p.1 p.2) := by
    funext p
    rw [← hρi p.1]
    have := (hlam_pos p.1).ne'
    by_cases hμ : P.rate p.1 p.2 = 0
    · simp [hμ]
    · unfold effRate
      field_simp
  rw [vss_avail_eq, ha, hb]

lemma vss_equal (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r)
    (K : ℕ) (i j : L) : availability P q r K i = availability P q r K j := by
  obtain ⟨ρ, hρ, hK⟩ := vss_key P q hq hbal hconn r hr
  rw [hK K i, hK K j]
  rcases K with _ | k
  · rw [pfAv_zero, pfAv_zero]
  · rw [pfAv_succ, pfAv_succ]

lemma vss_eq5 (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r)
    (K : ℕ) (hK : 1 ≤ K) (i : L) :
    availability P q r K i =
      (K : ℝ) / ((K : ℝ) + (Fintype.card L : ℝ) - 1 +
        workload P q * (1 - availability P q r (K - 1) i)) := by
  obtain ⟨ρ, hρ, hav⟩ := vss_key P q hq hbal hconn r hr
  rw [hav K i, hav (K - 1) i,
    pf_eq5 ρ hρ _ (vss_b_nonneg P q hq ρ hρ) K hK i, vss_sum_b P q ρ,
    mul_div_cancel_left₀ _ hρ.ne']

end VSSWrap

open VehicleSharePricing.Static

theorem solution {L : Type*} [Fintype L] [DecidableEq L] [Nonempty L]
    (P : Instance L) (q : L → L → ℝ) (hq : IsQuantile P q) (hbal : Balanced P q)
    (hconn : InducesStronglyConnected P q) (r : L → ℝ) (hr : IsTrafficSolution P q r)
    (K : ℕ) (hK : 1 ≤ K) (i : L) :
    availability P q r K i =
      (K : ℝ) / ((K : ℝ) + (Fintype.card L : ℝ) - 1 +
        workload P q * (1 - availability P q r (K - 1) i)) :=
  vss_eq5 P q hq hbal hconn r hr K hK i
