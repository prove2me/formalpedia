-- Prove2me | solution 1 for RestrictedAP.Counting.fact_2_12
-- status  : ACCEPTED   (disprove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:59:14.250199+00:00
-- url     : https://prove2.me/submissions/e5b925a4-b0dd-4649-87e3-3940e124eb9e

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions
import Definitions.Def_RestrictedAP_Counting_ProductFunctions
import Definitions.Def_RestrictedAP_Counting_NoiseOperators

section
open Classical

namespace RestrictedAP.Counting.Dev.CE

/-- the one-letter sign function: `false ↦ 1`, `true ↦ -1`. -/
def u1 : Bool → ℂ := fun b => if b then -1 else 1

/-- the sign product on `Bool^n`. -/
def Pn (n : ℕ) : (Fin n → Bool) → ℂ := fun x => ∏ i, u1 (x i)

/-- the point mass on `false`. -/
def nu1 : Bool → ℝ := fun b => if b then 0 else 1

theorem nu1_isDist : IsDist nu1 := by
  refine ⟨fun x => by cases x <;> simp [nu1], ?_⟩
  simp [nu1]

theorem nu1_atoms : AtomsAtLeast nu1 1 := by
  intro x hx
  cases x <;> simp [nu1] at hx ⊢

theorem norm_u1 (b : Bool) : ‖u1 b‖ = 1 := by cases b <;> simp [u1]

theorem Pn_isProduct (n : ℕ) : IsProductFunction false (Pn n) :=
  ⟨fun _ => u1, fun _ a => norm_u1 a, fun _ => by simp [u1], fun x => rfl⟩

theorem Pn_const_false (n : ℕ) : Pn n (fun _ => false) = 1 := by simp [Pn, u1]

theorem prod_split {n : ℕ} (w : Fin n → Bool → ℂ) (i : Fin n) (b : Bool) :
    ∏ j, w j ((Function.update (fun _ : Fin n => false) i b) j) =
      w i b * ∏ j ∈ Finset.univ.erase i, w j false := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

theorem Pn_update_true (n : ℕ) (i : Fin n) :
    Pn n (Function.update (fun _ : Fin n => false) i true) = -1 := by
  unfold Pn
  rw [prod_split (fun _ => u1) i true]
  simp [u1]

theorem pn_sq (n : ℕ) : Pn n * Pn n = 1 := by
  funext x
  simp only [Pn, Pi.mul_apply, Pi.one_apply]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  cases x i <;> simp [u1]

theorem Pn_ne_one (n : ℕ) (hn : 1 ≤ n) : Pn n ≠ 1 := by
  intro h
  have := congrFun h (Function.update (fun _ : Fin n => false) ⟨0, hn⟩ true)
  rw [Pn_update_true] at this
  simp at this
  have h2 : (2 : ℂ) = 0 := by linear_combination -this
  norm_num at h2

theorem orderOf_Pn (n : ℕ) (hn : 1 ≤ n) : orderOf (Pn n) = 2 := by
  apply orderOf_eq_prime
  · rw [sq]; exact pn_sq n
  · exact Pn_ne_one n hn

theorem discrete_Pn (n : ℕ) (hn : 1 ≤ n) : IsDiscrete 2 (Pn n) := by
  unfold IsDiscrete; rw [orderOf_Pn n hn]; norm_num

theorem symbolic_key (n : ℕ) (u v : Fin n → Bool → ℂ) (hu : ∀ i a, ‖u i a‖ = 1)
    (hv : ∀ i a, ‖v i a‖ = 1) (hP : ∀ x, Pn n x = ∏ i, u i (x i))
    (h1 : ∀ x, (1 : (Fin n → Bool) → ℂ) x = ∏ i, v i (x i)) (i : Fin n) : u i ≠ v i := by
  intro h
  set x : Fin n → Bool := fun _ => false with hx
  set y := Function.update x i true with hy
  have e1 := hP x
  have e2 := hP y
  have e3 := h1 x
  have e4 := h1 y
  have hxx : ∏ j, u j (x j) = u i false * ∏ j ∈ Finset.univ.erase i, u j false := by
    rw [← prod_split u i false]; apply Finset.prod_congr rfl; intro j _; by_cases hj : j = i <;> simp [hx, hj]
  rw [hxx] at e1
  rw [hy, prod_split u i true] at e2
  have hxv : ∏ j, v j (x j) = v i false * ∏ j ∈ Finset.univ.erase i, v j false := by
    rw [← prod_split v i false]; apply Finset.prod_congr rfl; intro j _; by_cases hj : j = i <;> simp [hx, hj]
  rw [hxv] at e3
  rw [hy, prod_split v i true] at e4
  rw [Pn_const_false] at e1
  rw [Pn_update_true] at e2
  simp only [Pi.one_apply] at e3 e4
  rw [h] at e1 e2
  set A := ∏ j ∈ Finset.univ.erase i, u j false
  set B := ∏ j ∈ Finset.univ.erase i, v j false
  have hB : B ≠ 0 := by
    intro h0; rw [h0] at e3; simp at e3
  have hvv : v i false = v i true := mul_right_cancel₀ hB (e3.symm.trans e4)
  rw [hvv] at e1
  have : (1 : ℂ) = -1 := e1.trans e2.symm
  norm_num at this

theorem symbolic_Pn (n : ℕ) : n ≤ symbolicDist (Pn n) 1 := by
  unfold symbolicDist
  apply le_csInf
  · exact ⟨_, fun _ => u1, fun _ => 1, fun _ a => norm_u1 a, fun _ _ => by simp,
      fun x => rfl, fun x => by simp, rfl⟩
  · rintro k ⟨u, v, hu, hv, hP, h1, hk⟩
    rw [← hk]
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ _ := Finset.card_le_card (fun i _ => by simp [symbolic_key n u v hu hv hP h1 i])

/-- the weighted sum over `Bool^n` against the point mass is the value at the constant-false point. -/
theorem tensor_nu1 (n : ℕ) (x : Fin n → Bool) :
    tensorPow nu1 n x = if x = (fun _ => false) then 1 else 0 := by
  unfold tensorPow
  split_ifs with h
  · subst h; simp [nu1]
  · obtain ⟨i, hi⟩ : ∃ i, x i ≠ false := by
      by_contra hc; push Not at hc; exact h (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have : x i = true := by simpa using hi
    simp [nu1, this]

end RestrictedAP.Counting.Dev.CE

namespace RestrictedAP.Counting.Dev.CE

theorem expectC_Pn (n : ℕ) : expectC (tensorPow nu1 n) (Pn n) = 1 := by
  unfold expectC
  simp_rw [tensor_nu1]
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp [Pn_const_false]
  · intro x _ hx; simp [hx]
  · simp

theorem rpow_lt_one' (c : ℝ) (hc : 0 < c) : (2 : ℝ) ^ (-(c * ((1 : ℤ) : ℝ))) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
  simp; exact hc

end RestrictedAP.Counting.Dev.CE
end

section
open Classical

namespace RestrictedAP.Counting.Dev.CE

theorem fact_2_12_false : ¬ (
    (∀ (M : ℕ) (α : ℝ), 0 < α → ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ) (n : ℕ)
        (P : (Fin n → Sig) → ℂ) (D : ℤ),
        IsDist ν → AtomsAtLeast ν α → IsProductFunction σs P → IsDiscrete M P →
        (D : ℝ) ≤ (symbolicDist P 1 : ℝ) →
        ‖expectC (tensorPow ν n) P‖ ≤ (2 : ℝ) ^ (-(c * D))) ∧
    (∀ (M : ℕ) (α τ : ℝ), 0 < α → 0 < τ → τ ≤ 1 → ∃ c : ℝ, 0 < c ∧
      ∀ (Sig : Type) [Fintype Sig] [DecidableEq Sig] (σs : Sig) (ν : Sig → ℝ) (n : ℕ)
        (P : (Fin n → Sig) → ℂ) (D : ℤ),
        IsDist ν → AtomsAtLeast ν α → IsProductFunction σs P → IsDiscrete M P →
        (D : ℝ) ≤ (symbolicDist P 1 : ℝ) →
        l2Norm (tensorPow ν n) (noiseOp ν (1 - τ) n P) ≤ (2 : ℝ) ^ (-(c * D)))) := by
  rintro ⟨h1, -⟩
  obtain ⟨c, hc, H⟩ := h1 2 1 one_pos
  have := H Bool false nu1 1 (Pn 1) 1 nu1_isDist nu1_atoms (Pn_isProduct 1) (discrete_Pn 1 le_rfl)
    (by exact_mod_cast symbolic_Pn 1)
  rw [expectC_Pn] at this
  have h2 := rpow_lt_one' c hc
  simp only [norm_one] at this
  exact absurd this (not_le.mpr h2)

end RestrictedAP.Counting.Dev.CE
end
theorem solution : type_of% @RestrictedAP.Counting.Dev.CE.fact_2_12_false := @RestrictedAP.Counting.Dev.CE.fact_2_12_false
