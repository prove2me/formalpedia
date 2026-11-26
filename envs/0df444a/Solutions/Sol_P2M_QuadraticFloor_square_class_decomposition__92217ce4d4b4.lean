-- Prove2me | solution 1 for P2M_QuadraticFloor_square_class_decomposition__92217ce4d4b4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:00:41.137679+00:00
-- url     : https://prove2.me/submissions/28046738-70da-46f6-9b24-9d2b1035638c

module
public import Definitions.Def_QuadraticFloor_HalfPeriod
public import Definitions.Def_QuadraticFloor_SquareClass
public import Theorems.Thm_QuadraticFloor_ind_mod_A
public import Theorems.Thm_QuadraticFloor_ind_mod_eight
public import Theorems.Thm_QuadraticFloor_mod_eight_mul_iff
public import Theorems.Thm_QuadraticFloor_admissible_data
public import Theorems.Thm_P2M_QuadraticFloor_window__8c99d9986259
public import Theorems.Thm_QuadraticFloor_sum_window_char
public import Theorems.Thm_QuadraticFloor_vartheta_add_half
public import Theorems.Thm_P2M_QuadraticFloor_bern_antiperiodic__37acfbc76d79
public import Theorems.Thm_QuadraticFloor_eta_of_even


set_option autoImplicit true
@[expose] public section
public section
open QuadraticFloor
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {A : ℕ}
namespace QuadraticFloor
theorem _root_.solution (hp2 : p ≠ 2) [NeZero A] (hA : Odd A) (hpA : ¬ p ∣ A)
    {B C : ℤ} (hBC : Admissible A B C) :
    (floorSum A B C p : ℂ) = (C.negOnePow : ℤ) - (1 / (A.totient : ℂ)) *
      ∑ ψ : DirichletCharacter ℂ A, (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 *
        bern (8 * A * p) (vartheta p ψ) := by
  obtain ⟨d, hdD, hd1, hd4A, hd4, hd8⟩ := admissible_data hA hBC
  have hwin := window' hp2 hA hpA hBC hdD hd4A hd8
  have hdA : (d : ZMod A) = (B : ZMod A) ^ 2 := by
    have : ((d : ℤ) : ZMod A) = ((B ^ 2 - 4 * A * C : ℤ) : ZMod A) := by rw [hdD]
    push_cast at this
    rw [this, ZMod.natCast_self]; ring
  have hd8A : d < 8 * A := by omega
  have hh : 0 < 4 * A * p := by
    have := hA.pos; have := hp.out.pos; positivity
  -- expand the indicator of `x ≡ d (mod 8A)` for every `x`
  have hpt : ∀ x ∈ Icc 1 (4 * A * p),
      (if x % (8 * A) = d then (eta p x : ℂ) else 0) =
        (1 / (4 * (A.totient : ℂ))) * ∑ ψ : DirichletCharacter ℂ A,
          (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * ((eta p x : ℂ) * ψ (x : ZMod A) *
            (1 + (ZMod.χ₄ (x : ZMod 4) : ℂ) + (ZMod.χ₈ (d : ZMod 8) : ℂ) *
              ((ZMod.χ₈ (x : ZMod 8) : ℂ) + (ZMod.χ₈' (x : ZMod 8) : ℂ)))) := by
    intro x _
    by_cases hx : Even x
    · simp [eta_of_even hx]
    have hxo : Odd x := Nat.not_even_iff_odd.1 hx
    have e1 : (if x % (8 * A) = d then (eta p x : ℂ) else 0) =
        (if x % 8 = d % 8 then (1 : ℂ) else 0) * (if x % A = d % A then (1 : ℂ) else 0) *
          (eta p x : ℂ) := by
      by_cases h8 : x % 8 = d % 8 <;> by_cases hA' : x % A = d % A <;>
        simp [mod_eight_mul_iff hA hd8A, h8, hA']
    rw [e1, ind_mod_eight hxo hd4, ind_mod_A hBC.2.1 hdA x, mul_sum, mul_sum, sum_mul, mul_sum]
    apply sum_congr rfl
    intro ψ _
    ring
  have hfilter : ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), (eta p x : ℂ) =
      ∑ x ∈ Icc 1 (4 * A * p), (if x % (8 * A) = d then (eta p x : ℂ) else 0) := by
    rw [sum_filter]
  have hmain : ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), (eta p x : ℂ) =
      (1 / (4 * (A.totient : ℂ))) * ∑ ψ : DirichletCharacter ℂ A,
        (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * (-2 * bern (8 * A * p) (vartheta p ψ)) := by
    rw [hfilter, sum_congr rfl hpt, ← mul_sum, sum_comm]
    congr 1
    apply sum_congr rfl
    intro ψ _
    rw [← mul_sum, sum_window_char hp2 hA hpA ψ, show 8 * A * p = 2 * (4 * A * p) by ring,
      bern_antiperiodic' _ hh (vartheta_add_half hp2 hA ψ)]
    ring
  have hwinC : (floorSum A B C p : ℂ) - ((C.negOnePow : ℤ) : ℂ) =
      2 * ∑ x ∈ (Icc 1 (4 * A * p)).filter (fun x => x % (8 * A) = d), (eta p x : ℂ) := by
    exact_mod_cast hwin
  have htot : (A.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.2 hA.pos).ne'
  rw [hmain] at hwinC
  have : (floorSum A B C p : ℂ) = ((C.negOnePow : ℤ) : ℂ) + 2 * ((1 / (4 * (A.totient : ℂ))) *
      ∑ ψ : DirichletCharacter ℂ A,
        (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * (-2 * bern (8 * A * p) (vartheta p ψ))) := by
    rw [← hwinC]; ring
  have hs : ∑ ψ : DirichletCharacter ℂ A,
      (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * (-2 * bern (8 * A * p) (vartheta p ψ)) =
      -2 * ∑ ψ : DirichletCharacter ℂ A,
        (starRingEnd ℂ (ψ (B : ZMod A))) ^ 2 * bern (8 * A * p) (vartheta p ψ) := by
    rw [mul_sum]; exact sum_congr rfl fun ψ _ => by ring
  rw [this, hs]
  field_simp
  ring
end QuadraticFloor
