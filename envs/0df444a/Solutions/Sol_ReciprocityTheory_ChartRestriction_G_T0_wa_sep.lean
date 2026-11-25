-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.wa_sep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:45:47.369479+00:00
-- url     : https://prove2.me/submissions/841dfc57-c46b-44cc-8951-f388e929077a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_exists_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_ne_zero_of_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_pair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.ChartRestriction.G.T0
open Filter
section WeakApproxAux
variable {F : Type*} [Field F]
private theorem addValuation_add_eq_of_lt (w : AddValuation F (WithTop ℤ)) {x y : F} (h : w x < w y) :
    w (x + y) = w x := by
  rw [AddValuation.map_add_of_distinct_val w h.ne, min_eq_left h.le]
private theorem addValuation_one_add_pow_of_pos (w : AddValuation F (WithTop ℤ)) {s : F} {a : ℤ} (hs : w s = a)
    (M : ℕ) (hM : 0 < M) (ha : 0 < a) : w (1 + s ^ M) = ((0 : ℤ) : WithTop ℤ) := by
  have h1 := wa_pow w hs M
  have h2 : w 1 < w (s ^ M) := by
    rw [h1, AddValuation.map_one, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    exact mul_pos (by exact_mod_cast hM) ha
  rw [addValuation_add_eq_of_lt w h2, AddValuation.map_one, WithTop.coe_zero]
private theorem addValuation_one_add_pow_of_neg (w : AddValuation F (WithTop ℤ)) {s : F} {a : ℤ} (hs : w s = a)
    (M : ℕ) (hM : 0 < M) (ha : a < 0) : w (1 + s ^ M) = ((↑M * a : ℤ) : WithTop ℤ) := by
  have h1 := wa_pow w hs M
  have h2 : w (s ^ M) < w 1 := by
    rw [h1, AddValuation.map_one, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hM) ha
  rw [add_comm, addValuation_add_eq_of_lt w h2, h1]
private theorem exists_nat_gt_of_finset {ι : Type*} (T : Finset ι) (c : ι → ℤ) :
    ∃ N : ℕ, ∀ j ∈ T, c j < N := by
  refine ⟨(∑ j ∈ T, (c j).toNat) + 1, fun j hj => ?_⟩
  have h1 := Int.self_le_toNat (c j)
  have h2 : (c j).toNat ≤ ∑ j ∈ T, (c j).toNat :=
    Finset.single_le_sum (f := fun j => (c j).toNat) (fun _ _ => Nat.zero_le _) hj
  have h3 : ((c j).toNat : ℤ) ≤ ((∑ j ∈ T, (c j).toNat : ℕ) : ℤ) := Nat.cast_le.mpr h2
  rw [Nat.cast_succ]
  linarith
end WeakApproxAux
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Filter
variable {F : Type*} [Field F]
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {ι : Type*} [DecidableEq ι] (v : ι → AddValuation F (WithTop ℤ))
    (hfin : ∀ i (a : F), a ≠ 0 → v i a ≠ ⊤) (hone : ∀ i, ∃ π : F, v i π = 1)
    (hdist : Pairwise fun i j => v i ≠ v j) (i : ι) (T : Finset ι) (hi : i ∉ T) :
    ∃ s : F, s ≠ 0 ∧ 0 < v i s ∧ ∀ j ∈ T, v j s < 0 := by
  revert hi
  refine Finset.induction_on T ?_ ?_
  · intro _
    obtain ⟨q, hq⟩ := hone i
    have hq1 : v i q = ((1 : ℤ) : WithTop ℤ) := by rw [WithTop.coe_one]; exact hq
    refine ⟨q, wa_ne_zero_of_coe (v i) hq1, ?_, ?_⟩
    · rw [hq1, ← WithTop.coe_zero, WithTop.coe_lt_coe]
      exact one_pos
    · intro j hj
      simp at hj
  · intro j T hjT ih hi
    have hij : i ≠ j := by
      rintro rfl
      exact hi (Finset.mem_insert_self _ _)
    have hiT : i ∉ T := fun h => hi (Finset.mem_insert_of_mem h)
    obtain ⟨s, hs0, hsi, hsT⟩ := ih hiT
    obtain ⟨t, hti, htj⟩ := wa_pair (v i) (v j) (hfin i) (hfin j) (hone i) (hone j) (hdist hij)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [AddValuation.map_zero] at htj
      exact absurd htj (not_lt.mpr le_top)
    choose a ha using fun l => wa_exists_coe (v l) (hfin l) hs0
    choose c hc using fun l => wa_exists_coe (v l) (hfin l) ht0
    have hai : 0 < a i := by
      have h' := hsi
      rw [ha i, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
      exact h'
    have hci : 0 < c i := by
      have h' := hti
      rw [hc i, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
      exact h'
    have hcj : c j < 0 := by
      have h' := htj
      rw [hc j, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
      exact h'
    have haT : ∀ l ∈ T, a l < 0 := by
      intro l hl
      have h' := hsT l hl
      rw [ha l, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
      exact h'
    obtain ⟨N1, hN1⟩ := exists_nat_gt_of_finset T c
    obtain ⟨N2, hN2⟩ := exists_nat_gt_of_finset T (fun l => -c l)
    by_cases hajle : a j ≤ 0
    · have hv : ∀ l, v l (s ^ N1 * t) = ((↑N1 * a l + c l : ℤ) : WithTop ℤ) :=
        fun l => wa_mul (v l) (wa_pow (v l) (ha l) N1) (hc l)
      refine ⟨s ^ N1 * t, wa_ne_zero_of_coe (v i) (hv i), ?_, ?_⟩
      · rw [hv i, ← WithTop.coe_zero, WithTop.coe_lt_coe]
        have h0 : (0 : ℤ) ≤ (N1 : ℤ) * a i := mul_nonneg (by positivity) hai.le
        linarith
      · intro l hl
        rw [hv l, ← WithTop.coe_zero, WithTop.coe_lt_coe]
        rcases Finset.mem_insert.mp hl with hlj | hlT
        · rw [hlj]
          have h0 : (N1 : ℤ) * a j ≤ 0 := by nlinarith [(by positivity : (0 : ℤ) ≤ (N1 : ℤ))]
          linarith
        · have hb : c l < (N1 : ℤ) := hN1 l hlT
          have hal := haT l hlT
          have h0 : (0 : ℤ) ≤ (N1 : ℤ) * (-1 - a l) := mul_nonneg (by positivity) (by omega)
          nlinarith
    · have hajpos : 0 < a j := by omega
      have hM : 0 < N2 + 1 := Nat.succ_pos N2
      have hDi := addValuation_one_add_pow_of_pos (v i) (ha i) (N2 + 1) hM hai
      have hDj := addValuation_one_add_pow_of_pos (v j) (ha j) (N2 + 1) hM hajpos
      have hti' := wa_mul (v i) (hc i) (wa_inv (v i) hDi)
      have htj' := wa_mul (v j) (hc j) (wa_inv (v j) hDj)
      have hltj : v j (t * (1 + s ^ (N2 + 1))⁻¹) < v j s := by
        rw [htj', ha j, WithTop.coe_lt_coe]
        omega
      have hj : v j (s + t * (1 + s ^ (N2 + 1))⁻¹) = ((c j + -0 : ℤ) : WithTop ℤ) := by
        rw [add_comm, addValuation_add_eq_of_lt (v j) hltj, htj']
      refine ⟨s + t * (1 + s ^ (N2 + 1))⁻¹, wa_ne_zero_of_coe (v j) hj, ?_, ?_⟩
      · refine lt_of_lt_of_le (lt_min hsi ?_) (AddValuation.map_add (v i) _ _)
        rw [hti', ← WithTop.coe_zero, WithTop.coe_lt_coe]
        omega
      · intro l hl
        rcases Finset.mem_insert.mp hl with hlj | hlT
        · rw [hlj, hj, ← WithTop.coe_zero, WithTop.coe_lt_coe]
          omega
        · have hal := haT l hlT
          have hDl := addValuation_one_add_pow_of_neg (v l) (ha l) (N2 + 1) hM hal
          have htl' := wa_mul (v l) (hc l) (wa_inv (v l) hDl)
          have hb : -c l < (N2 : ℤ) := hN2 l hlT
          have hlt : v l s < v l (t * (1 + s ^ (N2 + 1))⁻¹) := by
            rw [ha l, htl', WithTop.coe_lt_coe]
            have h0 : (0 : ℤ) ≤ ((N2 + 1 : ℕ) : ℤ) * (-1 - a l) :=
              mul_nonneg (by positivity) (by omega)
            have h3 : ((N2 + 1 : ℕ) : ℤ) = (N2 : ℤ) + 1 := Nat.cast_succ N2
            nlinarith
          rw [addValuation_add_eq_of_lt (v l) hlt, ha l, ← WithTop.coe_zero, WithTop.coe_lt_coe]
          exact hal
end ReciprocityTheory.ChartRestriction.G.T0
