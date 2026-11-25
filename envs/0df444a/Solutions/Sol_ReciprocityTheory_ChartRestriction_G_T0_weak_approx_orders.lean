-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.weak_approx_orders
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:52:01.306812+00:00
-- url     : https://prove2.me/submissions/76cd84ab-b93e-4d9a-9112-19bd2502238b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_exists_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_ne_zero_of_coe
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_zpow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_wa_sep
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
private theorem lt_addValuation_sum_of_forall_lt {F : Type*} [Field F] {ι : Type*} (w : AddValuation F (WithTop ℤ))
    (S : Finset ι) (x : ι → F) (c : WithTop ℤ) (h : ∀ i ∈ S, c < w (x i)) (hc : c ≠ ⊤) :
    c < w (∑ i ∈ S, x i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    rw [Finset.sum_empty, AddValuation.map_zero]
    exact lt_top_iff_ne_top.mpr hc
  · intro j S hjS ih h
    rw [Finset.sum_insert hjS]
    exact lt_of_lt_of_le (lt_min (h j (Finset.mem_insert_self j S))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))) (AddValuation.map_add w _ _)
end ReciprocityTheory.ChartRestriction.G.T0
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open Filter
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {F : Type*} [Field F] {k : ℕ} (v : Fin k → AddValuation F (WithTop ℤ))
    (hfin : ∀ i (a : F), a ≠ 0 → v i a ≠ ⊤) (hone : ∀ i, ∃ π : F, v i π = 1)
    (hdist : Pairwise fun i j => v i ≠ v j) (n : Fin k → ℤ) :
    ∃ g : F, ∀ i, v i g = n i := by
  choose s hs0 hsi hsj using
    fun i => wa_sep v hfin hone hdist i (Finset.univ.erase i) (by simp)
  choose q hq using hone
  have hq1 : ∀ i, v i (q i) = ((1 : ℤ) : WithTop ℤ) := fun i => by
    rw [WithTop.coe_one]
    exact hq i
  have hq0 : ∀ i, q i ≠ 0 := fun i => wa_ne_zero_of_coe (v i) (hq1 i)
  choose p hp using fun i j => wa_exists_coe (v j) (hfin j) (hq0 i)
  choose a ha using fun i j => wa_exists_coe (v j) (hfin j) (hs0 i)
  have hai : ∀ i, 0 < a i i := fun i => by
    have h' := hsi i
    rw [ha i i, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
    exact h'
  have haij : ∀ i j, i ≠ j → a i j < 0 := fun i j hij => by
    have h' := hsj i j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
    rw [ha i j, ← WithTop.coe_zero, WithTop.coe_lt_coe] at h'
    exact h'
  choose N hN using fun i => exists_nat_gt_of_finset (Finset.univ : Finset (Fin k)) (fun j => n j - n i * p i j)
  have hdiag : ∀ i, v i (q i ^ n i * (1 + s i ^ (N i + 1))⁻¹) = ((n i : ℤ) : WithTop ℤ) := by
    intro i
    rw [wa_mul (v i) (wa_zpow (v i) (hq1 i) (n i))
      (wa_inv (v i) (addValuation_one_add_pow_of_pos (v i) (ha i i) (N i + 1) (Nat.succ_pos _) (hai i)))]
    congr 1
    ring
  have hoff : ∀ i j, i ≠ j →
      ((n j : ℤ) : WithTop ℤ) < v j (q i ^ n i * (1 + s i ^ (N i + 1))⁻¹) := by
    intro i j hij
    have hneg : a i j < 0 := haij i j hij
    rw [wa_mul (v j) (wa_zpow (v j) (hp i j) (n i))
      (wa_inv (v j) (addValuation_one_add_pow_of_neg (v j) (ha i j) (N i + 1) (Nat.succ_pos _) hneg)),
      WithTop.coe_lt_coe]
    have hb : n j - n i * p i j < (N i : ℤ) := hN i j (Finset.mem_univ j)
    have h0 : (0 : ℤ) ≤ ((N i + 1 : ℕ) : ℤ) * (-1 - a i j) := mul_nonneg (by positivity) (by omega)
    have h3 : ((N i + 1 : ℕ) : ℤ) = (N i : ℤ) + 1 := Nat.cast_succ (N i)
    nlinarith
  refine ⟨∑ i, q i ^ n i * (1 + s i ^ (N i + 1))⁻¹, fun j => ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
  have hrest : ((n j : ℤ) : WithTop ℤ) <
      v j (∑ i ∈ Finset.univ.erase j, q i ^ n i * (1 + s i ^ (N i + 1))⁻¹) :=
    lt_addValuation_sum_of_forall_lt (v j) _ _ _ (fun i hi => hoff i j (Finset.ne_of_mem_erase hi)) WithTop.coe_ne_top
  have hlt : v j (q j ^ n j * (1 + s j ^ (N j + 1))⁻¹) <
      v j (∑ i ∈ Finset.univ.erase j, q i ^ n i * (1 + s i ^ (N i + 1))⁻¹) := by
    rw [hdiag j]
    exact hrest
  rw [addValuation_add_eq_of_lt (v j) hlt, hdiag j]
end ReciprocityTheory.ChartRestriction.G.T0
