-- Prove2me | solution 1 for RegLearnGames.TotalRegret.display_2
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T10:15:54.702672+00:00
-- url     : https://prove2.me/submissions/28cad3fe-8e83-4638-b895-7ee055bfad15

import Mathlib
import Definitions.Def_RegLearnGames_TotalRegret_Setting

/- The marginal decomposition and hybrid helpers below adapt carlok's accepted
   Corollary 8 submission 974bb90b-3915-41fe-86d6-1af32970d1a9 (2026-10-12),
   public on Prove2Me under Apache-2.0. The index type is generalized here.
   The product L1 identity and the explicit display_2 conclusion are added here. -/
namespace P2MProductVariation
open Finset RegLearnGames.TotalRegret
variable {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

noncomputable def Pr (σ : ι → Fin d → ℝ) (i : ι) (r : {j // j ≠ i} → Fin d) : ℝ :=
  ∏ j : {j // j ≠ i}, σ j.1 (r j)

lemma decomp (σ : ι → Fin d → ℝ) (i : ι) (f : (ι → Fin d) → ℝ) :
    ∑ s, AGT.profileProb σ s * f s =
      ∑ a, σ i a * ∑ r, Pr σ i r * f ((Equiv.funSplitAt i (Fin d)).symm (a, r)) := by
  rw [← (Equiv.funSplitAt i (Fin d)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold AGT.profileProb Pr
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have h1 : (Equiv.funSplitAt i (Fin d)).symm (a, r) i = a := by
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  have h2 : ∀ j : {j // j ≠ i}, (Equiv.funSplitAt i (Fin d)).symm (a, r) j.1 = r j := by
    intro j; simp [Equiv.funSplitAt, Equiv.piSplitAt, j.2]
  simp only [h1, h2]
  ring

lemma Pr_update (σ : ι → Fin d → ℝ) (i : ι) (v : Fin d → ℝ) (r : {j // j ≠ i} → Fin d) :
    Pr (Function.update σ i v) i r = Pr σ i r := by
  unfold Pr
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Function.update_of_ne j.2]

lemma Pr_nonneg (σ : ι → Fin d → ℝ) (hσ : ∀ k, σ k ∈ stdSimplex ℝ (Fin d)) (i : ι)
    (r : {j // j ≠ i} → Fin d) : 0 ≤ Pr σ i r :=
  prod_nonneg fun j _ => (hσ j.1).1 _

lemma Pr_sum (σ : ι → Fin d → ℝ) (hσ : ∀ k, σ k ∈ stdSimplex ℝ (Fin d)) (i : ι) :
    ∑ r, Pr σ i r = 1 := by
  classical
  unfold Pr
  rw [← Fintype.prod_sum (fun (j : {j // j ≠ i}) (a : Fin d) => σ j.1 a)]
  exact prod_eq_one fun j _ => (hσ j.1).2

lemma one_coord (σ : ι → Fin d → ℝ) (hσ : ∀ k, σ k ∈ stdSimplex ℝ (Fin d)) (j : ι)
    (v : Fin d → ℝ) (hv : v ∈ stdSimplex ℝ (Fin d)) (f : (ι → Fin d) → ℝ)
    (hf : ∀ s, f s ∈ Set.Icc (0:ℝ) 1) :
    |∑ s, AGT.profileProb σ s * f s - ∑ s, AGT.profileProb (Function.update σ j v) s * f s|
      ≤ (1/2) * l1 (σ j - v) := by
  rw [decomp σ j, decomp _ j]
  simp only [Function.update_self, Pr_update]
  set K : Fin d → ℝ := fun a => ∑ r, Pr σ j r * f ((Equiv.funSplitAt j (Fin d)).symm (a, r))
  have hK0 : ∀ a, 0 ≤ K a := fun a =>
    sum_nonneg fun r _ => mul_nonneg (Pr_nonneg σ hσ j r) (hf _).1
  have hK1 : ∀ a, K a ≤ 1 := fun a => by
    calc K a ≤ ∑ r, Pr σ j r := sum_le_sum fun r _ =>
            mul_le_of_le_one_right (Pr_nonneg σ hσ j r) (hf _).2
      _ = 1 := Pr_sum σ hσ j
  have e : ∑ a, σ j a * K a - ∑ a, v a * K a = ∑ a, (σ j a - v a) * (K a - 1/2) := by
    have : ∑ a, (σ j a - v a) * (1/2:ℝ) = 0 := by
      rw [← sum_mul, sum_sub_distrib, (hσ j).2, hv.2]; ring
    simp only [mul_sub, sum_sub_distrib, this, sub_zero]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => by ring
  show |∑ a, σ j a * K a - ∑ a, v a * K a| ≤ _
  rw [e]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  unfold l1; rw [mul_sum]
  refine sum_le_sum fun a _ => ?_
  rw [abs_mul, Pi.sub_apply]
  have : |K a - 1/2| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith [hK0 a, hK1 a]
  calc |σ j a - v a| * |K a - 1/2| ≤ |σ j a - v a| * (1/2) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg _)
    _ = 1/2 * |σ j a - v a| := by ring

lemma multi_coord (f : (ι → Fin d) → ℝ) (hf : ∀ s, f s ∈ Set.Icc (0:ℝ) 1)
    (S : Finset (ι)) : ∀ σ τ : ι → Fin d → ℝ, (∀ k, σ k ∈ stdSimplex ℝ (Fin d)) →
      (∀ k, τ k ∈ stdSimplex ℝ (Fin d)) → (∀ k ∉ S, σ k = τ k) →
      |∑ s, AGT.profileProb σ s * f s - ∑ s, AGT.profileProb τ s * f s|
        ≤ (1/2) * ∑ k ∈ S, l1 (σ k - τ k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro σ τ _ _ h
    have : σ = τ := funext fun k => h k (by simp)
    subst this; simp
  | insert j S hj ih =>
    intro σ τ hσ hτ h
    set ρ := Function.update σ j (τ j)
    have hρ : ∀ k, ρ k ∈ stdSimplex ℝ (Fin d) := by
      intro k; by_cases hk : k = j
      · subst hk; simp [ρ, hτ]
      · simp [ρ, Function.update_of_ne hk, hσ]
    have hρτ : ∀ k ∉ S, ρ k = τ k := by
      intro k hk; by_cases hkj : k = j
      · subst hkj; simp [ρ]
      · simp only [ρ, Function.update_of_ne hkj]; exact h k (by simp [hkj, hk])
    have h1 := one_coord σ hσ j (τ j) (hτ j) f hf
    have h2 := ih ρ τ hρ hτ hρτ
    have e : ∑ k ∈ S, l1 (ρ k - τ k) = ∑ k ∈ S, l1 (σ k - τ k) := by
      refine sum_congr rfl fun k hk => ?_
      have : k ≠ j := fun h => hj (h ▸ hk)
      simp [ρ, Function.update_of_ne this]
    rw [e] at h2
    rw [sum_insert hj, mul_add]
    calc _ ≤ |∑ s, AGT.profileProb σ s * f s - ∑ s, AGT.profileProb ρ s * f s| +
          |∑ s, AGT.profileProb ρ s * f s - ∑ s, AGT.profileProb τ s * f s| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add h1 h2

lemma product_mass (σ : ι → Fin d → ℝ)
    (hσ : ∀ j, σ j ∈ stdSimplex ℝ (Fin d)) :
    ∑ s, AGT.profileProb σ s = 1 := by
  classical
  unfold AGT.profileProb
  rw [← Fintype.prod_sum]
  exact prod_eq_one fun j _ => (hσ j).2

lemma product_l1 (σ τ : ι → Fin d → ℝ)
    (hσ : ∀ j, σ j ∈ stdSimplex ℝ (Fin d))
    (hτ : ∀ j, τ j ∈ stdSimplex ℝ (Fin d)) :
    ∑ s, |AGT.profileProb σ s - AGT.profileProb τ s| ≤
      ∑ j, l1 (σ j - τ j) := by
  classical
  let D := fun s => AGT.profileProb σ s - AGT.profileProb τ s
  let f := fun s => if 0 ≤ D s then (1 : ℝ) else 0
  have hf : ∀ s, f s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s; dsimp [f]; split_ifs <;> constructor <;> norm_num
  have h := multi_coord f hf univ σ τ hσ hτ (by simp)
  have hmass : ∑ s, D s = 0 := by
    dsimp [D]
    rw [sum_sub_distrib, product_mass σ hσ, product_mass τ hτ, sub_self]
  have hid : ∀ s, |D s| = 2 * (D s * f s) - D s := by
    intro s
    by_cases hs : 0 ≤ D s
    · simp [f, hs, abs_of_nonneg hs]; ring
    · simp [f, hs, abs_of_neg (lt_of_not_ge hs)]
  have heq : ∑ s, |D s| =
      2 * (∑ s, AGT.profileProb σ s * f s - ∑ s, AGT.profileProb τ s * f s) := by
    simp_rw [hid]
    rw [sum_sub_distrib, ← mul_sum, hmass, sub_zero]
    congr 1
    simp [D, sub_mul, sum_sub_distrib]
  have habs := le_abs_self
    (∑ s, AGT.profileProb σ s * f s - ∑ s, AGT.profileProb τ s * f s)
  change ∑ s, |D s| ≤ _
  linarith

lemma util_repr {n : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (w : Fin n → Fin d → ℝ) (i : Fin n) (x : Fin d) :
    utilVec u w i x =
      ∑ r, Pr w i r * u i ((Equiv.funSplitAt i (Fin d)).symm (x, r)) := by
  unfold utilVec AGT.expectedPayoff
  rw [decomp _ i]
  simp [Pr_update, Pi.single_apply]

end P2MProductVariation

open Finset RegLearnGames.TotalRegret P2MProductVariation
theorem solution {n d : ℕ} (u : Fin n → (Fin n → Fin d) → ℝ)
    (hu : ∀ i s, u i s ∈ Set.Icc (0 : ℝ) 1)
    (w w' : Fin n → Fin d → ℝ) (hw : ∀ j, w j ∈ stdSimplex ℝ (Fin d))
    (hw' : ∀ j, w' j ∈ stdSimplex ℝ (Fin d)) (i : Fin n) :
    ‖utilVec u w i - utilVec u w' i‖ ≤
        ∑ s : {j : Fin n // j ≠ i} → Fin d, |∏ j, w j.1 (s j) - ∏ j, w' j.1 (s j)| ∧
      ∑ s : {j : Fin n // j ≠ i} → Fin d, |∏ j, w j.1 (s j) - ∏ j, w' j.1 (s j)| ≤
        ∑ j : {j : Fin n // j ≠ i}, l1 (w j.1 - w' j.1) := by
  classical
  constructor
  · apply (pi_norm_le_iff_of_nonneg (sum_nonneg fun _ _ => abs_nonneg _)).2
    intro x
    simp only [Pi.sub_apply, Real.norm_eq_abs, util_repr]
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ r, |Pr w i r * u i ((Equiv.funSplitAt i (Fin d)).symm (x, r)) -
          Pr w' i r * u i ((Equiv.funSplitAt i (Fin d)).symm (x, r))| :=
        abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        refine sum_le_sum fun r _ => ?_
        rw [← sub_mul, abs_mul, abs_of_nonneg (hu i _).1]
        exact mul_le_of_le_one_right (abs_nonneg _) (hu i _).2
  · exact product_l1 (fun j : {j : Fin n // j ≠ i} => w j.1)
      (fun j : {j : Fin n // j ≠ i} => w' j.1)
      (fun j => hw j.1) (fun j => hw' j.1)
