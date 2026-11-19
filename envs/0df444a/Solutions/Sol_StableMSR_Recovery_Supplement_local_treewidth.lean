-- Prove2me | solution 1 for StableMSR.Recovery.Supplement.local_treewidth
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-18T21:20:02.668214+00:00
-- url     : https://prove2.me/submissions/c3757fc1-8fc9-4316-bdfa-69aa5793e35b

import Definitions.Def_StableMSR_Recovery_Supplement_Partitions
import Theorems.Thm_StableMSR_Recovery_interaction_balanced_separators
import Theorems.Thm_DvorakNorin2018_balanced_separators_treewidth
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
open scoped Classical
namespace StableMSR.Recovery.Supplement

theorem fold_net_properties {n : ℕ} (d : Point n → Point n → ℝ) (sym : ∀ x y, d x y = d y x) (R : ℝ)
    (W : Cluster n) (xs : List (Point n)) (contained : ∀ x ∈ xs, x ∈ W) (A : Cluster n)
    (sub : A ⊆ W) (sep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 2*R < d x y) :
    let B := xs.foldl (fun S x => if ∀ z ∈ S, 2*R < d x z then insert x S else S) A
    B ⊆ W ∧ ∀ x ∈ B, ∀ y ∈ B, x ≠ y → 2*R < d x y := by
  classical
  induction xs generalizing A with
  | nil => exact ⟨sub,sep⟩
  | cons x xs ih =>
    have tail : ∀ y ∈ xs, y ∈ W := fun y hy => contained y (by simp [hy])
    simp only [List.foldl_cons]
    by_cases far : ∀ z ∈ A, 2*R < d x z
    · rw [if_pos far]
      apply ih tail
      · exact Finset.insert_subset (contained x List.mem_cons_self) sub
      · intro a ha b hb ab
        rcases Finset.mem_insert.mp ha with hax|haA
        · rcases Finset.mem_insert.mp hb with hbx|hbB
          · exact (ab (hax.trans hbx.symm)).elim
          · simpa only [hax] using far _ hbB
        · rcases Finset.mem_insert.mp hb with hbx|hbB
          · rw [hbx,sym a x]; exact far _ haA
          · exact sep _ haA _ hbB ab
    · rw [if_neg far]; exact ih tail A sub sep

theorem prescribed_net_properties {n : ℕ} (d : Point n → Point n → ℝ) (sym : ∀ x y, d x y = d y x)
    (R : ℝ) (W : Cluster n) : greedyNet d R W ⊆ W ∧
    ∀ x ∈ greedyNet d R W, ∀ y ∈ greedyNet d R W, x ≠ y → 2*R < d x y := by
  exact fold_net_properties d sym R W (W.sort (· ≤ ·)) (by simp) ∅ (Finset.empty_subset _) (by simp)

theorem width_parameter_bound (ε : ℝ) (hε : 0 < ε) (h1 : ε < 1) :
    (widthBound ε : ℝ) ≤ 1274960 / ε^4 := by
  have sq : ε^2 ≤ 1 := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr h1.le)]
  have fourth : ε^4 ≤ 1 := by nlinarith [mul_nonneg (sq_nonneg ε) (sub_nonneg.mpr sq)]
  have den : 0 < ε^2 := by positivity
  have growth : growthConstant ε * ε^2 ≤ 161 := by
    unfold growthConstant
    field_simp
    nlinarith
  have pos : 0 ≤ growthConstant ε := by unfold growthConstant; positivity
  have non : 0 ≤ growthConstant ε * ε^2 := mul_nonneg pos den.le
  have growth2 : (growthConstant ε * ε^2)^2 ≤ 161^2 :=
    pow_le_pow_left₀ non growth 2
  have gr4 : growthConstant ε * ε^4 ≤ 161 := calc
    _ = (growthConstant ε * ε^2)*ε^2 := by ring
    _ ≤ (growthConstant ε * ε^2)*1 := mul_le_mul_of_nonneg_left sq non
    _ ≤ _ := by simpa using growth
  have ceil := (Nat.ceil_lt_add_one (show 0 ≤ 49*(growthConstant ε)^2+30*growthConstant ε by positivity)).le
  change (⌈49*(growthConstant ε)^2+30*growthConstant ε⌉₊:ℝ) ≤ _
  apply (le_div_iff₀ (by positivity)).mpr
  have step := mul_le_mul_of_nonneg_right ceil (show 0 ≤ ε^4 by positivity)
  nlinarith [growth2,gr4,fourth]

end StableMSR.Recovery.Supplement
open StableMSR.Recovery StableMSR.Recovery.Supplement
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      (∀ ε : ℝ, 0 < ε → ε < 1 → (widthBound ε : ℝ) ≤ C / ε ^ 4) ∧
      ∀ (n k : ℕ) (d : Point n → Point n → ℝ) (γ : ℝ) (O : Partition n),
        1 ≤ k → k < n → IsMetricArray d → 1 < γ → γ < 2 → Stable d k γ O →
        ∀ W : Cluster n, Aligned O W → diameter d W ≤ densityScale d O (γ - 1) →
          RobertsonSeymour1986.GM5.TreewidthLE
            (interactionGraph d (largestRadius d O) W) (widthBound (γ - 1)) := by
  refine ⟨1274960,by norm_num,width_parameter_bound,?_⟩
  intro n k d γ O hk hkn hd hγ hγ2 hO W _ hdiam
  let N := greedyNet d (largestRadius d O) W
  have sym (x y : Point n) : d x y = d y x := by
    obtain ⟨m, hm⟩ := hd
    letI := m
    rw [← hm x y,← hm y x,dist_comm]
  have net := prescribed_net_properties d sym (largestRadius d O) W
  obtain ⟨a,ha,hs⟩ := StableMSR.Recovery.interaction_balanced_separators d hd k ⟨hk,hkn.le⟩ γ ⟨hγ,hγ2⟩ hkn O hO W N net.1 hdiam net.2
  have separators : Havens.HasBalancedSeparations (interactionGraph d (largestRadius d O) W) a := hs
  obtain ⟨T,hT,t,X,hdec,hwidth⟩ := DvorakNorin2018.balanced_separators_treewidth _ a separators
  exact ⟨T,hT,t,X,hdec,fun i => (hwidth i).trans (by omega)⟩
