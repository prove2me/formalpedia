-- Prove2me | solution 1 for OnlineSetCover.Unweighted.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:12:34.635346+00:00
-- url     : https://prove2.me/submissions/89f5cd91-cca3-4ff0-aa5a-ff57d03f27ca

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover


namespace OnlineSetCover.Unweighted

lemma l22_k_pos {x : ℝ} {k : ℕ} (hlt : x < 1) (hk : IsAugExponent x k) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; have := hk.1; simp at this; linarith
  · exact h

lemma l22_bound {x : ℝ} {k : ℕ} (hlt : x < 1) (hk : IsAugExponent x k) :
    (2 : ℝ) ^ k * x ≤ 2 := by
  have hk1 := l22_k_pos hlt hk
  have := hk.2 (k - 1) (by omega)
  have e : (2:ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [e]; nlinarith

/-- the key real inequality -/
lemma l22_real (n : ℝ) (hn : 1 ≤ n) (W y K r : ℝ) (hW : 0 < W) (hy : 0 ≤ y) (hyW : y ≤ W)
    (hK : 1 ≤ K) (hKW : K * W ≤ 2) (hr : 4 * Real.log n ≤ r) (m : ℕ) (hm : (m:ℝ) = r) (z : ℝ) :
    n ^ (2 * (z + (K - 1) * y)) * (1 - y / W) ^ m ≤ n ^ (2 * z) := by
  have hn0 : 0 < n := by linarith
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  set u := y / W with hu
  have hu0 : 0 ≤ u := div_nonneg hy hW.le
  have hu1 : u ≤ 1 := (div_le_one hW).mpr hyW
  have e1 : n ^ (2 * (z + (K - 1) * y)) = n ^ (2 * z) * Real.exp (Real.log n * (2 * ((K - 1) * y))) := by
    rw [mul_add, Real.rpow_add hn0, Real.rpow_def_of_pos hn0 (2 * ((K-1)*y))]
  have e2 : (1 - u) ^ m ≤ Real.exp (m * -u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by simpa using Real.one_sub_le_exp_neg u) m
  have hd : 2 * ((K - 1) * y) ≤ 4 * u := by
    have : y = W * u := by rw [hu]; field_simp
    rw [this]
    nlinarith [mul_nonneg hW.le hu0]
  have h3 : Real.log n * (2 * ((K - 1) * y)) + m * -u ≤ 0 := by
    rw [hm]
    have := mul_le_mul_of_nonneg_left hd hlog
    nlinarith
  rw [e1]
  have hp : 0 < n ^ (2 * z) := Real.rpow_pos_of_pos hn0 _
  calc n ^ (2 * z) * Real.exp (Real.log n * (2 * ((K - 1) * y))) * (1 - u) ^ m
      ≤ n ^ (2 * z) * Real.exp (Real.log n * (2 * ((K - 1) * y))) * Real.exp (m * -u) := by
        apply mul_le_mul_of_nonneg_left e2; positivity
    _ = n ^ (2 * z) * Real.exp (Real.log n * (2 * ((K - 1) * y)) + m * -u) := by
        rw [Real.exp_add]; ring
    _ ≤ n ^ (2 * z) * 1 := by
        apply mul_le_mul_of_nonneg_left _ hp.le
        calc Real.exp _ ≤ Real.exp 0 := Real.exp_le_exp.mpr h3
          _ = 1 := Real.exp_zero
    _ = n ^ (2 * z) := mul_one _

theorem l22_core {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (hw : ∀ S, 0 < w S)
    (cover : Finset T) (j : E) (k : ℕ)
    (hlt : elementWeight inst w j < 1)
    (hk : IsAugExponent (elementWeight inst w j) k) :
    ∃ F : Finset T, F ⊆ inst.elemSets j ∧ F.card ≤ setCap (Fintype.card E) ∧
      potential inst (augment inst w j k) (cover ∪ F) ≤ potential inst w cover := by
  classical
  set W := elementWeight inst w j with hWdef
  have hk1 := l22_k_pos hlt hk
  have hKW := l22_bound hlt hk
  have hW : 0 < W := by
    have h1 := hk.1
    by_contra h; push_neg at h
    have : (2:ℝ) ^ k * W ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  set Sj := inst.elemSets j with hSj
  have hSjne : Sj.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : W = 0 := by rw [hWdef]; unfold elementWeight; rw [← hSj, h]; simp
    linarith
  set r := setCap (Fintype.card E) with hr
  let q : Sj → ℝ := fun S => w S / W
  have hqsum : ∑ S : Sj, q S = 1 := by
    simp only [q]
    rw [← Finset.sum_div, Finset.sum_coe_sort Sj (fun S => w S)]
    rw [hWdef]; unfold elementWeight; rw [← hSj]; exact div_self hW.ne'
  let p : (Fin r → Sj) → ℝ := fun x => ∏ t, q (x t)
  have hp0 : ∀ x, 0 ≤ p x := fun x => Finset.prod_nonneg (fun t _ => div_nonneg (hw _).le hW.le)
  have hpsum : ∑ x, p x = 1 := by
    have := Finset.prod_univ_sum (fun (_ : Fin r) => (Finset.univ : Finset Sj)) (fun _ S => q S)
    simp only [Fintype.piFinset_univ] at this
    simp only [p]; rw [← this, hqsum]; simp
  let Fx : (Fin r → Sj) → Finset T := fun x => Finset.univ.image (fun t => (x t : T))
  let g : (Fin r → Sj) → ℝ := fun x => potential inst (augment inst w j k) (cover ∪ Fx x)
  haveI : Nonempty Sj := hSjne.coe_sort
  obtain ⟨x0, -, hx0⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin r → Sj)) g
    Finset.univ_nonempty
  refine ⟨Fx x0, ?_, ?_, ?_⟩
  · intro S hS
    simp only [Fx, Finset.mem_image] at hS
    obtain ⟨t, -, rfl⟩ := hS
    exact (x0 t).2
  · calc (Fx x0).card ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
      _ = r := by simp
  · -- averaging
    have havg : ∑ x, p x * g x ≤ potential inst w cover := by
      set n : ℝ := (Fintype.card E : ℝ) with hn
      have hn1 : 1 ≤ n := by
        rw [hn]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨j⟩
      simp only [g, potential, Finset.sum_filter, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro i _
      by_cases hc : coveredBy inst cover i
      · have : ∀ x, ¬ ¬ coveredBy inst (cover ∪ Fx x) i := by
          intro x hx; apply hx
          obtain ⟨t, ht, htc⟩ := hc
          exact ⟨t, ht, Finset.mem_union_left _ htc⟩
        simp [this, hc]
      · rw [if_pos hc]
        let q' : Sj → ℝ := fun S => if (S : T) ∈ inst.elemSets i then 0 else q S
        have hcond : ∀ x, ¬ coveredBy inst (cover ∪ Fx x) i ↔ ∀ t, (x t : T) ∉ inst.elemSets i := by
          intro x
          constructor
          · intro h t ht
            exact h ⟨x t, ht, Finset.mem_union_right _ (by simp [Fx])⟩
          · rintro h ⟨S, hS, hSc⟩
            rcases Finset.mem_union.mp hSc with h1 | h1
            · exact hc ⟨S, hS, h1⟩
            · simp only [Fx, Finset.mem_image] at h1
              obtain ⟨t, -, rfl⟩ := h1
              exact h t hS
        set N' := n ^ (2 * elementWeight inst (augment inst w j k) i) with hN'
        have hterm : ∀ x, p x * (if ¬ coveredBy inst (cover ∪ Fx x) i then N' else 0) =
            N' * ∏ t, q' (x t) := by
          intro x
          by_cases h : ∀ t, (x t : T) ∉ inst.elemSets i
          · rw [if_pos ((hcond x).mpr h)]
            have : ∏ t, q' (x t) = p x := by
              apply Finset.prod_congr rfl; intro t _; simp only [q']; rw [if_neg (h t)]
            rw [this]; ring
          · rw [if_neg (fun h' => h ((hcond x).mp h'))]
            push_neg at h
            obtain ⟨t0, ht0⟩ := h
            have : ∏ t, q' (x t) = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ t0) (by simp only [q']; rw [if_pos ht0])
            rw [this]; ring
        rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
        have hprod : ∑ x : Fin r → Sj, ∏ t, q' (x t) = (∑ S, q' S) ^ r := by
          have := Finset.prod_univ_sum (fun (_ : Fin r) => (Finset.univ : Finset Sj)) (fun _ S => q' S)
          simp only [Fintype.piFinset_univ] at this
          rw [← this]; simp
        rw [hprod]
        set y : ℝ := ∑ S : Sj, if (S : T) ∈ inst.elemSets i then w S else 0 with hy
        have hq' : ∑ S, q' S = 1 - y / W := by
          rw [← hqsum, hy, Finset.sum_div, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro S _
          simp only [q']; split_ifs <;> ring
        have hy0 : 0 ≤ y := Finset.sum_nonneg (fun S _ => by split_ifs; exact (hw _).le; exact le_rfl)
        have hyW : y ≤ W := by
          have : y ≤ ∑ S : Sj, w S := Finset.sum_le_sum (fun S _ => by
            split_ifs; exact le_rfl; exact (hw _).le)
          rw [Finset.sum_coe_sort Sj (fun S => w S)] at this
          rw [hWdef]; unfold elementWeight; rw [← hSj]; exact this
        have hwi : elementWeight inst (augment inst w j k) i =
            elementWeight inst w i + ((2:ℝ) ^ k - 1) * y := by
          unfold elementWeight augment
          have h1 : ∀ S, (if S ∈ inst.elemSets j then (2:ℝ) ^ k * w S else w S) =
              w S + ((2:ℝ) ^ k - 1) * (if S ∈ Sj then w S else 0) := by
            intro S; rw [hSj]; split_ifs <;> ring
          simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
          congr 2
          rw [hy, Finset.sum_coe_sort Sj (fun S => if S ∈ inst.elemSets i then w S else 0)]
          rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_comm]
        rw [hq', hN', hwi]
        exact l22_real n hn1 W y (2 ^ k) (r : ℝ) hW hy0 hyW (one_le_pow₀ (by norm_num)) hKW
          (by rw [hr]; exact Nat.le_ceil _) r rfl _
    calc g x0 = ∑ x, p x * g x0 := by rw [← Finset.sum_mul, hpsum, one_mul]
      _ ≤ ∑ x, p x * g x :=
          Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hx0 x (Finset.mem_univ _)) (hp0 x))
      _ ≤ _ := havg
end OnlineSetCover.Unweighted

open OnlineSetCover.Unweighted


theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (w : T → ℝ) (hw : ∀ S, 0 < w S)
    (cover : Finset T) (j : E) (k : ℕ)
    (hlt : elementWeight inst w j < 1)
    (hk : IsAugExponent (elementWeight inst w j) k) :
    ∃ F : Finset T, F ⊆ inst.elemSets j ∧ F.card ≤ setCap (Fintype.card E) ∧
      potential inst (augment inst w j k) (cover ∪ F) ≤ potential inst w cover := by
  exact l22_core inst w hw cover j k hlt hk
