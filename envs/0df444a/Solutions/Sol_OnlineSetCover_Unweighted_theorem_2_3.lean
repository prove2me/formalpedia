-- Prove2me | solution 1 for OnlineSetCover.Unweighted.theorem_2_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T16:15:41.122541+00:00
-- url     : https://prove2.me/submissions/d10183fd-26e2-4c1f-9341-94cbe93bff43

import Mathlib
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_SetCoverInstance
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_coveredBy
import Definitions.Def_OnlinePrimalDual_OnlineSetCover_elementWeight
import Definitions.Def_OnlineSetCover_Unweighted_Algorithm
open OnlinePrimalDual.OnlineSetCover


namespace OnlineSetCover.Unweighted


lemma l21_aug_k_pos {x : ℝ} {k : ℕ} (hlt : x < 1) (hk : IsAugExponent x k) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; have := hk.1; simp at this; linarith
  · exact h

lemma l21_aug_bound {x : ℝ} {k : ℕ} (hlt : x < 1) (hk : IsAugExponent x k) :
    (2 : ℝ) ^ k * x ≤ 2 := by
  have hk1 := l21_aug_k_pos hlt hk
  have := hk.2 (k - 1) (by omega)
  have e : (2:ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [e]; nlinarith

lemma l21_step {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (OPT : Finset T) {s s' : State T} {j : E} {b : Bool}
    (hst : Step inst s j s' b) (hcov : coveredBy inst OPT j)
    (hpos : ∀ S, 0 < s.w S) (hle : ∀ S, s.w S ≤ 2) :
    (∀ S, 0 < s'.w S) ∧ (∀ S, s'.w S ≤ 2) ∧
      (if b then (1:ℝ) else 0) + ∑ S ∈ OPT, Real.logb 2 (s.w S) ≤
        ∑ S ∈ OPT, Real.logb 2 (s'.w S) := by
  cases hst with
  | noAug h => simp; exact ⟨hpos, hle⟩
  | aug k F hlt hk hF hcard hΦ =>
    have hk1 := l21_aug_k_pos hlt hk
    have hb := l21_aug_bound hlt hk
    have hSle : ∀ S ∈ inst.elemSets j, s.w S ≤ elementWeight inst s.w j := by
      intro S hS
      unfold elementWeight
      exact Finset.single_le_sum (f := s.w) (fun t _ => (hpos t).le) hS
    have h2k : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    have hge : ∀ S, s.w S ≤ augment inst s.w j k S := by
      intro S; unfold augment; split_ifs
      · nlinarith [hpos S]
      · exact le_rfl
    refine ⟨?_, ?_, ?_⟩
    · intro S; dsimp only; unfold augment; split_ifs
      · exact mul_pos (by positivity) (hpos S)
      · exact hpos S
    · intro S; dsimp only; unfold augment; split_ifs with hS
      · have := hSle S hS
        have : (2:ℝ) ^ k * s.w S ≤ 2 ^ k * elementWeight inst s.w j :=
          mul_le_mul_of_nonneg_left this (by positivity)
        linarith
      · exact hle S
    · obtain ⟨S0, hS0j, hS0O⟩ := hcov
      simp only [if_true]
      rw [← Finset.add_sum_erase _ _ hS0O, ← Finset.add_sum_erase _ _ hS0O]
      have h1 : 1 + Real.logb 2 (s.w S0) ≤ Real.logb 2 (augment inst s.w j k S0) := by
        unfold augment; rw [if_pos hS0j]
        rw [Real.logb_mul (by positivity) (hpos S0).ne', Real.logb_pow]
        simp
        have : (1:ℝ) ≤ k := by exact_mod_cast hk1
        linarith
      have h2 : ∑ S ∈ OPT.erase S0, Real.logb 2 (s.w S) ≤
          ∑ S ∈ OPT.erase S0, Real.logb 2 (augment inst s.w j k S) := by
        apply Finset.sum_le_sum; intro S _
        exact Real.logb_le_logb_of_le (by norm_num) (hpos S) (hge S)
      linarith

lemma l21_run {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (OPT : Finset T) {s s' : State T} {σ : List E} {a : ℕ}
    (hrun : RunFrom inst s σ s' a) (hcov : ∀ j ∈ σ, coveredBy inst OPT j)
    (hpos : ∀ S, 0 < s.w S) (hle : ∀ S, s.w S ≤ 2) :
    (∀ S, 0 < s'.w S) ∧ (∀ S, s'.w S ≤ 2) ∧
      (a : ℝ) + ∑ S ∈ OPT, Real.logb 2 (s.w S) ≤ ∑ S ∈ OPT, Real.logb 2 (s'.w S) := by
  induction hrun with
  | nil s => simp; exact ⟨hpos, hle⟩
  | @cons s s1 s2 j σ b a hst hr ih =>
    obtain ⟨p1, l1, i1⟩ := l21_step inst OPT hst (hcov j (by simp)) hpos hle
    obtain ⟨p2, l2, i2⟩ := ih (fun j hj => hcov j (by simp [hj])) p1 l1
    refine ⟨p2, l2, ?_⟩
    push_cast
    linarith

theorem l21_core {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (σ : List E) (OPT : Finset T)
    (hOPT : ∀ j ∈ σ, coveredBy inst OPT j)
    (s : State T) (a : ℕ) (hrun : Run inst σ s a) :
    (a : ℝ) ≤ (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by
  rcases Nat.eq_zero_or_pos (Fintype.card T) with hm | hm
  · -- no sets: σ must be empty
    have hOe : OPT = ∅ := by
      ext t; simp; have := Fintype.card_eq_zero_iff.mp hm; exact this.elim t
    cases σ with
    | nil =>
      unfold Run at hrun; cases hrun; simp [hOe]
    | cons j σ =>
      obtain ⟨t, _, ht⟩ := hOPT j (by simp)
      simp [hOe] at ht
  · have hmR : (0:ℝ) < Fintype.card T := by exact_mod_cast hm
    have hm1 : (1:ℝ) ≤ Fintype.card T := by exact_mod_cast hm
    have hpos : ∀ S, 0 < (initState T).w S := by
      intro S; simp [initState]; positivity
    have hle : ∀ S, (initState T).w S ≤ 2 := by
      intro S; simp only [initState]
      rw [div_le_iff₀ (by positivity)]; nlinarith
    obtain ⟨_, l2, i2⟩ := l21_run inst OPT hrun hOPT hpos hle
    have hfin : ∑ S ∈ OPT, Real.logb 2 (s.w S) ≤ OPT.card * 1 := by
      have : ∑ S ∈ OPT, Real.logb 2 (s.w S) ≤ ∑ S ∈ OPT, (1:ℝ) := by
        apply Finset.sum_le_sum; intro S _
        have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by linarith [‹∀ S, 0 < s.w S› S]) (l2 S)
        simpa using this
      simpa using this
    have hinit : ∑ S ∈ OPT, Real.logb 2 ((initState T).w S) =
        OPT.card * (-(Real.logb 2 (Fintype.card T) + 1)) := by
      simp only [initState, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [one_div, Real.logb_inv, Real.logb_mul (by norm_num) hmR.ne', Real.logb_self_eq_one (by norm_num)]
      ring
    rw [hinit] at i2
    nlinarith

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

lemma t23_K {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hn : 2 ≤ Fintype.card E) (s : State T)
    (hΦ : potential inst s.w s.cover ≤ potential inst (initState T).w (initState T).cover)
    (i : E) (hi : ¬ coveredBy inst s.cover i) : elementWeight inst s.w i < 1 := by
  classical
  by_contra hge; push_neg at hge
  set n : ℝ := (Fintype.card E : ℝ) with hndef
  have hn2 : (2:ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
  have hn0 : 0 < n := by linarith
  have hn1 : 1 < n := by linarith
  have hΦ0 : potential inst (initState T).w (initState T).cover =
      ∑ i, n ^ (2 * elementWeight inst (initState T).w i) := by
    unfold potential
    rw [Finset.filter_true_of_mem (fun i _ => by simp [coveredBy, initState])]
  have hterm : ∀ i, n ^ (2 * elementWeight inst (initState T).w i) ≤ n ∧
      (inst.elemSets i ≠ Finset.univ → n ^ (2 * elementWeight inst (initState T).w i) < n) := by
    intro i
    have hw : elementWeight inst (initState T).w i =
        (inst.elemSets i).card * (1 / (2 * (Fintype.card T : ℝ))) := by
      unfold elementWeight; simp [initState]
    have hc : (inst.elemSets i).card ≤ Fintype.card T := Finset.card_le_univ _
    have key : 2 * elementWeight inst (initState T).w i ≤ 1 ∧
        (inst.elemSets i ≠ Finset.univ → 2 * elementWeight inst (initState T).w i < 1) := by
      rw [hw]
      rcases Nat.eq_zero_or_pos (Fintype.card T) with hm | hm
      · simp [hm]
      · have hmR : (0:ℝ) < Fintype.card T := by exact_mod_cast hm
        have e : 2 * ((inst.elemSets i).card * (1 / (2 * (Fintype.card T : ℝ)))) =
            (inst.elemSets i).card / (Fintype.card T : ℝ) := by field_simp
        rw [e]
        constructor
        · rw [div_le_one hmR]; exact_mod_cast hc
        · intro hne
          have hx : ∃ x, x ∉ inst.elemSets i := by
            by_contra hh; push_neg at hh; exact hne (Finset.eq_univ_of_forall hh)
          obtain ⟨x, hx⟩ := hx
          have : (inst.elemSets i).card < Fintype.card T := Finset.card_lt_univ_of_notMem hx
          rw [div_lt_one hmR]; exact_mod_cast this
    constructor
    · calc n ^ (2 * elementWeight inst (initState T).w i) ≤ n ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1.le key.1
        _ = n := Real.rpow_one n
    · intro hne
      calc n ^ (2 * elementWeight inst (initState T).w i) < n ^ (1:ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt hn1 (key.2 hne)
        _ = n := Real.rpow_one n
  have hsingle : n ^ (2 * elementWeight inst s.w i) ≤ potential inst s.w s.cover := by
    unfold potential
    exact Finset.single_le_sum (f := fun i => n ^ (2 * elementWeight inst s.w i))
      (fun _ _ => (Real.rpow_pos_of_pos hn0 _).le) (by simp [hi])
  have hsq : n ^ (2:ℕ) ≤ n ^ (2 * elementWeight inst s.w i) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hn1.le (by push_cast; linarith)
  have hsumn : ∑ _i : E, n = n * n := by simp [Finset.sum_const, hndef]
  have hΦ0le : potential inst (initState T).w (initState T).cover ≤ n * n := by
    rw [hΦ0, ← hsumn]; exact Finset.sum_le_sum (fun i _ => (hterm i).1)
  have hall : ∀ i, inst.elemSets i = Finset.univ := by
    by_contra h; push_neg at h
    obtain ⟨i0, hi0⟩ := h
    have : ∑ i, n ^ (2 * elementWeight inst (initState T).w i) < ∑ _i : E, n :=
      Finset.sum_lt_sum (fun i _ => (hterm i).1) ⟨i0, Finset.mem_univ _, (hterm i0).2 hi0⟩
    rw [hsumn, ← hΦ0] at this
    nlinarith
  have hcov : s.cover = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro t ht; apply hi; exact ⟨t, by rw [hall i]; exact Finset.mem_univ _, ht⟩
  have hΦs : potential inst s.w s.cover = n * n ^ (2 * elementWeight inst s.w i) := by
    unfold potential
    rw [Finset.filter_true_of_mem (fun i' _ => by simp [coveredBy, hcov])]
    have : ∀ i', elementWeight inst s.w i' = elementWeight inst s.w i := by
      intro i'; unfold elementWeight; rw [hall i', hall i]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hndef]
  have hp2 : 0 < n ^ (2:ℕ) := by positivity
  have : n * n ^ (2:ℕ) ≤ n * n := by
    calc n * n ^ (2:ℕ) ≤ n * n ^ (2 * elementWeight inst s.w i) :=
          mul_le_mul_of_nonneg_left hsq hn0.le
      _ = potential inst s.w s.cover := hΦs.symm
      _ ≤ _ := hΦ
      _ ≤ _ := hΦ0le
  nlinarith

lemma t23_inv {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hn : 2 ≤ Fintype.card E)
    {s s' : State T} {σ : List E} {a : ℕ} (hrun : RunFrom inst s σ s' a)
    (hΦ : potential inst s.w s.cover ≤ potential inst (initState T).w (initState T).cover) :
    s.cover ⊆ s'.cover ∧ (∀ j ∈ σ, coveredBy inst s'.cover j) ∧
      s'.cover.card ≤ s.cover.card + setCap (Fintype.card E) * a := by
  induction hrun with
  | nil s => simp
  | @cons s s1 s2 j σ b a hst hr ih =>
    have step : potential inst s1.w s1.cover ≤ potential inst (initState T).w (initState T).cover ∧
        s.cover ⊆ s1.cover ∧ coveredBy inst s1.cover j ∧
        s1.cover.card ≤ s.cover.card + setCap (Fintype.card E) * (if b then 1 else 0) := by
      cases hst with
      | noAug h =>
        refine ⟨hΦ, subset_rfl, ?_, by simp⟩
        by_contra hc
        have := t23_K inst hn s hΦ j hc
        linarith
      | aug k F hlt hk hF hcard hΦ' =>
        refine ⟨le_trans hΦ' hΦ, Finset.subset_union_left, ?_, ?_⟩
        · by_contra hc
          have h1 := t23_K inst hn ⟨augment inst s.w j k, s.cover ∪ F⟩ (le_trans hΦ' hΦ) j hc
          have h2 : elementWeight inst (augment inst s.w j k) j = 2 ^ k * elementWeight inst s.w j := by
            unfold elementWeight augment
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro S hS; rw [if_pos hS]
          have := hk.1
          have h1' : elementWeight inst (augment inst s.w j k) j < 1 := h1
          linarith
        · simp only [if_true, mul_one]
          exact le_trans (Finset.card_union_le _ _) (by omega)
    obtain ⟨p1, sub1, c1, card1⟩ := step
    obtain ⟨sub2, c2, card2⟩ := ih p1
    refine ⟨subset_trans sub1 sub2, ?_, ?_⟩
    · intro j' hj'
      rcases List.mem_cons.mp hj' with rfl | h
      · obtain ⟨t, ht, htc⟩ := c1; exact ⟨t, ht, sub2 htc⟩
      · exact c2 j' h
    · rw [mul_add]; omega

lemma t23_exists {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (σ : List E) :
    ∀ (s : State T), (∀ S, 0 < s.w S) → (∀ j ∈ σ, (inst.elemSets j).Nonempty) →
      ∃ s' a, RunFrom inst s σ s' a := by
  induction σ with
  | nil => intro s _ _; exact ⟨s, 0, RunFrom.nil s⟩
  | cons j σ ih =>
    intro s hpos hne
    have hne' : ∀ j' ∈ σ, (inst.elemSets j').Nonempty := fun j' h => hne j' (by simp [h])
    by_cases h1 : 1 ≤ elementWeight inst s.w j
    · obtain ⟨s', a, hr⟩ := ih s hpos hne'
      exact ⟨s', _, RunFrom.cons (Step.noAug s j h1) hr⟩
    · push_neg at h1
      have hW : 0 < elementWeight inst s.w j := by
        unfold elementWeight
        exact Finset.sum_pos (fun t _ => hpos t) (hne j (by simp))
      have hex : ∃ k : ℕ, 1 < (2:ℝ) ^ k * elementWeight inst s.w j := by
        obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / elementWeight inst s.w j) (by norm_num : (1:ℝ) < 2)
        refine ⟨k, ?_⟩
        rw [div_lt_iff₀ hW] at hk; exact hk
      classical
      let k := Nat.find hex
      have hk : IsAugExponent (elementWeight inst s.w j) k :=
        ⟨Nat.find_spec hex, fun k' hk' => not_lt.mp (Nat.find_min hex hk')⟩
      obtain ⟨F, hF, hcard, hΦ⟩ := l22_core inst s.w hpos s.cover j k h1 hk
      have hpos' : ∀ S, 0 < (⟨augment inst s.w j k, s.cover ∪ F⟩ : State T).w S := by
        intro S; dsimp only; unfold augment; split_ifs
        · exact mul_pos (by positivity) (hpos S)
        · exact hpos S
      obtain ⟨s', a, hr⟩ := ih _ hpos' hne'
      exact ⟨s', _, RunFrom.cons (Step.aug s j k F h1 hk hF hcard hΦ) hr⟩

theorem t23_core {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hn : 2 ≤ Fintype.card E)
    (σ : List E) (OPT : Finset T) (hOPT : ∀ j ∈ σ, coveredBy inst OPT j) :
    (∃ (s : State T) (a : ℕ), Run inst σ s a) ∧
      ∀ (s : State T) (a : ℕ), Run inst σ s a →
        (∀ j ∈ σ, coveredBy inst s.cover j) ∧
          (s.cover.card : ℝ) ≤
            (setCap (Fintype.card E) : ℝ) * (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by
  constructor
  · have hpos : ∀ S, 0 < (initState T).w S := by
      intro S
      have : 0 < Fintype.card T := Fintype.card_pos_iff.mpr ⟨S⟩
      have : (0:ℝ) < Fintype.card T := by exact_mod_cast this
      simp [initState]; positivity
    have hne : ∀ j ∈ σ, (inst.elemSets j).Nonempty := by
      intro j hj; obtain ⟨t, ht, _⟩ := hOPT j hj; exact ⟨t, ht⟩
    exact t23_exists inst σ (initState T) hpos hne
  · intro s a hrun
    obtain ⟨_, hc, hcard⟩ := t23_inv inst hn hrun le_rfl
    refine ⟨hc, ?_⟩
    have ha := l21_core inst σ OPT hOPT s a hrun
    have h0 : (initState T).cover.card = 0 := by simp [initState]
    rw [h0, zero_add] at hcard
    have hcardR : (s.cover.card : ℝ) ≤ (setCap (Fintype.card E) : ℝ) * a := by exact_mod_cast hcard
    calc (s.cover.card : ℝ) ≤ (setCap (Fintype.card E) : ℝ) * a := hcardR
      _ ≤ (setCap (Fintype.card E) : ℝ) * ((OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2)) :=
          mul_le_mul_of_nonneg_left ha (Nat.cast_nonneg _)
      _ = _ := by ring
end OnlineSetCover.Unweighted

open OnlineSetCover.Unweighted


theorem solution {E T : Type*} [Fintype E] [Fintype T] [DecidableEq T]
    (inst : SetCoverInstance E T) (hn : 2 ≤ Fintype.card E)
    (σ : List E) (OPT : Finset T) (hOPT : ∀ j ∈ σ, coveredBy inst OPT j) :
    (∃ (s : State T) (a : ℕ), Run inst σ s a) ∧
      ∀ (s : State T) (a : ℕ), Run inst σ s a →
        (∀ j ∈ σ, coveredBy inst s.cover j) ∧
          (s.cover.card : ℝ) ≤
            (setCap (Fintype.card E) : ℝ) * (OPT.card : ℝ) * (Real.logb 2 (Fintype.card T) + 2) := by
  exact t23_core inst hn σ OPT hOPT
