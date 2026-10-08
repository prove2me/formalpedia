-- Prove2me | solution 1 for WeightedMajority.InfinitePool.theorem_4_1_part_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T19:04:43.288304+00:00
-- url     : https://prove2.me/submissions/4fe6bf55-ecc7-410b-9c59-dbfc98784eaa

import Mathlib
import Definitions.Def_WeightedMajority_InfinitePool_IsWMI2Run



namespace WeightedMajority.InfinitePool

lemma wmi_cnt_succ {T : ℕ} (P : Fin T → Prop) [DecidablePred P] (n : ℕ) (h : n < T) :
    (Finset.univ.filter (fun s : Fin T => s.val < n + 1 ∧ P s)).card =
      (Finset.univ.filter (fun s : Fin T => s.val < n ∧ P s)).card +
        (if P ⟨n, h⟩ then 1 else 0) := by
  simp only [Finset.card_filter]
  have key : ∀ s : Fin T, (if s.val < n + 1 ∧ P s then 1 else 0) =
      (if s.val < n ∧ P s then 1 else 0) + (if s = ⟨n, h⟩ then (if P ⟨n, h⟩ then 1 else 0) else 0) := by
    intro s
    by_cases hs : s = ⟨n, h⟩
    · subst hs; simp
    · have hne : s.val ≠ n := fun e => hs (Fin.ext e)
      have : (s.val < n + 1) ↔ (s.val < n) := by omega
      simp [hs, this]
  rw [Finset.sum_congr rfl (fun s _ => key s), Finset.sum_add_distrib]
  simp

lemma wmi_mb_succ {T : ℕ} (prediction label : Fin T → Bool) (n : ℕ) (h : n < T) :
    mistakesBefore prediction label (n + 1) =
      mistakesBefore prediction label n +
        (if prediction ⟨n, h⟩ ≠ label ⟨n, h⟩ then 1 else 0) :=
  wmi_cnt_succ (fun s => prediction s ≠ label s) n h

lemma wmi_mb_zero {T : ℕ} (prediction label : Fin T → Bool) :
    mistakesBefore prediction label 0 = 0 := by
  simp [mistakesBefore]

lemma wmi_u_pos {β : ℝ} (hβ0 : 0 ≤ β) : 0 < u β := by unfold u; linarith
lemma wmi_u_lt {β : ℝ} (hβ1 : β < 1) : u β < 1 := by unfold u; linarith

lemma wmi_What1_pos {W What : ℕ+ → ℝ} (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i) : 0 < What 1 := by
  have h1 := hWhat_tail 1
  have e : (fun j : ℕ+ => if 1 ≤ j then W j else 0) = W := by
    funext j; simp
  rw [e] at h1
  exact lt_of_lt_of_le (hW_sum.tsum_pos (fun i => (hW_pos i).le) 1 (hW_pos 1)) h1

lemma wmi_slack_nonneg {β : ℝ} {What : ℕ+ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ha : 0 < What 1)
    (m : ℕ) : 0 ≤ slack β What m := by
  unfold slack
  have := wmi_u_pos hβ0
  have : 0 < 1 - β := by linarith
  positivity

lemma wmi_slack_anti {β : ℝ} {What : ℕ+ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ha : 0 < What 1)
    (m : ℕ) : slack β What (m + 1) ≤ slack β What m := by
  unfold slack
  have hu := wmi_u_pos hβ0
  have hu1 := wmi_u_lt hβ1
  have hb : 0 < 1 - β := by linarith
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hp : 0 ≤ u β ^ (m + 1) * What 1 := by positivity
  rw [pow_succ]
  have e1 : u β ^ (m + 1) * u β * What 1 * ((1 - β) * (↑m + 1) * (↑m + 2)) =
      u β * (u β ^ (m + 1) * What 1) * ((1 - β) * (↑m + 1) * (↑m + 2)) := by ring
  have e2 : u β ^ (m + 1) * What 1 * ((1 - β) * (↑m + 1 + 1) * (↑m + 1 + 2)) =
      (u β ^ (m + 1) * What 1) * ((1 - β) * (↑m + 1) * (↑m + 2)) +
      (u β ^ (m + 1) * What 1) * ((1 - β) * (↑m + 2) * 2) := by ring
  rw [e1, e2]
  have h3 : 0 ≤ (u β ^ (m + 1) * What 1) * ((1 - β) * (↑m + 1) * (↑m + 2)) := by positivity
  have h4 : 0 ≤ (u β ^ (m + 1) * What 1) * ((1 - β) * (↑m + 2) * 2) := by positivity
  nlinarith

lemma wmi_part1 {β : ℝ} {W What : ℕ+ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    {T : ℕ} {x : Fin T → ℕ+ → Bool} {label : Fin T → Bool}
    {prediction : Fin T → Bool} {w : ℕ → ℕ+ → ℝ} {l : ℕ → ℕ}
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ n : ℕ, n < T →
      What (Nat.succPNat (l n)) ≤ slack β What (mistakesBefore prediction label n) ∧
      ∀ l' < l n, slack β What (mistakesBefore prediction label n) < What (Nat.succPNat l') := by
  have ha := wmi_What1_pos hW_pos hW_sum hWhat_tail
  intro n
  induction n with
  | zero =>
    intro _
    rw [wmi_mb_zero]
    exact ⟨hrun.init_size, hrun.init_size_min⟩
  | succ n ih =>
    intro hn
    have hn' : n < T := by omega
    obtain ⟨ih1, ih2⟩ := ih hn'
    rw [wmi_mb_succ prediction label n hn']
    by_cases hp : prediction ⟨n, hn'⟩ = label ⟨n, hn'⟩
    · have hl := hrun.size_keep ⟨n, hn'⟩ hp
      simp only at hl
      simp only [hp, ne_eq, not_true_eq_false, if_false, add_zero]
      rw [hl]
      exact ⟨ih1, ih2⟩
    · have hl1 := hrun.size_grow ⟨n, hn'⟩ hp
      have hl2 := hrun.size_grow_min ⟨n, hn'⟩ hp
      have hl3 := hrun.size_grow_le ⟨n, hn'⟩ hp
      simp only at hl1 hl2 hl3
      rw [wmi_mb_succ prediction label n hn'] at hl1 hl2
      simp only [hp, ne_eq, not_false_eq_true, if_true] at hl1 hl2 ⊢
      refine ⟨hl1, fun l' hl' => ?_⟩
      by_cases hc : l' < l n
      · exact lt_of_le_of_lt (wmi_slack_anti hβ0 hβ1 ha _) (ih2 l' hc)
      · exact hl2 l' (by omega) hl'

lemma wmi_Om_eq (W : ℕ+ → ℝ) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ) (t k : ℕ) :
    omega W w l t (Nat.succPNat k) =
      if k < l t then w t (Nat.succPNat k) else W (Nat.succPNat k) := by
  unfold omega
  simp [Nat.succPNat_coe, Nat.succ_le_iff]

lemma wmi_V_summable {W : ℕ+ → ℝ} (hW_sum : Summable W) :
    Summable (fun n : ℕ => W (Nat.succPNat n)) := by
  have := (Equiv.summable_iff (f := W) Equiv.pnatEquivNat.symm).mpr hW_sum
  simpa [Function.comp_def, Equiv.pnatEquivNat_symm_apply] using this

lemma wmi_Om_tail (W : ℕ+ → ℝ) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ) (t n : ℕ) :
    omega W w l t (Nat.succPNat (n + l t)) = W (Nat.succPNat (n + l t)) := by
  rw [wmi_Om_eq]; simp

lemma wmi_Om_summable {W : ℕ+ → ℝ} (hW_sum : Summable W) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ) (t : ℕ) :
    Summable (fun k : ℕ => omega W w l t (Nat.succPNat k)) := by
  rw [← summable_nat_add_iff (l t)]
  have : (fun n : ℕ => omega W w l t (Nat.succPNat (n + l t))) =
      fun n : ℕ => W (Nat.succPNat (n + l t)) := by
    funext n; exact wmi_Om_tail W w l t n
  rw [this]
  exact (summable_nat_add_iff (l t)).mpr (wmi_V_summable hW_sum)

lemma wmi_Om_split {W : ℕ+ → ℝ} (hW_sum : Summable W) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ) (t : ℕ) :
    ∑' k : ℕ, omega W w l t (Nat.succPNat k) =
      (∑ k ∈ Finset.range (l t), w t (Nat.succPNat k)) +
        ∑' n : ℕ, W (Nat.succPNat (n + l t)) := by
  have h := (wmi_Om_summable hW_sum w l t).sum_add_tsum_nat_add (l t)
  rw [← h]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    rw [wmi_Om_eq, if_pos (Finset.mem_range.mp hk)]
  · apply tsum_congr
    intro n
    exact wmi_Om_tail W w l t n

lemma wmi_tail_le {W What : ℕ+ → ℝ} (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i) (L : ℕ) :
    ∑' n : ℕ, W (Nat.succPNat (n + L)) ≤ What (Nat.succPNat L) := by
  have h := hWhat_tail (Nat.succPNat L)
  rw [← Equiv.tsum_eq Equiv.pnatEquivNat.symm] at h
  simp only [Equiv.pnatEquivNat_symm_apply] at h
  have hfe : (fun n : ℕ => if Nat.succPNat L ≤ Nat.succPNat n then W (Nat.succPNat n) else 0) =
      fun n : ℕ => if L ≤ n then W (Nat.succPNat n) else 0 := by
    funext n
    have : Nat.succPNat L ≤ Nat.succPNat n ↔ L ≤ n := by
      rw [← PNat.coe_le_coe]; simp
    simp only [this]
  rw [hfe] at h
  have hfs : Summable (fun n : ℕ => if L ≤ n then W (Nat.succPNat n) else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (wmi_V_summable hW_sum)
    · split_ifs
      · exact (hW_pos _).le
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact (hW_pos _).le
  have h2 := hfs.sum_add_tsum_nat_add L
  have h3 : ∑ i ∈ Finset.range L, (if L ≤ i then W (Nat.succPNat i) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
  have h4 : (fun i : ℕ => if L ≤ i + L then W (Nat.succPNat (i + L)) else 0) =
      fun i : ℕ => W (Nat.succPNat (i + L)) := by
    funext i; rw [if_pos (by omega)]
  rw [h3, h4, zero_add] at h2
  rw [h2]; exact h

lemma wmi_Om_step {β : ℝ} {W What : ℕ+ → ℝ} {T : ℕ} {x : Fin T → ℕ+ → Bool}
    {label prediction : Fin T → Bool} {w : ℕ → ℕ+ → ℝ} {l : ℕ → ℕ}
    (hrun : IsWMI2Run β W What x label prediction w l) (n : ℕ) (hn : n < T) (k : ℕ) :
    omega W w l (n + 1) (Nat.succPNat k) =
      omega W w l n (Nat.succPNat k) -
        (if prediction ⟨n, hn⟩ ≠ label ⟨n, hn⟩ ∧ k < l n ∧
            x ⟨n, hn⟩ (Nat.succPNat k) ≠ label ⟨n, hn⟩
          then (1 - β) * w n (Nat.succPNat k) else 0) := by
  have hmono : l n ≤ l (n + 1) := by
    by_cases hp : prediction ⟨n, hn⟩ = label ⟨n, hn⟩
    · have := hrun.size_keep ⟨n, hn⟩ hp
      simp only at this; omega
    · exact hrun.size_grow_le ⟨n, hn⟩ hp
  rw [wmi_Om_eq, wmi_Om_eq]
  by_cases hk : k < l n
  · have hk' : k < l (n + 1) := by omega
    have hu := hrun.update_weight ⟨n, hn⟩ (Nat.succPNat k)
      (by simp [Nat.succPNat_coe]; omega)
    simp only at hu
    rw [if_pos hk, if_pos hk', hu]
    by_cases hc : prediction ⟨n, hn⟩ ≠ label ⟨n, hn⟩ ∧ x ⟨n, hn⟩ (Nat.succPNat k) ≠ label ⟨n, hn⟩
    · rw [if_pos hc, if_pos ⟨hc.1, hk, hc.2⟩]; ring
    · rw [if_neg hc, if_neg (by tauto)]; ring
  · have hc : ¬ (prediction ⟨n, hn⟩ ≠ label ⟨n, hn⟩ ∧ k < l n ∧
        x ⟨n, hn⟩ (Nat.succPNat k) ≠ label ⟨n, hn⟩) := fun h => hk h.2.1
    rw [if_neg hc, if_neg hk]
    by_cases hk' : k < l (n + 1)
    · have := hrun.activate_weight ⟨n, hn⟩ (Nat.succPNat k) (by simp; omega) (by simp; omega)
      simp only at this
      rw [if_pos hk', this]; ring
    · rw [if_neg hk']; ring

lemma wmi_bool_key : ∀ a b y : Bool, b ≠ y → (a ≠ y ↔ a = b) := by decide

lemma wmi_part2_nat {β : ℝ} {W What : ℕ+ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    {T : ℕ} {x : Fin T → ℕ+ → Bool} {label : Fin T → Bool}
    {prediction : Fin T → Bool} {w : ℕ → ℕ+ → ℝ} {l : ℕ → ℕ}
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ n : ℕ, n ≤ T →
      ∑' k : ℕ, omega W w l n (Nat.succPNat k) ≤
        (2 - 1 / ((mistakesBefore prediction label n : ℝ) + 1)) *
          u β ^ mistakesBefore prediction label n * What 1 := by
  have ha := wmi_What1_pos hW_pos hW_sum hWhat_tail
  have hu := wmi_u_pos hβ0
  have hb : 0 < 1 - β := by linarith
  intro n
  induction n with
  | zero =>
    intro _
    rw [wmi_mb_zero, wmi_Om_split hW_sum]
    have h1 := (wmi_V_summable hW_sum).sum_add_tsum_nat_add (l 0)
    have h2 : ∑' n : ℕ, W (Nat.succPNat n) = ∑' j : ℕ+, W j := by
      have := Equiv.tsum_eq Equiv.pnatEquivNat.symm W
      simpa [Equiv.pnatEquivNat_symm_apply] using this
    have h3 := hWhat_tail 1
    have e : (fun j : ℕ+ => if 1 ≤ j then W j else 0) = W := by
      funext j; simp
    rw [e] at h3
    have h4 : (∑ k ∈ Finset.range (l 0), w 0 (Nat.succPNat k)) =
        ∑ k ∈ Finset.range (l 0), W (Nat.succPNat k) := by
      apply Finset.sum_congr rfl
      intro k hk
      apply hrun.init_weight
      simp [Nat.succPNat_coe]; have := Finset.mem_range.mp hk; omega
    rw [h4]
    simp
    linarith
  | succ n ih =>
    intro hn1
    have hn : n < T := by omega
    have hb0 := ih (by omega)
    rw [wmi_mb_succ prediction label n hn]
    have hs : Summable (fun k : ℕ => omega W w l n (Nat.succPNat k)) :=
      wmi_Om_summable hW_sum w l n
    by_cases hp : prediction ⟨n, hn⟩ = label ⟨n, hn⟩
    · have : (fun k : ℕ => omega W w l (n + 1) (Nat.succPNat k)) =
          fun k : ℕ => omega W w l n (Nat.succPNat k) := by
        funext k; rw [wmi_Om_step hrun n hn k]; simp [hp]
      rw [this]
      simpa [hp] using hb0
    · -- mistake
      have hp' : prediction ⟨n, hn⟩ ≠ label ⟨n, hn⟩ := hp
      simp only [hp', ne_eq, not_false_eq_true, if_true]
      obtain ⟨m, hm⟩ : ∃ m, m = mistakesBefore prediction label n := ⟨_, rfl⟩
      rw [← hm] at hb0 ⊢
      have hP1 := (wmi_part1 hβ0 hβ1 hW_pos hW_sum hWhat_tail hrun) n hn
      rw [← hm] at hP1
      have hI := wmi_tail_le hW_pos hW_sum hWhat_tail (l n)
      have hIs : ∑' j : ℕ, W (Nat.succPNat (j + l n)) ≤ slack β What m := le_trans hI hP1.1
      -- g
      set g : ℕ → ℝ := fun k => if k < l n ∧ x ⟨n, hn⟩ (Nat.succPNat k) ≠ label ⟨n, hn⟩
          then (1 - β) * w n (Nat.succPNat k) else 0 with hg
      have hstep : (fun k : ℕ => omega W w l (n + 1) (Nat.succPNat k)) =
          fun k : ℕ => omega W w l n (Nat.succPNat k) - g k := by
        funext k
        rw [wmi_Om_step hrun n hn k]
        simp [hg, hp']
      have hgsum : Summable g := by
        apply summable_of_ne_finset_zero (s := Finset.range (l n))
        intro k hk
        have : ¬ k < l n := fun h => hk (Finset.mem_range.mpr h)
        simp [hg, this]
      have hgt : ∑' k, g k = ∑ k ∈ Finset.range (l n), g k := by
        apply tsum_eq_sum
        intro k hk
        have : ¬ k < l n := fun h => hk (Finset.mem_range.mpr h)
        simp [hg, this]
      rw [hstep, hs.tsum_sub hgsum, hgt]
      -- bad
      set bad : ℝ := ∑ k ∈ Finset.range (l n),
          (if x ⟨n, hn⟩ (Nat.succPNat k) ≠ label ⟨n, hn⟩ then w n (Nat.succPNat k) else 0) with hbad
      have hgb : ∑ k ∈ Finset.range (l n), g k = (1 - β) * bad := by
        rw [hbad, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have := Finset.mem_range.mp hk
        simp only [hg, this, true_and]
        split_ifs <;> simp
      rw [hgb]
      have hsplit := wmi_Om_split hW_sum w l n
      rw [hsplit] at hb0 ⊢
      set A : ℝ := ∑ k ∈ Finset.range (l n), w n (Nat.succPNat k) with hA
      set I : ℝ := ∑' j : ℕ, W (Nat.succPNat (j + l n)) with hI'
      set s : ℝ := slack β What m with hs'
      have hqA : A = activeVote x w l ⟨n, hn⟩ true + activeVote x w l ⟨n, hn⟩ false := by
        unfold activeVote
        rw [hA, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        cases x ⟨n, hn⟩ (Nat.succPNat k) <;> simp
      have hbq : bad = activeVote x w l ⟨n, hn⟩ (prediction ⟨n, hn⟩) := by
        unfold activeVote
        rw [hbad]
        apply Finset.sum_congr rfl
        intro k _
        simp only [wmi_bool_key _ _ _ hp']
      have hforce : 2 * bad ≥ A - s := by
        have hpt := hrun.predict_one ⟨n, hn⟩
        have hpz := hrun.predict_zero ⟨n, hn⟩
        have hpt' : activeVote x w l ⟨n, hn⟩ false + s <
            activeVote x w l ⟨n, hn⟩ true → prediction ⟨n, hn⟩ = true := by
          intro h; apply hpt; simp only [Fin.val_mk, ← hm]; exact h
        have hpz' : activeVote x w l ⟨n, hn⟩ true + s <
            activeVote x w l ⟨n, hn⟩ false → prediction ⟨n, hn⟩ = false := by
          intro h; apply hpz; simp only [Fin.val_mk, ← hm]; exact h
        rw [hbq]
        cases hy : label ⟨n, hn⟩
        · have hpf : prediction ⟨n, hn⟩ = true := by
            cases h : prediction ⟨n, hn⟩
            · exact absurd (h.trans hy.symm) hp
            · rfl
          rw [hpf]
          have : ¬ (activeVote x w l ⟨n, hn⟩ true + s < activeVote x w l ⟨n, hn⟩ false) :=
            fun h => by have := hpz' h; rw [hpf] at this; exact Bool.noConfusion this
          rw [hqA]; push_neg at this; linarith
        · have hpf : prediction ⟨n, hn⟩ = false := by
            cases h : prediction ⟨n, hn⟩
            · rfl
            · exact absurd (h.trans hy.symm) hp
          rw [hpf]
          have : ¬ (activeVote x w l ⟨n, hn⟩ false + s < activeVote x w l ⟨n, hn⟩ true) :=
            fun h => by have := hpt' h; rw [hpf] at this; exact Bool.noConfusion this
          rw [hqA]; push_neg at this; linarith
      have hs_eq : (1 - β) * s = u β ^ (m + 1) * What 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
        rw [hs']; unfold slack
        have : (0:ℝ) < 1 - β := hb
        field_simp
      have hu' : u β = (1 + β) / 2 := rfl
      have hI0 : I ≤ s := hIs
      have h1 : A + I - (1 - β) * bad ≤ u β * (A + I) + (1 - β) * s := by
        rw [hu']
        nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hforce), mul_nonneg hb.le (sub_nonneg.mpr hI0)]
      have h2 : u β * (A + I) ≤ u β * ((2 - 1 / ((m : ℝ) + 1)) * u β ^ m * What 1) :=
        mul_le_mul_of_nonneg_left hb0 hu.le
      have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
      have h3 : u β * ((2 - 1 / ((m : ℝ) + 1)) * u β ^ m * What 1) +
          u β ^ (m + 1) * What 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) =
          (2 - 1 / (((m + 1 : ℕ) : ℝ) + 1)) * u β ^ (m + 1) * What 1 := by
        push_cast
        rw [pow_succ]
        field_simp
        ring
      rw [hs_eq] at h1
      linarith

lemma wmi_inv {β : ℝ} {W What : ℕ+ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hW_pos : ∀ i, 0 < W i)
    {T : ℕ} {x : Fin T → ℕ+ → Bool} {label : Fin T → Bool}
    {prediction : Fin T → Bool} {w : ℕ → ℕ+ → ℝ} {l : ℕ → ℕ}
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ n : ℕ, n ≤ T → ∀ k < l n,
      W (Nat.succPNat k) *
        β ^ (Finset.univ.filter (fun s : Fin T => s.val < n ∧
          (prediction s ≠ label s ∧ x s (Nat.succPNat k) ≠ label s))).card
        ≤ w n (Nat.succPNat k) := by
  intro n
  induction n with
  | zero =>
    intro _ k hk
    have := hrun.init_weight (Nat.succPNat k) (by simp [Nat.succPNat_coe]; omega)
    rw [this]
    simp
  | succ n ih =>
    intro hn1 k hk
    have hn : n < T := by omega
    rw [wmi_cnt_succ (fun s => prediction s ≠ label s ∧ x s (Nat.succPNat k) ≠ label s) n hn]
    by_cases hkl : k < l n
    · have hu := hrun.update_weight ⟨n, hn⟩ (Nat.succPNat k)
        (by simp [Nat.succPNat_coe]; omega)
      simp only at hu
      rw [hu]
      have ih' := ih (by omega) k hkl
      by_cases hc : prediction ⟨n, hn⟩ ≠ label ⟨n, hn⟩ ∧ x ⟨n, hn⟩ (Nat.succPNat k) ≠ label ⟨n, hn⟩
      · have e1 : (if (fun s => prediction s ≠ label s ∧ x s (Nat.succPNat k) ≠ label s) ⟨n, hn⟩
            then 1 else 0) = 1 := if_pos hc
        rw [e1, if_pos hc, pow_succ]
        calc _ = β * (W (Nat.succPNat k) * β ^ (Finset.univ.filter (fun s : Fin T => s.val < n ∧
              (prediction s ≠ label s ∧ x s (Nat.succPNat k) ≠ label s))).card) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left ih' hβ0
      · have e1 : (if (fun s => prediction s ≠ label s ∧ x s (Nat.succPNat k) ≠ label s) ⟨n, hn⟩
            then 1 else 0) = 0 := if_neg hc
        rw [e1, if_neg hc, add_zero]
        exact ih'
    · have := hrun.activate_weight ⟨n, hn⟩ (Nat.succPNat k) (by simp; omega) (by simp; omega)
      simp only at this
      rw [this]
      exact le_trans (mul_le_mul_of_nonneg_left (pow_le_one₀ hβ0 hβ1.le) (hW_pos _).le)
        (le_of_eq (mul_one _))

lemma wmi_lower {β : ℝ} {W What : ℕ+ → ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    {T : ℕ} {x : Fin T → ℕ+ → Bool} {label : Fin T → Bool}
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    {prediction : Fin T → Bool} {w : ℕ → ℕ+ → ℝ} {l : ℕ → ℕ}
    (hrun : IsWMI2Run β W What x label prediction w l) (k : ℕ) :
    W (Nat.succPNat k) * β ^ mi (Nat.succPNat k) ≤
      ∑' j : ℕ, omega W w l T (Nat.succPNat j) := by
  have hinv := wmi_inv hβ0 hβ1 hW_pos hrun T le_rfl
  have hc : ∀ j, (Finset.univ.filter (fun s : Fin T => s.val < T ∧
          (prediction s ≠ label s ∧ x s (Nat.succPNat j) ≠ label s))).card ≤ mi (Nat.succPNat j) := by
    intro j
    refine le_trans (Finset.card_le_card ?_) (hmi _)
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs.2.2
  have hpow : ∀ j, β ^ mi (Nat.succPNat j) ≤ β ^ (Finset.univ.filter (fun s : Fin T => s.val < T ∧
          (prediction s ≠ label s ∧ x s (Nat.succPNat j) ≠ label s))).card :=
    fun j => pow_le_pow_of_le_one hβ0 hβ1.le (hc j)
  have hwnn : ∀ j < l T, 0 ≤ w T (Nat.succPNat j) := by
    intro j hj
    exact le_trans (by have := hW_pos (Nat.succPNat j); positivity) (hinv j hj)
  rw [wmi_Om_split hW_sum]
  have hI0 : 0 ≤ ∑' n : ℕ, W (Nat.succPNat (n + l T)) :=
    tsum_nonneg (fun n => (hW_pos _).le)
  by_cases hk : k < l T
  · have h1 : w T (Nat.succPNat k) ≤ ∑ j ∈ Finset.range (l T), w T (Nat.succPNat j) :=
      Finset.single_le_sum (f := fun j => w T (Nat.succPNat j))
        (fun j hj => hwnn j (Finset.mem_range.mp hj)) (Finset.mem_range.mpr hk)
    have h2 := hinv k hk
    have h3 : W (Nat.succPNat k) * β ^ mi (Nat.succPNat k) ≤
        W (Nat.succPNat k) * β ^ (Finset.univ.filter (fun s : Fin T => s.val < T ∧
          (prediction s ≠ label s ∧ x s (Nat.succPNat k) ≠ label s))).card :=
      mul_le_mul_of_nonneg_left (hpow k) (hW_pos _).le
    linarith
  · have hA0 : 0 ≤ ∑ j ∈ Finset.range (l T), w T (Nat.succPNat j) :=
      Finset.sum_nonneg (fun j hj => hwnn j (Finset.mem_range.mp hj))
    have hsm : Summable (fun n : ℕ => W (Nat.succPNat (n + l T))) :=
      (summable_nat_add_iff (l T)).mpr (wmi_V_summable hW_sum)
    have h1 := hsm.le_tsum (k - l T) (fun j _ => (hW_pos _).le)
    have e : k - l T + l T = k := by omega
    rw [e] at h1
    have h3 : W (Nat.succPNat k) * β ^ mi (Nat.succPNat k) ≤ W (Nat.succPNat k) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hβ0 hβ1.le) (hW_pos _).le
    linarith

theorem wmi_part2_core
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ t ≤ T,
      Summable (omega W w l t) ∧
      ∑' i, omega W w l t i ≤
        (2 - 1 / ((mistakesBefore prediction label t : ℝ) + 1)) *
          u β ^ mistakesBefore prediction label t * What 1 := by
  intro t ht
  refine ⟨?_, ?_⟩
  · have := wmi_Om_summable hW_sum w l t
    exact (Equiv.summable_iff (f := omega W w l t) Equiv.pnatEquivNat.symm).mp
      (by simpa [Function.comp_def, Equiv.pnatEquivNat_symm_apply] using this)
  · have h := Equiv.tsum_eq Equiv.pnatEquivNat.symm (omega W w l t)
    simp only [Equiv.pnatEquivNat_symm_apply] at h
    rw [← h]
    exact wmi_part2_nat hβ0 hβ1 hW_pos hW_sum hWhat_tail hrun t ht

theorem wmi_part1_core
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ t : Fin T,
      What (Nat.succPNat (l t.val)) ≤ slack β What (mistakesBefore prediction label t.val) ∧
      ∀ l' < l t.val,
        slack β What (mistakesBefore prediction label t.val) < What (Nat.succPNat l') :=
  fun t => wmi_part1 hβ0 hβ1 hW_pos hW_sum hWhat_tail hrun t.val t.isLt

theorem wmi_part3_core
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    (0 < β → ∀ i : ℕ+,
      (mistakesBefore prediction label T : ℝ) ≤
        (Real.log (What 1 / W i) + (mi i : ℝ) * Real.log (1 / β) + Real.log 2) /
          Real.log (1 / u β)) ∧
    (β = 0 → ∀ i : ℕ+, mi i = 0 →
      (mistakesBefore prediction label T : ℝ) ≤ 1 + Real.logb 2 (What 1 / W i)) := by
  have ha := wmi_What1_pos hW_pos hW_sum hWhat_tail
  have hu := wmi_u_pos hβ0
  have hu1 := wmi_u_lt hβ1
  have hP2 := wmi_part2_nat hβ0 hβ1 hW_pos hW_sum hWhat_tail hrun T le_rfl
  have hC : ∀ i : ℕ+, W i * β ^ mi i ≤
      2 * u β ^ mistakesBefore prediction label T * What 1 := by
    intro i
    obtain ⟨k, rfl⟩ : ∃ k, i = Nat.succPNat k := ⟨i.natPred, (PNat.succPNat_natPred i).symm⟩
    have h1 := wmi_lower hβ0 hβ1 hW_pos hW_sum mi hmi hrun k
    refine le_trans h1 (le_trans hP2 ?_)
    have h2 : (0:ℝ) ≤ 1 / ((mistakesBefore prediction label T : ℝ) + 1) := by positivity
    have h3 : 0 < u β ^ mistakesBefore prediction label T * What 1 := by positivity
    nlinarith
  set m := mistakesBefore prediction label T with hm
  refine ⟨fun hβ i => ?_, fun hβ i hi => ?_⟩
  · have h1 := hC i
    have hW := hW_pos i
    have hlog := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hW.ne' (by positivity), Real.log_pow,
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow] at hlog
    have hpos : 0 < Real.log (1 / u β) := Real.log_pos (one_lt_one_div hu hu1)
    rw [le_div_iff₀ hpos]
    rw [Real.log_div ha.ne' hW.ne', one_div, one_div, Real.log_inv, Real.log_inv]
    nlinarith
  · subst hβ
    have h1 := hC i
    rw [hi] at h1
    have hu0 : u 0 = 1 / 2 := by unfold u; norm_num
    rw [hu0] at h1
    have hW := hW_pos i
    have h2 : (2:ℝ) ^ m ≤ 2 * (What 1 / W i) := by
      have h2m : (0:ℝ) < 2 ^ m := by positivity
      have h1' : W i ≤ 2 * (2 ^ m)⁻¹ * What 1 := by
        rw [one_div, inv_pow] at h1
        simpa using h1
      have h5 : W i * 2 ^ m ≤ 2 * What 1 := by
        calc W i * 2 ^ m ≤ (2 * (2 ^ m)⁻¹ * What 1) * 2 ^ m :=
              mul_le_mul_of_nonneg_right h1' h2m.le
          _ = 2 * What 1 := by field_simp
      rw [← mul_div_assoc, le_div_iff₀ hW]
      linarith
    have h3 : (m : ℝ) ≤ Real.logb 2 (2 * (What 1 / W i)) := by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), Real.rpow_natCast]
      exact h2
    rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one one_lt_two] at h3
    exact h3

end WeightedMajority.InfinitePool

open WeightedMajority.InfinitePool


theorem solution
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (W What : ℕ+ → ℝ) (hW_pos : ∀ i, 0 < W i) (hW_sum : Summable W)
    (hWhat_tail : ∀ i, (∑' j : ℕ+, if i ≤ j then W j else 0) ≤ What i)
    (hWhat_lim : Filter.Tendsto What Filter.atTop (nhds 0))
    {T : ℕ} (x : Fin T → ℕ+ → Bool) (label : Fin T → Bool)
    (mi : ℕ+ → ℕ)
    (hmi : ∀ i, (Finset.univ.filter (fun t : Fin T => x t i ≠ label t)).card ≤ mi i)
    (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (hrun : IsWMI2Run β W What x label prediction w l) :
    ∀ t ≤ T,
      Summable (omega W w l t) ∧
      ∑' i, omega W w l t i ≤
        (2 - 1 / ((mistakesBefore prediction label t : ℝ) + 1)) *
          u β ^ mistakesBefore prediction label t * What 1 := by
  exact wmi_part2_core β hβ0 hβ1 W What hW_pos hW_sum hWhat_tail hWhat_lim x label mi hmi prediction w l hrun
