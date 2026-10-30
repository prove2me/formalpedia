-- Prove2me | solution 1 for RepeatedNRM.Myopic.ec5_quality_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T19:12:09.605544+00:00
-- url     : https://prove2.me/submissions/d0854179-4a44-43fb-9cbb-80e0965e5806

import Mathlib
import Definitions.Def_RepeatedNRM_Myopic_Model

namespace RepeatedNRM.Myopic

lemma rnrm_zero_feasible (I : Instance) (hI : I.Standing) (b : Fin I.m → ℝ)
    (hb : ∀ j, 0 ≤ b j) : feasible I b (fun _ _ => 0) := by
  refine ⟨fun _ _ => le_rfl, fun j => by simpa using hb j, fun i => by simpa using hI.1 i⟩

lemma rnrm_revenue_le (I : Instance) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) : revenue I x ≤ ∑ j, b j := by
  unfold revenue
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun j _ => hx.2.1 j

lemma rnrm_bdd (I : Instance) (b : Fin I.m → ℝ) :
    BddAbove (revenue I '' {x | feasible I b x}) := by
  refine ⟨∑ j, b j, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact rnrm_revenue_le I b x hx

lemma rnrm_nonempty (I : Instance) (hI : I.Standing) (b : Fin I.m → ℝ)
    (hb : ∀ j, 0 ≤ b j) : (revenue I '' {x | feasible I b x}).Nonempty :=
  ⟨_, ⟨_, rnrm_zero_feasible I hI b hb, rfl⟩⟩

lemma rnrm_le_MY (I : Instance) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) : revenue I x ≤ MY I b :=
  le_csSup (rnrm_bdd I b) ⟨x, hx, rfl⟩

lemma rnrm_MY_nonneg (I : Instance) (hI : I.Standing) (b : Fin I.m → ℝ)
    (hb : ∀ j, 0 ≤ b j) : 0 ≤ MY I b := by
  have := rnrm_le_MY I b _ (rnrm_zero_feasible I hI b hb)
  simpa [revenue] using this

lemma rnrm_feasible_mono (I : Instance) (b bbar : Fin I.m → ℝ) (hle : ∀ j, b j ≤ bbar j)
    (x : Fin I.n → Fin I.m → ℝ) (hx : feasible I b x) : feasible I bbar x :=
  ⟨hx.1, fun j => (hx.2.1 j).trans (hle j), hx.2.2⟩

lemma rnrm_MY_mono (I : Instance) (hI : I.Standing) (b bbar : Fin I.m → ℝ)
    (hb : ∀ j, 0 ≤ b j) (hle : ∀ j, b j ≤ bbar j) : MY I b ≤ MY I bbar := by
  apply csSup_le_csSup (rnrm_bdd I bbar) (rnrm_nonempty I hI b hb)
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, rnrm_feasible_mono I b bbar hle x hx, rfl⟩

/-! Utility / quality facts -/

lemma rnrm_custFeasible_zero (I : Instance) (hI : I.Standing) (j : Fin I.m) (bj : ℝ)
    (hbj : 0 ≤ bj) : custFeasible I j bj (fun _ => 0) :=
  ⟨fun i => ⟨le_rfl, hI.1 i⟩, by simpa using hbj⟩

lemma rnrm_utility_nonneg (I : Instance) (hI : I.Standing) (j : Fin I.m) (y : Fin I.n → ℝ)
    (hy : ∀ i, 0 ≤ y i) : 0 ≤ utility I j y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.2 (hI.2.2.1 i j)) (hy i)

lemma rnrm_utility_bdd (I : Instance) (hI : I.Standing) (j : Fin I.m) (bj : ℝ) :
    BddAbove (utility I j '' {y | custFeasible I j bj y}) := by
  refine ⟨∑ i, (I.v i j - I.p i j) * I.s i, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_left (hy.1 i).2 (sub_nonneg.2 (hI.2.2.1 i j))

lemma rnrm_utility_le_uStar (I : Instance) (hI : I.Standing) (j : Fin I.m) (bj : ℝ)
    (y : Fin I.n → ℝ) (hy : custFeasible I j bj y) : utility I j y ≤ uStar I j bj :=
  le_csSup (rnrm_utility_bdd I hI j bj) ⟨y, hy, rfl⟩

lemma rnrm_uStar_nonneg (I : Instance) (hI : I.Standing) (j : Fin I.m) (bj : ℝ)
    (hbj : 0 ≤ bj) : 0 ≤ uStar I j bj := by
  have := rnrm_utility_le_uStar I hI j bj _ (rnrm_custFeasible_zero I hI j bj hbj)
  simpa [utility] using this

lemma rnrm_cust_of_feasible (I : Instance) (b : Fin I.m → ℝ) (x : Fin I.n → Fin I.m → ℝ)
    (hx : feasible I b x) (j : Fin I.m) : custFeasible I j (b j) (fun i => x i j) := by
  refine ⟨fun i => ⟨hx.1 i j, ?_⟩, hx.2.1 j⟩
  calc x i j ≤ ∑ k, x i k :=
        Finset.single_le_sum (f := fun k => x i k) (fun k _ => hx.1 i k) (Finset.mem_univ j)
    _ ≤ I.s i := hx.2.2 i

lemma rnrm_quality_mem (I : Instance) (hI : I.Standing) (j : Fin I.m) (bj : ℝ) (hbj : 0 ≤ bj)
    (y : Fin I.n → ℝ) (hy : custFeasible I j bj y) : quality I j bj y ∈ Set.Icc (0 : ℝ) 1 := by
  unfold quality
  split_ifs with h
  · exact ⟨zero_le_one, le_rfl⟩
  · simp only [not_or] at h
    have hU := rnrm_utility_nonneg I hI j y (fun i => (hy.1 i).1)
    have hle := rnrm_utility_le_uStar I hI j bj y hy
    have hpos : 0 < uStar I j bj := lt_of_le_of_ne (rnrm_uStar_nonneg I hI j bj hbj) (Ne.symm h.2)
    exact ⟨div_nonneg hU hpos.le, (div_le_one hpos).2 hle⟩

lemma rnrm_phiIter_mem (I : Instance) (hI : I.Standing) (j : Fin I.m) (t : ℕ) (b q : ℝ)
    (hb : b ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    phiIter I j t b q ∈ Set.Icc (0 : ℝ) 1 := by
  induction t with
  | zero => simpa [phiIter] using hb
  | succ t ih =>
    have : phiIter I j (t + 1) b q = I.phi j (phiIter I j t b q) q := by
      simp only [phiIter]; rw [Function.iterate_succ_apply']
    rw [this]; exact hI.2.2.2 j _ _ ih hq

lemma rnrm_phiIter_succ (I : Instance) (j : Fin I.m) (t : ℕ) (b q : ℝ) :
    phiIter I j (t + 1) b q = I.phi j (phiIter I j t b q) q := by
  simp only [phiIter]; rw [Function.iterate_succ_apply']


lemma rnrm_traj_bounds (I : Instance) (hI : I.Standing) (h1 : ∀ j, Assumption1i I j)
    (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (x : ℕ → Fin I.n → Fin I.m → ℝ) (b : ℕ → Fin I.m → ℝ) (hx : IsTrajectory I b1 x b) :
    ∀ t, ∀ j, b t j ∈ Set.Icc (0 : ℝ) 1 ∧ b t j ≤ phiIter I j t (b1 j) 1 := by
  intro t
  induction t with
  | zero => intro j; rw [hx.1]; exact ⟨hb1 j, by simp [phiIter]⟩
  | succ t ih =>
    intro j
    have hq := rnrm_quality_mem I hI j (b t j) (ih j).1.1 _
      (rnrm_cust_of_feasible I (b t) (x t) (hx.2 t).1 j)
    have hupd : b (t + 1) j = I.phi j (b t j) (qualityVec I (b t) (x t) j) := by
      rw [(hx.2 t).2]; rfl
    have h01 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have hit := rnrm_phiIter_mem I hI j t (b1 j) 1 (hb1 j) h01
    rw [hupd, rnrm_phiIter_succ]
    refine ⟨hI.2.2.2 j _ _ (ih j).1 hq, ?_⟩
    calc I.phi j (b t j) (qualityVec I (b t) (x t) j) ≤ I.phi j (b t j) 1 :=
          (h1 j).2 _ _ _ (ih j).1 h01 hq hq.2
      _ ≤ I.phi j (phiIter I j t (b1 j) 1) 1 := (h1 j).1 _ _ _ h01 hit (ih j).1 (ih j).2

theorem rnrm_proposition_2 (I : Instance) (hI : I.Standing) (h1 : ∀ j, Assumption1i I j)
    (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1) (T : ℕ)
    (x : ℕ → Fin I.n → Fin I.m → ℝ) (b : ℕ → Fin I.m → ℝ) (hx : IsTrajectory I b1 x b) :
    ∑ t ∈ Finset.range T, revenue I (x t) ≤ Jrelax I T b1 := by
  unfold Jrelax
  apply Finset.sum_le_sum
  intro t _
  have hB := rnrm_traj_bounds I hI h1 b1 hb1 x b hx t
  calc revenue I (x t) ≤ MY I (b t) := rnrm_le_MY I _ _ (hx.2 t).1
    _ ≤ MY I (phiIterVec I t b1 1) :=
        rnrm_MY_mono I hI _ _ (fun j => (hB j).1.1) (fun j => (hB j).2)

theorem rnrm_scaling_step (I : Instance) (hI : I.Standing) (h1 : ∀ j, Assumption1iii I j)
    (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) :
    (∀ t ∈ Finset.range T, ∀ x : Fin I.n → Fin I.m → ℝ, feasible I (phiIterVec I t b1 1) x →
        feasible I (phiIterVec I t b1 (1 - γ)) ((1 - γ) • x)) ∧
      (1 - γ) * Jrelax I T b1 ≤ JLBMY I T b1 γ := by
  have hg : 0 ≤ 1 - γ := sub_nonneg.2 hγ.2
  have h01 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hg01 : (1 - γ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hg, by linarith [hγ.1]⟩
  have key : ∀ t : ℕ, ∀ x : Fin I.n → Fin I.m → ℝ, feasible I (phiIterVec I t b1 1) x →
      feasible I (phiIterVec I t b1 (1 - γ)) ((1 - γ) • x) := by
    intro t x hx
    refine ⟨fun i j => ?_, fun j => ?_, fun i => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hg (hx.1 i j)
    · simp only [Pi.smul_apply, smul_eq_mul, phiIterVec]
      have hb := hx.2.1 j
      simp only [phiIterVec] at hb
      have hsc : (1 - γ) * phiIter I j t (b1 j) 1 ≤ phiIter I j t (b1 j) (1 - γ) := by
        rcases Nat.eq_zero_or_pos t with rfl | ht
        · simp only [phiIter, Function.iterate_zero, id]
          nlinarith [(hb1 j).1, hγ.1]
        · exact h1 j (b1 j) (hb1 j) t ht γ hγ
      calc ∑ i, I.p i j * ((1 - γ) * x i j) = (1 - γ) * ∑ i, I.p i j * x i j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ (1 - γ) * phiIter I j t (b1 j) 1 := mul_le_mul_of_nonneg_left hb hg
        _ ≤ _ := hsc
    · simp only [Pi.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
      have := hx.2.2 i
      nlinarith [hI.1 i, hγ.1]
  refine ⟨fun t _ => key t, ?_⟩
  unfold Jrelax JLBMY
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro t _
  have hB : ∀ j, 0 ≤ phiIterVec I t b1 1 j := fun j =>
    (rnrm_phiIter_mem I hI j t (b1 j) 1 (hb1 j) h01).1
  have hB' : ∀ j, 0 ≤ phiIterVec I t b1 (1 - γ) j := fun j =>
    (rnrm_phiIter_mem I hI j t (b1 j) (1 - γ) (hb1 j) hg01).1
  rcases eq_or_lt_of_le hg with h0 | hpos
  · have hn := rnrm_MY_nonneg I hI _ hB'; rw [← h0] at hn ⊢; rw [zero_mul]; exact hn
  · rw [← le_div_iff₀' hpos]
    apply csSup_le (rnrm_nonempty I hI _ hB)
    rintro _ ⟨x, hx, rfl⟩
    rw [le_div_iff₀' hpos]
    have := rnrm_le_MY I _ _ (key t x hx)
    have hr : revenue I ((1 - γ) • x) = (1 - γ) * revenue I x := by
      unfold revenue
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    linarith


lemma rnrm_spendA_le (I : Instance) (hI : I.Standing) (A : Finset (Fin I.n)) (j : Fin I.m)
    (bj : ℝ) (z : Fin I.n → ℝ) (hz : custFeasible I j bj z) :
    ∑ i ∈ A, I.p i j * z i ≤ min bj (∑ i ∈ A, I.p i j * I.s i) := by
  apply le_min
  · calc ∑ i ∈ A, I.p i j * z i ≤ ∑ i, I.p i j * z i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
            (fun i _ _ => mul_nonneg (hI.2.1 i j) (hz.1 i).1)
      _ ≤ bj := hz.2
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hz.1 i).2 (hI.2.1 i j)

lemma rnrm_utility_eq (I : Instance) (A : Fin I.m → Finset (Fin I.n)) (γ : ℝ)
    (h2 : Assumption2 I A γ) (j : Fin I.m) (z : Fin I.n → ℝ) :
    utility I j z = ∑ i ∈ A j, (I.v i j / I.p i j - 1) * (I.p i j * z i) := by
  unfold utility
  rw [← Finset.sum_subset (Finset.subset_univ (A j))]
  · apply Finset.sum_congr rfl
    intro i hi
    have hp := h2.2.2.1 j i hi
    field_simp
  · intro i _ hi
    obtain ⟨hv, hp⟩ := h2.2.1 j i hi
    simp [hv, hp]

theorem rnrm_ec5 (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n))
    (γ : ℝ) (h2 : Assumption2 I A γ) (j : Fin I.m) (bj : ℝ) (hbj : bj ∈ Set.Icc (0 : ℝ) 1)
    (y : Fin I.n → ℝ) (hy : custFeasible I j bj y) :
    (1 - γ) * ((∑ i ∈ A j, I.p i j * y i) / min bj (∑ i ∈ A j, I.p i j * I.s i)) ≤
      quality I j bj y := by
  set P := ∑ i ∈ A j, I.p i j * y i with hPdef
  set M := min bj (∑ i ∈ A j, I.p i j * I.s i) with hMdef
  have hg : 0 ≤ 1 - γ := sub_nonneg.2 h2.1.2
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (hI.2.1 i j) (hy.1 i).1
  have hPM : P ≤ M := rnrm_spendA_le I hI (A j) j bj y hy
  have hM0 : 0 ≤ M := hP0.trans hPM
  have hq := rnrm_quality_mem I hI j bj hbj.1 y hy
  have hfrac : P / M ≤ 1 := div_le_one_of_le₀ hPM hM0
  by_cases hA : (A j).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty] at hA
    have : P = 0 := by rw [hPdef, hA, Finset.sum_empty]
    rw [this, zero_div, mul_zero]; exact hq.1
  unfold quality
  split_ifs with hc
  · nlinarith [h2.1.1, div_nonneg hP0 hM0]
  simp only [not_or] at hc
  set ρ : Fin I.n → ℝ := fun i => I.v i j / I.p i j - 1 with hρ
  obtain ⟨k, hk, hkmax⟩ := Finset.exists_max_image (A j) ρ hA
  have hρnn : ∀ i ∈ A j, 0 ≤ ρ i := by
    intro i hi
    have hp := h2.2.2.1 j i hi
    simp only [hρ, sub_nonneg]
    rw [le_div_iff₀ hp, one_mul]; exact hI.2.2.1 i j
  have hUy : (1 - γ) * ρ k * P ≤ utility I j y := by
    rw [rnrm_utility_eq I A γ h2 j y, hPdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_right (h2.2.2.2 j i hi k hk)
      (mul_nonneg (hI.2.1 i j) (hy.1 i).1)
  have hUs : uStar I j bj ≤ ρ k * M := by
    unfold uStar
    refine csSup_le ⟨utility I j (fun _ => 0), ⟨fun _ => 0, rnrm_custFeasible_zero I hI j bj hbj.1, rfl⟩⟩ ?_
    rintro _ ⟨z, hz, rfl⟩
    rw [rnrm_utility_eq I A γ h2 j z]
    calc ∑ i ∈ A j, ρ i * (I.p i j * z i) ≤ ∑ i ∈ A j, ρ k * (I.p i j * z i) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hkmax i hi)
            (mul_nonneg (hI.2.1 i j) (hz.1 i).1)
      _ = ρ k * ∑ i ∈ A j, I.p i j * z i := by rw [Finset.mul_sum]
      _ ≤ ρ k * M := mul_le_mul_of_nonneg_left (rnrm_spendA_le I hI (A j) j bj z hz)
          (hρnn k hk)
  have hUpos : 0 < uStar I j bj :=
    lt_of_le_of_ne (rnrm_uStar_nonneg I hI j bj hbj.1) (Ne.symm hc.2)
  have hMpos : 0 < M := by
    rcases eq_or_lt_of_le hM0 with h | h
    · rw [← h, mul_zero] at hUs; linarith
    · exact h
  rw [← mul_div_assoc, div_le_div_iff₀ hMpos hUpos]
  have h1 : (1 - γ) * P * uStar I j bj ≤ (1 - γ) * P * (ρ k * M) :=
    mul_le_mul_of_nonneg_left hUs (mul_nonneg hg hP0)
  have h3 : (1 - γ) * ρ k * P * M ≤ utility I j y * M := mul_le_mul_of_nonneg_right hUy hM0
  linarith [show (1 - γ) * P * (ρ k * M) = (1 - γ) * ρ k * P * M by ring]

theorem rnrm_lemma_3 (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n))
    (h1 : ∀ j, Assumption1i I j ∧ Assumption1ii I j ∧ Assumption1iii I j)
    (h2 : Assumption2 I A 0) (b1 : Fin I.m → ℝ) (hb1 : ∀ j, b1 j ∈ Set.Icc (0 : ℝ) 1)
    (x : Fin I.n → Fin I.m → ℝ) (hx : IsMyopicAlloc I b1 x) :
    feasible I (update I b1 x) x := by
  have hf := hx.1
  refine ⟨hf.1, fun l => ?_, hf.2.2⟩
  have hc := rnrm_cust_of_feasible I b1 x hf l
  have he := rnrm_ec5 I hI A 0 h2 l (b1 l) (hb1 l) _ hc
  have hq := rnrm_quality_mem I hI l (b1 l) (hb1 l).1 _ hc
  rw [sub_zero, one_mul] at he
  set P := ∑ i ∈ A l, I.p i l * x i l
  set M := min (b1 l) (∑ i ∈ A l, I.p i l * I.s i)
  have hspend : ∑ i, I.p i l * x i l = P := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp [(h2.2.1 l i hi).2]
  have hP0 : 0 ≤ P := Finset.sum_nonneg fun i _ => mul_nonneg (hI.2.1 i l) (hf.1 i l)
  have hPM : P ≤ M := rnrm_spendA_le I hI (A l) l (b1 l) _ hc
  have hM1 : M ≤ 1 := (min_le_left _ _).trans (hb1 l).2
  have hPq : P ≤ quality I l (b1 l) (fun i => x i l) := by
    rcases eq_or_lt_of_le (hP0.trans hPM) with h | h
    · rw [← h] at hPM; linarith [hq.1]
    · refine le_trans ?_ he
      rw [le_div_iff₀ h]
      nlinarith
  show ∑ i, I.p i l * x i l ≤ I.phi l (b1 l) (qualityVec I b1 x l)
  rw [hspend]
  refine le_trans ?_ ((h1 l).2.1 (b1 l) _ (hb1 l) hq)
  exact le_min (hspend ▸ hf.2.1 l) hPq

end RepeatedNRM.Myopic

open RepeatedNRM.Myopic

theorem solution (I : Instance) (hI : I.Standing) (A : Fin I.m → Finset (Fin I.n))
    (γ : ℝ) (h2 : Assumption2 I A γ) (j : Fin I.m) (bj : ℝ) (hbj : bj ∈ Set.Icc (0 : ℝ) 1)
    (y : Fin I.n → ℝ) (hy : custFeasible I j bj y) :
    (1 - γ) * ((∑ i ∈ A j, I.p i j * y i) / min bj (∑ i ∈ A j, I.p i j * I.s i)) ≤
      quality I j bj y :=
  rnrm_ec5 I hI A γ h2 j bj hbj y hy
