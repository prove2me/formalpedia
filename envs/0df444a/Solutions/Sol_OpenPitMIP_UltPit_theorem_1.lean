-- Prove2me | solution 1 for OpenPitMIP.UltPit.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:31:00.819749+00:00
-- url     : https://prove2.me/submissions/8abfaae6-5ef7-41f5-8211-37812f0a03fc

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

namespace RRAux_OpenPitMIP_UltPit_theorem_1

open OpenPitMIP.UltPit OpenPitMIP.UltPit.PCPSPC

-- Abel summation: decreasing nonnegative weights against sequences with nonpositive partial sums.
lemma abel {T : ℕ} (δ : ℕ → ℝ) (hanti : ∀ n, δ (n + 1) ≤ δ n) (hpos : ∀ n, 0 ≤ δ n)
    (a : Fin T → ℝ) (hW : ∀ s : Fin T, ∑ t ∈ Finset.Iic s, a t ≤ 0) :
    ∑ t, δ t.val * a t ≤ 0 := by
  have hδ : ∀ t : Fin T, δ t.val =
      ∑ s : Fin T, (if t.val ≤ s.val then δ s.val - δ (s.val + 1) else 0) + δ T := by
    intro t
    rw [Fin.sum_univ_eq_sum_range (fun n => if t.val ≤ n then δ n - δ (n + 1) else 0),
      ← Finset.sum_filter]
    have : (Finset.range T).filter (fun n => t.val ≤ n) = Finset.Ico t.val T := by
      ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [this, Finset.sum_Ico_eq_sub _ (le_of_lt t.isLt), Finset.sum_range_sub',
      Finset.sum_range_sub']
    ring
  have hIic : ∀ s : Fin T, ∑ t ∈ Finset.Iic s, a t =
      ∑ t : Fin T, (if t.val ≤ s.val then a t else 0) := by
    intro s
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (Finset.ext fun t => ?_) (fun _ _ => rfl)
    rw [Finset.mem_Iic, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ _, h⟩, fun h => h.2⟩
  have e1 : ∑ t, δ t.val * a t =
      ∑ s : Fin T, (δ s.val - δ (s.val + 1)) * ∑ t ∈ Finset.Iic s, a t +
        δ T * ∑ t, a t := by
    rw [Finset.sum_congr rfl fun t _ => by rw [hδ t]]
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hIic s, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> ring
  have htot : ∑ t, a t ≤ 0 := by
    cases T with
    | zero => simp
    | succ n =>
      have h := hW (Fin.last n)
      have : Finset.Iic (Fin.last n) = Finset.univ := by
        ext t; simp [Fin.le_last]
      rwa [this] at h
  rw [e1]
  have h1 : ∑ s : Fin T, (δ s.val - δ (s.val + 1)) * ∑ t ∈ Finset.Iic s, a t ≤ 0 :=
    Finset.sum_nonpos fun s _ =>
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 (hanti s.val)) (hW s)
  have h2 : δ T * ∑ t, a t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (hpos T) htot
  linarith

lemma exists_eps {C : Type} [Fintype C] (f : C → ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ c, 0 < f c → ε ≤ f c := by
  classical
  by_cases h : (Finset.univ.filter fun c => 0 < f c).Nonempty
  · refine ⟨min 1 ((Finset.univ.filter fun c => 0 < f c).inf' h f), ?_, min_le_left _ _,
      fun c hc => ?_⟩
    · apply lt_min one_pos
      rw [Finset.lt_inf'_iff]
      intro c hc
      simpa using hc
    · exact le_trans (min_le_right _ _) (Finset.inf'_le _ (by simpa using hc))
  · exact ⟨1, one_pos, le_rfl, fun c hc => absurd ⟨c, by simpa using hc⟩ h⟩

lemma eps_step {xc xc' ε zc zc' : ℝ} (hε0 : 0 < ε) (hle : xc ≤ xc') (h0 : 0 ≤ xc)
    (hzc : zc ≤ zc') : xc + ε * zc ≤ xc' + ε * zc' := by
  have := mul_le_mul_of_nonneg_left hzc hε0.le
  linarith

lemma eps_cross {xc xc' ε zc : ℝ} (hε0 : 0 < ε) (hz1 : zc ≤ 1) (hεle : ε ≤ xc')
    (hxc : xc ≤ 0) : xc + ε * zc ≤ xc' + ε * 0 := by
  have := mul_le_mul_of_nonneg_left hz1 hε0.le
  linarith

lemma upit_dir {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [Nonempty D] {T m : ℕ}
    (I : PCPSPC B D C T m) (xU : C → ℝ) (hU : I.UPitOptimal xU) (z : C → ℝ)
    (hz0 : ∀ c, 0 ≤ z c) (hz1 : ∀ c, z c ≤ 1) (hzarc : ∀ c c', I.arc c c' → z c ≤ z c') :
    ∑ c, I.pbar c * (if 0 < xU c then 0 else z c) ≤ 0 := by
  obtain ⟨ε, hε0, hε1, hεle⟩ := exists_eps xU
  let zQ : C → ℝ := fun c => if 0 < xU c then 0 else z c
  have hfeas : I.UPitFeasible (fun c => xU c + ε * zQ c) := by
    refine ⟨fun c c' harc => ?_, fun c => ?_⟩
    · have h1 := hU.1.1 c c' harc
      have hb := hU.1.2 c
      have hb' := hU.1.2 c'
      have hzc := hzarc c c' harc
      by_cases hc : 0 < xU c <;> by_cases hc' : 0 < xU c' <;>
        simp only [zQ, hc, hc', if_true, if_false]
      · linarith
      · linarith
      · exact eps_cross hε0 (hz1 c) (hεle c' hc') (not_lt.1 hc)
      · exact eps_step hε0 h1 hb.1 hzc
    · have hb := hU.1.2 c
      by_cases hc : 0 < xU c <;> simp only [zQ, hc, if_true, if_false]
      · constructor <;> linarith
      · have h0 : xU c = 0 := le_antisymm (not_lt.1 hc) hb.1
        have h2 := mul_le_mul_of_nonneg_left (hz1 c) hε0.le
        have h3 := mul_nonneg hε0.le (hz0 c)
        constructor <;> nlinarith
  have hobj := hU.2 _ hfeas
  unfold UPitObjective at hobj
  have hsplit : ∑ c, I.pbar c * (xU c + ε * zQ c) =
      ∑ c, I.pbar c * xU c + ε * ∑ c, I.pbar c * zQ c := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  rw [hsplit] at hobj
  have hneg : ε * ∑ c, I.pbar c * zQ c ≤ 0 := by linarith
  by_contra hcon
  push Not at hcon
  have := mul_pos hε0 hcon
  linarith

lemma obj_le {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [Nonempty D] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing) (xU : C → ℝ) (hU : I.UPitOptimal xU)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ)
    (hxy : ∀ b t, x (I.clu b) t = ∑ d, y b d t) (hsum1 : ∀ c, ∑ t, x c t ≤ 1)
    (hprec : ∀ c c', I.arc c c' → ∀ t, cum x c t ≤ cum x c' t)
    (hy0 : ∀ b d t, 0 ≤ y b d t) (hx0 : ∀ c t, 0 ≤ x c t) :
    ∑ b, ∑ d, ∑ t, (if 0 < xU (I.clu b) then 0 else I.value b d t * y b d t) ≤ 0 := by
  classical
  have hr : 0 < 1 + I.r := by linarith [hI.r_pos]
  let δ : ℕ → ℝ := fun n => ((1 + I.r) ^ (n + 1))⁻¹
  let M : B → ℝ := fun b => Finset.univ.sup' Finset.univ_nonempty (I.p b)
  let a : Fin T → ℝ := fun t => ∑ c, I.pbar c * (if 0 < xU c then 0 else x c t)
  have step1 : ∑ b, ∑ d, ∑ t, (if 0 < xU (I.clu b) then 0 else I.value b d t * y b d t) ≤
      ∑ b, ∑ d, ∑ t, (if 0 < xU (I.clu b) then 0 else M b * δ t.val * y b d t) := by
    refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun d _ =>
      Finset.sum_le_sum fun t _ => ?_
    split_ifs
    · exact le_rfl
    · unfold PCPSPC.value
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Finset.le_sup' (I.p b) (Finset.mem_univ d))
          (inv_nonneg.2 (pow_pos hr _).le)) (hy0 b d t)
  have hbl : ∀ c, I.blocksOf {c} = Finset.univ.filter (fun b => I.clu b = c) := by
    intro c; ext b; simp [PCPSPC.blocksOf]
  have step2 : ∑ b, ∑ d, ∑ t, (if 0 < xU (I.clu b) then 0 else M b * δ t.val * y b d t) =
      ∑ t, δ t.val * a t := by
    rw [Finset.sum_congr rfl fun b _ => Finset.sum_comm]
    have hin : ∀ b t, ∑ d, (if 0 < xU (I.clu b) then 0 else M b * δ t.val * y b d t) =
        δ t.val * (M b * (if 0 < xU (I.clu b) then 0 else x (I.clu b) t)) := by
      intro b t
      split_ifs
      · simp
      · rw [hxy b t, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        ring
    simp only [hin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_fiberwise Finset.univ I.clu]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold PCPSPC.pbar
    rw [hbl c, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbc : I.clu b = c := by simpa using hb
    rw [hbc]
  have step3 : ∑ t, δ t.val * a t ≤ 0 := by
    refine abel δ (fun n => ?_) (fun n => (inv_nonneg.2 (pow_pos hr _).le)) a (fun s => ?_)
    · exact inv_anti₀ (pow_pos hr _) (pow_le_pow_right₀ (by linarith [hI.r_pos]) (by omega))
    · have hcum : ∑ t ∈ Finset.Iic s, a t =
          ∑ c, I.pbar c * (if 0 < xU c then 0 else cum x c s) := by
        simp only [a]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        split_ifs
        · simp
        · rw [cum, Finset.mul_sum]
      rw [hcum]
      refine upit_dir I xU hU (fun c => cum x c s) (fun c => ?_) (fun c => ?_)
        (fun c c' h => hprec c c' h s)
      · exact Finset.sum_nonneg fun t _ => hx0 c t
      · exact le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun t _ _ => hx0 c t)) (hsum1 c)
  linarith

end RRAux_OpenPitMIP_UltPit_theorem_1

open RRAux_OpenPitMIP_UltPit_theorem_1 in
open OpenPitMIP.UltPit in
open OpenPitMIP.UltPit.PCPSPC in
-- Theorem 1, p. 1431.
theorem solution {B D C : Type} [Fintype B] [Fintype D] [Fintype C] [Nonempty D] {T m : ℕ}
    (I : PCPSPC B D C T m) (hI : I.Standing)
    (hG : ∀ i b d t, 0 ≤ I.G i b d t) (hg : ∀ i, 0 ≤ I.g i)
    (κ : Integrality) (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ)
    (hopt : I.MinimalOptimal κ x y)
    (xU : C → ℝ) (hU : I.UPitMinimalOptimal xU) :
    pitLimit (fun c => ∑ t, x c t) ⊆ pitLimit xU := by
  intro c hc
  by_contra hcU
  have hcU' : ¬ 0 < xU c := hcU
  have hc' : 0 < ∑ t, x c t := hc
  obtain ⟨⟨hfeas, hbest⟩, hmin⟩ := hopt
  obtain ⟨hxy, hsum1, hprec, hGy, hy0, hint⟩ := hfeas
  have hx0 : ∀ c t, 0 ≤ x c t := by
    intro c t
    obtain ⟨b, rfl⟩ := hI.clu_surjective c
    rw [hxy b t]
    exact Finset.sum_nonneg fun d _ => hy0 b d t
  have hcum0 : ∀ c t, 0 ≤ cum x c t := fun c t => Finset.sum_nonneg fun s _ => hx0 c s
  let x' : C → Fin T → ℝ := fun c t => if 0 < xU c then x c t else 0
  let y' : B → D → Fin T → ℝ := fun b d t => if 0 < xU (I.clu b) then y b d t else 0
  have hcum' : ∀ c t, cum x' c t = if 0 < xU c then cum x c t else 0 := by
    intro c t
    unfold cum
    by_cases h : 0 < xU c <;> simp [x', h]
  have harcU : ∀ c c', I.arc c c' → 0 < xU c → 0 < xU c' := fun c c' h h0 =>
    lt_of_lt_of_le h0 (hU.1.1.1 c c' h)
  have hfeas' : I.Feasible κ x' y' := by
    refine ⟨fun b t => ?_, fun c => ?_, fun c c' h t => ?_, fun i => ?_, fun b d t => ?_, ?_⟩
    · by_cases h : 0 < xU (I.clu b) <;> simp [x', y', h, hxy b t]
    · by_cases h : 0 < xU c <;> simp [x', h, hsum1 c]
    · rw [hcum' c t, hcum' c' t]
      by_cases h0 : 0 < xU c
      · rw [if_pos h0, if_pos (harcU c c' h h0)]
        exact hprec c c' h t
      · rw [if_neg h0]
        split_ifs
        · exact hcum0 c' t
        · exact le_rfl
    · refine le_trans (Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun d _ =>
        Finset.sum_le_sum fun t _ => ?_) (hGy i)
      by_cases h : 0 < xU (I.clu b)
      · simp [y', h]
      · simp only [y', h, if_false, mul_zero]
        exact mul_nonneg (hG i b d t) (hy0 b d t)
    · by_cases h : 0 < xU (I.clu b) <;> simp [y', h, hy0 b d t]
    · cases κ with
      | F =>
        intro c t
        by_cases h : 0 < xU c
        · simp only [x', h, if_true]; exact hint c t
        · simp [x', h]
      | P =>
        intro c c' h t hpos
        rw [hcum' c t] at hpos
        rw [hcum' c' t]
        by_cases h0 : 0 < xU c
        · rw [if_pos h0] at hpos
          rw [if_pos (harcU c c' h h0)]
          exact hint c c' h t hpos
        · rw [if_neg h0] at hpos
          exact absurd hpos (lt_irrefl 0)
  have hsplit : I.objective y = I.objective y' +
      ∑ b, ∑ d, ∑ t, (if 0 < xU (I.clu b) then 0 else I.value b d t * y b d t) := by
    unfold objective
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : 0 < xU (I.clu b) <;> simp [y', h]
  have hE := obj_le I hI xU hU.1 x y hxy hsum1 hprec hy0 hx0
  have hobj : I.objective y ≤ I.objective y' := by linarith
  have hopt' : I.Optimal κ x' y' :=
    ⟨hfeas', fun x'' y'' h => (hbest x'' y'' h).trans hobj⟩
  have hlex : x' ≤ x := by
    intro c t
    by_cases h : 0 < xU c
    · simp [x', h]
    · simp only [x', h, if_false]; exact hx0 c t
  have hley : y' ≤ y := by
    intro b d t
    by_cases h : 0 < xU (I.clu b)
    · simp [y', h]
    · simp only [y', h, if_false]; exact hy0 b d t
  obtain ⟨hxeq, _⟩ := hmin x' y' hopt' hlex hley
  have hzero : ∀ t, x c t = 0 := by
    intro t
    have := congrFun (congrFun hxeq c) t
    simp only [x', hcU', if_false] at this
    exact this.symm
  simp [hzero] at hc'

#print axioms solution
