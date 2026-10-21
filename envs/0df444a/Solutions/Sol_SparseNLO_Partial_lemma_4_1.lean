-- Prove2me | solution 1 for SparseNLO.Partial.lemma_4_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:26:52.661616+00:00
-- url     : https://prove2.me/submissions/404a7f1d-e7f7-4e65-bb73-134e7d4ba3ec

import Mathlib
import Definitions.Def_SparseNLO_Partial_Method

set_option autoImplicit false
open scoped RealInnerProductSpace
open SparseNLO.Partial

theorem sn_Ms_eq {n s : ℕ} (hs : 0 < s) (hsn : s < n) (x : EuclideanSpace ℝ (Fin n))
    (hk : l0 x = s) (m : Fin n) (hm : m ∈ I1 x) (hmin : ∀ i ∈ I1 x, |x m| ≤ |x i|) :
    Ms s x = |x m| := by
  set M : Multiset ℝ := Finset.univ.val.map (fun i => |x i|) with hM
  set L : List ℝ := M.sort (fun a b : ℝ => b ≤ a) with hL
  have hperm : (L : Multiset ℝ) = M := Multiset.sort_eq _ _
  have hlen : L.length = n := by
    rw [hL, Multiset.length_sort]
    simp [hM]
  have hpw : L.Pairwise (fun a b : ℝ => b ≤ a) := Multiset.pairwise_sort _ _
  have hp : s - 1 < L.length := by omega
  have hMs : Ms s x = L[s - 1] := by
    unfold Ms
    rw [List.getD_eq_getElem _ _ hp]
  rw [hMs]
  have hcount : ∀ a : ℝ, L.countP (fun y => decide (a ≤ y)) = (Finset.univ.filter (fun i => a ≤ |x i|)).card := by
    intro a
    have h1 : (↑L : Multiset ℝ).countP (fun y => a ≤ y) = L.countP (fun y => decide (a ≤ y)) := by
      simp
    rw [← h1, hperm, hM, Multiset.countP_map]
    rfl
  have hI1card : (I1 x).card = s := hk
  have hxm : 0 < |x m| := by
    have : x m ≠ 0 := by simpa [I1] using hm
    positivity
  apply le_antisymm
  · by_contra hlt
    push Not at hlt
    -- hlt : |x m| < L[s-1]
    have hA : s ≤ L.countP (fun y => decide (L[s - 1] ≤ y)) := by
      have h1 : ((L.take s).countP (fun y => decide (L[s - 1] ≤ y))) = s := by
        rw [List.countP_eq_length.mpr]
        · simp; omega
        · intro y hy
          obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hy
          simp only [List.getElem_take, decide_eq_true_eq]
          have hq' : q < s := by simp at hq; omega
          by_cases hqe : q = s - 1
          · subst hqe; exact le_rfl
          · have := List.pairwise_iff_getElem.mp hpw q (s - 1) (by omega) hp (by omega)
            simpa using this
      exact h1.symm.trans_le (List.take_sublist _ _).countP_le
    rw [hcount] at hA
    have hsub : Finset.univ.filter (fun i => L[s - 1] ≤ |x i|) ⊆ (I1 x).erase m := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_erase, I1, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · rintro rfl; linarith
      · intro h0; rw [h0] at hi; simp at hi; linarith
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hm, hI1card] at this
    omega
  · by_contra hlt
    push Not at hlt
    -- hlt : L[s-1] < |x m|
    have hB : L.countP (fun y => decide (|x m| ≤ y)) ≤ s - 1 := by
      rw [← List.take_append_drop (s - 1) L, List.countP_append]
      have h1 : ((L.drop (s - 1)).countP (fun y => decide (|x m| ≤ y))) = 0 := by
        rw [List.countP_eq_zero]
        intro y hy
        obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hy
        simp only [List.getElem_drop, decide_eq_true_eq, not_le]
        by_cases hq0 : q = 0
        · subst hq0; simpa using hlt
        · have := List.pairwise_iff_getElem.mp hpw (s - 1) (s - 1 + q) hp (by simp at hq; omega) (by omega)
          exact lt_of_le_of_lt this hlt
      have h2 : ((L.take (s - 1)).countP (fun y => decide (|x m| ≤ y))) ≤ s - 1 := by
        refine List.countP_le_length.trans ?_
        simp
      omega
    rw [hcount] at hB
    have hsub : I1 x ⊆ Finset.univ.filter (fun i => |x m| ≤ |x i|) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmin i hi
    have := Finset.card_le_card hsub
    rw [hI1card] at this
    omega

theorem sn_local_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (i j : Fin n) (hij : i ≠ j) (x d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L2 / 2 * ‖d‖ ^ 2 := by
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hgrad : ∀ p w : EuclideanSpace ℝ (Fin n), fderiv ℝ f p w = ⟪gradient f p, w⟫ := by
    intro p w
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • d) d t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hphi : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (x + t • d)) (⟪gradient f (x + t • d), d⟫) t := by
    intro t
    have := (hdiff (x + t • d)).hasFDerivAt.comp_hasDerivAt t (hline t)
    rw [hgrad] at this
    exact this
  have hnorm : ‖d‖ ^ 2 = d i ^ 2 + d j ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_eq_add i j hij]
    · intro c _ h; simp [hd c h.1 h.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  have hinner : ∀ g : EuclideanSpace ℝ (Fin n), ⟪g, d⟫ = g i * d i + g j * d j := by
    intro g
    rw [PiLp.inner_apply, Finset.sum_eq_add i j hij]
    · simp [mul_comm]
    · intro c _ h; simp [hd c h.1 h.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  set ψ : ℝ → ℝ := fun t => f (x + t • d) - f x - t * ⟪gradient f x, d⟫
    - L2 / 2 * ‖d‖ ^ 2 * t ^ 2 with hψ
  have hψd : ∀ t : ℝ, HasDerivAt ψ (⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫
      - L2 * ‖d‖ ^ 2 * t) t := by
    intro t
    have h1 := ((hphi t).sub_const (f x)).sub ((hasDerivAt_id t).mul_const (⟪gradient f x, d⟫))
    have h2 := h1.sub ((hasDerivAt_pow 2 t).const_mul (L2 / 2 * ‖d‖ ^ 2))
    exact h2.congr_deriv (by norm_num; ring)
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 1) ?_ ?_ ?_
    · exact fun t _ => (hψd t).continuousAt.continuousWithinAt
    · exact fun t _ => (hψd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hψd t).deriv]
      have hloc := hL2 i j hij x (t • d) (by intro k h1 h2; simp [hd k h1 h2])
      have hnt : ‖t • d‖ = t * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      rw [hnt] at hloc
      set a := gradient f (x + t • d) i - gradient f x i with ha
      set b := gradient f (x + t • d) j - gradient f x j with hb
      have hs : Real.sqrt (a ^ 2 + b ^ 2) ≤ L2 * (t * ‖d‖) := by
        have : (gradient f x i - gradient f (x + t • d) i) ^ 2 + (gradient f x j - gradient f (x + t • d) j) ^ 2 = a ^ 2 + b ^ 2 := by
          simp only [ha, hb]; ring
        rw [this] at hloc
        exact hloc
      have hdd : ⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ = a * d i + b * d j := by
        rw [← inner_sub_left, hinner]
        simp [ha, hb]
      rw [hdd]
      have hsq : (a * d i + b * d j) ^ 2 ≤ (Real.sqrt (a ^ 2 + b ^ 2) * ‖d‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by positivity), hnorm]
        nlinarith [sq_nonneg (a * d j - b * d i)]
      have hle := (abs_le_of_sq_le_sq' hsq (by positivity)).2
      have hmul : Real.sqrt (a ^ 2 + b ^ 2) * ‖d‖ ≤ L2 * (t * ‖d‖) * ‖d‖ := by gcongr
      nlinarith
  have h01 := hanti (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [hψ] at h01
  simp only [zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, one_pow, mul_one, sub_self] at h01
  linarith

theorem sn_maxSq_le {n : ℕ} (S : Finset (Fin n)) (v : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (h : ∀ i ∈ S, v i ^ 2 ≤ c) (hc : 0 ≤ c) : maxSq S v ≤ c := by
  unfold maxSq
  have : (S.sup fun i => ‖v i‖₊ ^ 2 : NNReal) ≤ c.toNNReal := by
    refine Finset.sup_le fun i hi => ?_
    rw [← NNReal.coe_le_coe]
    simp only [NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs, Real.coe_toNNReal _ hc]
    exact h i hi
  have h2 := (NNReal.coe_le_coe.mpr this)
  rwa [Real.coe_toNNReal _ hc] at h2

theorem sn_le_maxSq {n : ℕ} (S : Finset (Fin n)) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hi : i ∈ S) : v i ^ 2 ≤ maxSq S v := by
  unfold maxSq
  have := Finset.le_sup (f := fun i => ‖v i‖₊ ^ 2) hi
  have h2 := NNReal.coe_le_coe.mpr this
  simpa using h2

theorem sn_le_maxAbs {n : ℕ} (S : Finset (Fin n)) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hi : i ∈ S) : |v i| ≤ maxAbs S v := by
  unfold maxAbs
  have := Finset.le_sup (f := fun i => ‖v i‖₊) hi
  have h2 := NNReal.coe_le_coe.mpr this
  simpa using h2

theorem sn_maxAbs_eq {n : ℕ} (S : Finset (Fin n)) (v : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hi : i ∈ S) (h : ∀ j ∈ S, |v j| ≤ |v i|) : maxAbs S v = |v i| := by
  apply le_antisymm
  · unfold maxAbs
    have : (S.sup fun i => ‖v i‖₊ : NNReal) ≤ ‖v i‖₊ := by
      refine Finset.sup_le fun j hj => ?_
      rw [← NNReal.coe_le_coe]
      simpa using h j hj
    have h2 := NNReal.coe_le_coe.mpr this
    simpa using h2
  · exact sn_le_maxAbs S v i hi

theorem sn_single_descent {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L2 : ℝ) (hL2 : LocalLipschitz f L2) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (t : ℝ) :
    f (x + EuclideanSpace.single i t) ≤ f x + gradient f x i * t + L2 / 2 * t ^ 2 := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hj⟩ := exists_ne i
  have := sn_local_descent f hf L2 hL2 i j hj.symm x
    (EuclideanSpace.single i t) (by intro k h1 h2; simp [EuclideanSpace.single_apply, h1])
  have e : ⟪gradient f x, EuclideanSpace.single i t⟫ = gradient f x i * t := by
    rw [EuclideanSpace.inner_single_right]; simp [mul_comm]
  rw [e] at this
  simpa using this

theorem sn_single_decrease {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L2 : ℝ) (hL2pos : 0 < L2) (hL2 : LocalLipschitz f L2) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    f (x + EuclideanSpace.single i (-(gradient f x i) / L2)) ≤ f x - gradient f x i ^ 2 / (2 * L2) := by
  have := sn_single_descent hn f hf L2 hL2 x i (-(gradient f x i) / L2)
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

/-- the step `StepAt` makes the new point at least as good as both candidates -/
theorem sn_stepAt_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xk xk1 : EuclideanSpace ℝ (Fin n)) (i1 : Fin n) (T1 : ℝ) (i2 m : Fin n) (T2 : ℝ)
    (h : StepAt f xk xk1 i1 T1 i2 m T2) :
    f xk1 ≤ f (xk + EuclideanSpace.single i1 T1) ∧
    f xk1 ≤ f (xk - EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 T2) := by
  obtain ⟨-, -, -, -, -, -, -, h8, h9⟩ := h
  by_cases hc : f (xk + EuclideanSpace.single i1 T1) <
      f (xk - EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 T2)
  · rw [h8 hc]
    exact ⟨le_rfl, hc.le⟩
  · rw [h9 hc]
    exact ⟨not_lt.mp hc, le_rfl⟩

theorem sn_step_4_10 {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L2 : ℝ) (hL2pos : 0 < L2) (hL2 : LocalLipschitz f L2)
    (xk xk1 : EuclideanSpace ℝ (Fin n)) (i1 : Fin n) (T1 : ℝ) (i2 m : Fin n) (T2 : ℝ)
    (h : StepAt f xk xk1 i1 T1 i2 m T2) :
    1 / (2 * L2) * maxSq (I1 xk) (gradient f xk) ≤ f xk - f xk1 := by
  have hn : 2 ≤ n := by omega
  have hle := (sn_stepAt_le f xk xk1 i1 T1 i2 m T2 h).1
  obtain ⟨hi1, hmin, -⟩ := h
  have key : ∀ i ∈ I1 xk, gradient f xk i ^ 2 / (2 * L2) ≤ f xk - f xk1 := by
    intro i hi
    have h1 := hmin i hi (-(gradient f xk i) / L2)
    have h2 := sn_single_decrease hn f hf L2 hL2pos hL2 xk i
    linarith
  have hc : ∀ i ∈ I1 xk, gradient f xk i ^ 2 ≤ 2 * L2 * (f xk - f xk1) := by
    intro i hi
    have := key i hi
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hc0 : 0 ≤ 2 * L2 * (f xk - f xk1) := (sq_nonneg _).trans (hc i1 hi1)
  have := sn_maxSq_le (I1 xk) (gradient f xk) _ hc hc0
  calc 1 / (2 * L2) * maxSq (I1 xk) (gradient f xk) ≤ 1 / (2 * L2) * (2 * L2 * (f xk - f xk1)) := by gcongr
    _ = f xk - f xk1 := by field_simp

theorem sn_step_4_13 {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (L2 : ℝ) (hL2pos : 0 < L2) (hL2 : LocalLipschitz f L2)
    (xk xk1 : EuclideanSpace ℝ (Fin n)) (hk : l0 xk = s) (i1 : Fin n) (T1 : ℝ) (i2 m : Fin n) (T2 : ℝ)
    (h : StepAt f xk xk1 i1 T1 i2 m T2) :
    Ms s xk * (maxAbs (I0 xk) (gradient f xk) - L2 * Ms s xk)
        + xk m * gradient f xk m ≤ f xk - f xk1 := by
  have hn : 2 ≤ n := by omega
  have hle := (sn_stepAt_le f xk xk1 i1 T1 i2 m T2 h).2
  obtain ⟨hi1, hmin, hi2, hmax, hm, hmmin, hT2, -, -⟩ := h
  have hMs : Ms s xk = |xk m| := sn_Ms_eq hs hsn xk hk m hm hmmin
  have hI0 : maxAbs (I0 xk) (gradient f xk) = |gradient f xk i2| := sn_maxAbs_eq _ _ i2 hi2 hmax
  have hne : m ≠ i2 := by
    rintro rfl
    simp [I1, I0] at hm hi2
    exact hm hi2
  set M := |xk m| with hMdef
  set g2 := gradient f xk i2 with hg2
  set t : ℝ := if 0 ≤ g2 then -M else M with ht
  have htg : t * g2 = -(M * |g2|) := by
    by_cases h0 : 0 ≤ g2
    · simp [ht, h0, abs_of_nonneg h0]
    · push Not at h0
      simp [ht, not_le.mpr h0, abs_of_neg h0]
  have ht2 : t ^ 2 = M ^ 2 := by
    by_cases h0 : 0 ≤ g2 <;> simp [ht, h0]
  have h1 := hT2 t
  have hd := sn_local_descent f hf L2 hL2 m i2 hne xk
    (-EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 t)
    (by
      intro k hk1 hk2
      simp [EuclideanSpace.single_apply, hk1, hk2])
  have e1 : xk + (-EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 t) =
      xk - EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 t := by abel
  rw [e1] at hd
  have e2 : ⟪gradient f xk, -EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 t⟫ =
      -(gradient f xk m * xk m) + gradient f xk i2 * t := by
    rw [inner_add_right, inner_neg_right, EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_right]
    simp [mul_comm]
  have e3 : ‖-EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 t‖ ^ 2 = xk m ^ 2 + t ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Finset.sum_eq_add m i2 hne]
    · simp [EuclideanSpace.single_apply, hne, hne.symm]
    · intro c _ hc
      simp [EuclideanSpace.single_apply, hc.1, hc.2]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [e2, e3] at hd
  have hMsq : xk m ^ 2 = M ^ 2 := by simp [hMdef]
  rw [hMs, hI0]
  rw [ht2, hMsq] at hd
  have : xk m * gradient f xk m = xk m * gradient f xk m := rfl
  nlinarith [h1, hd, hle, htg]

theorem solution {n s : ℕ} (hs : 0 < s) (hsn : s < n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2pos : 0 < L2) (hL2 : LocalLipschitz f L2)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsPartialRun f s x) :
    (∀ k : ℕ, l0 (x k) < s →
      1 / (2 * L2) * maxSq Finset.univ (gradient f (x k)) ≤ f (x k) - f (x (k + 1))) ∧
    (∀ k : ℕ, l0 (x k) = s → Aval f s L2 (x k) ≤ f (x k) - f (x (k + 1))) := by
  have hn : 2 ≤ n := by omega
  refine ⟨?_, ?_⟩
  · intro k hlt
    have hstep := (hrun.2 k).1 hlt
    have hall : ∀ (j : Fin n) (t' : ℝ), f (x (k + 1)) ≤ f (x k + EuclideanSpace.single j t') := by
      rcases hstep with ⟨i, t, h1, h2, h3⟩ | ⟨h1, h2⟩
      · exact h3
      · rw [h2]; exact h1
    have key : ∀ j : Fin n, gradient f (x k) j ^ 2 ≤ 2 * L2 * (f (x k) - f (x (k + 1))) := by
      intro j
      have h1 := hall j (-(gradient f (x k) j) / L2)
      have h2 := sn_single_decrease hn f hf L2 hL2pos hL2 (x k) j
      have h3 : gradient f (x k) j ^ 2 / (2 * L2) ≤ f (x k) - f (x (k + 1)) := by linarith
      rw [div_le_iff₀ (by positivity)] at h3
      linarith
    have hj0 : (⟨0, by omega⟩ : Fin n) ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have hc0 : 0 ≤ 2 * L2 * (f (x k) - f (x (k + 1))) := (sq_nonneg _).trans (key ⟨0, by omega⟩)
    have := sn_maxSq_le Finset.univ (gradient f (x k)) _ (fun j _ => key j) hc0
    calc 1 / (2 * L2) * maxSq Finset.univ (gradient f (x k))
        ≤ 1 / (2 * L2) * (2 * L2 * (f (x k) - f (x (k + 1)))) := by gcongr
      _ = f (x k) - f (x (k + 1)) := by field_simp
  · intro k hk
    obtain ⟨i1, T1, i2, m, T2, hstep⟩ := (hrun.2 k).2 hk
    have h410 := sn_step_4_10 hs hsn f hf L2 hL2pos hL2 _ _ i1 T1 i2 m T2 hstep
    have h413 := sn_step_4_13 hs hsn f hf L2 hL2pos hL2 _ _ hk i1 T1 i2 m T2 hstep
    obtain ⟨-, -, -, -, hm, hmmin, -, -, -⟩ := hstep
    have hMs : Ms s (x k) = |x k m| := sn_Ms_eq hs hsn (x k) hk m hm hmmin
    unfold Aval
    refine max_le h410 ?_
    have hgm : |gradient f (x k) m| ≤ maxAbs (I1 (x k)) (gradient f (x k)) := sn_le_maxAbs _ _ m hm
    have hM0 : 0 ≤ Ms s (x k) := by rw [hMs]; exact abs_nonneg _
    have h1 : -(Ms s (x k) * maxAbs (I1 (x k)) (gradient f (x k))) ≤ x k m * gradient f (x k) m := by
      have : |x k m * gradient f (x k) m| ≤ Ms s (x k) * maxAbs (I1 (x k)) (gradient f (x k)) := by
        rw [abs_mul, hMs]; gcongr
      exact (neg_le_of_abs_le this)
    nlinarith [h413, h1]
