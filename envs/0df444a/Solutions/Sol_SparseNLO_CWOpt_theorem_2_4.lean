-- Prove2me | solution 1 for SparseNLO.CWOpt.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T03:17:15.639221+00:00
-- url     : https://prove2.me/submissions/bdd7aba3-65fe-4f80-aff4-802dbd48dbe8

import Mathlib
import Definitions.Def_SparseNLO_CWOpt_Setting

open SparseNLO.CWOpt
open scoped RealInnerProductSpace

private lemma coord_min {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hm : ∀ t : ℝ, f x ≤ f (x + EuclideanSpace.single i t)) :
    gradient f x i = 0 := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i 1
  have he (t : ℝ) : t • e = EuclideanSpace.single i t := by
    ext j
    simp [e, PiLp.single_apply]
  have hd := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) (((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x)
  have hm' : IsLocalMin (fun t : ℝ => f (x + t • e)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    change f (x + (0 : ℝ) • e) ≤ f (x + t • e)
    rw [zero_smul, add_zero, he]
    exact hm t
  have hh := hm'.hasDerivAt_eq_zero hd
  simpa [← inner_gradient_left, e, EuclideanSpace.inner_single_right] using hh

private theorem bf_aux {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (xstar : EuclideanSpace ℝ (Fin n)) (hx : xstar ∈ Cs n s) (hcw : IsCWMin f s xstar) :
    IsBF f s xstar := by
  refine ⟨hx, ?_, ?_⟩
  · intro hlt
    rcases hcw.2 with h | h
    · ext i
      exact coord_min f hf xstar i (h.2 i)
    · omega
  · intro heq i hi
    rcases hcw.2 with h | h
    · omega
    · apply coord_min f hf xstar i
      intro t
      convert h.2 i hi i (xstar i + t) using 1
      congr 1
      ext j
      simp [PiLp.single_apply]
      split_ifs <;> simp_all <;> ring

private lemma pair_sq {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ) :
    ‖EuclideanSpace.single i a + EuclideanSpace.single j b‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real]
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply, hij, hij.symm, Real.norm_eq_abs]

private lemma pair_norm {n : ℕ} (i j : Fin n) (hij : i ≠ j) (a b : ℝ) :
    ‖EuclideanSpace.single i a + EuclideanSpace.single j b‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← pair_sq i j hij a b, Real.sqrt_sq (norm_nonneg _)]

private lemma support_pair {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) :
    d = EuclideanSpace.single i (d i) + EuclideanSpace.single j (d j) := by
  ext k
  by_cases hki : k = i
  · subst k
    simp [PiLp.single_apply, hij, hij.symm]
  · by_cases hkj : k = j
    · subst k
      simp [PiLp.single_apply, hij, hij.symm]
    · simp [PiLp.single_apply, hki, hkj, hd k hki hkj]

private lemma local_nonneg {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hL : LocalLipschitz f L) (i j : Fin n) (hij : i ≠ j) : 0 ≤ L := by
  have hh := hL i j hij 0 (EuclideanSpace.single i 1) (by
    intro k hki hkj
    simp [PiLp.single_apply, hki])
  simp only [PiLp.norm_single, Real.norm_eq_abs, abs_one, mul_one] at hh
  exact (Real.sqrt_nonneg _).trans hh

private lemma along_deriv {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (x d : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (x + u • d)) ⟪gradient f (x + t • d), d⟫ t := by
  convert! (hf.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const d).const_add x) using 1
  simp [inner_gradient_left]

private lemma along_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (L : ℝ) (hL : LocalLipschitz f L) (i j : Fin n) (hij : i ≠ j)
    (x d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) (t : ℝ) (ht : 0 ≤ t) :
    ⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ ≤ L * t * ‖d‖ ^ 2 := by
  let a := gradient f x i - gradient f (x + t • d) i
  let b := gradient f x j - gradient f (x + t • d) j
  let w := EuclideanSpace.single i a + EuclideanSpace.single j b
  have hnorm : ‖w‖ ≤ L * t * ‖d‖ := by
    have hh := hL i j hij x (t • d) (by
      intro k hki hkj
      simp [hd k hki hkj])
    simpa [w, a, b, pair_norm i j hij, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg ht, mul_assoc] using hh
  have hinner : ⟪w, d⟫ = ⟪gradient f x, d⟫ - ⟪gradient f (x + t • d), d⟫ := by
    have hg (g : EuclideanSpace ℝ (Fin n)) : ⟪g, d⟫ = d i * g i + d j * g j := by
      conv_lhs => rw [support_pair i j hij d hd]
      simp only [inner_add_right, EuclideanSpace.inner_single_right, conj_trivial]
    rw [hg (gradient f x), hg (gradient f (x + t • d))]
    simp only [w, a, b, inner_add_left, EuclideanSpace.inner_single_left, conj_trivial]
    ring
  have hh := (neg_le_abs ⟪w, d⟫).trans (abs_real_inner_le_norm w d)
  rw [hinner] at hh
  have hmul := mul_le_mul_of_nonneg_right hnorm (norm_nonneg d)
  nlinarith

private theorem descent_aux {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (i j : Fin n) (hij : i ≠ j) (x d : EuclideanSpace ℝ (Fin n))
    (hd : ∀ k : Fin n, k ≠ i → k ≠ j → d k = 0) :
    f (x + d) ≤ f x + ⟪gradient f x, d⟫ + L2 / 2 * ‖d‖ ^ 2 := by
  let q : ℝ → ℝ := fun t => f (x + t • d) - t * ⟪gradient f x, d⟫ -
    L2 / 2 * t ^ 2 * ‖d‖ ^ 2
  let q' : ℝ → ℝ := fun t => ⟪gradient f (x + t • d), d⟫ - ⟪gradient f x, d⟫ -
    L2 * t * ‖d‖ ^ 2
  have hq (t : ℝ) : HasDerivAt q (q' t) t := by
    convert! (along_deriv f hf x d t).sub ((hasDerivAt_id t).mul_const ⟪gradient f x, d⟫) |>.sub
      ((((hasDerivAt_id t).pow 2).const_mul (L2 / 2)).mul_const (‖d‖ ^ 2)) using 1 <;>
      simp only [q, q', id_eq] <;> ring
  have hanti : AntitoneOn q (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · exact (continuous_iff_continuousAt.mpr (fun t => (hq t).continuousAt)).continuousOn
    · intro t ht
      exact (hq t).hasDerivWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := (interior_subset ht).1
      have hh := along_bound f L2 hL2 i j hij x d hd t ht0
      dsimp [q']
      linarith
  have hh := hanti (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) zero_le_one
  dsimp [q] at hh
  simp only [one_smul, zero_smul, add_zero, zero_mul, one_mul, one_pow,
    zero_pow (by omega : 2 ≠ 0), mul_one, mul_zero, sub_zero] at hh
  linarith

private theorem swap_aux {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hcw : IsCWMin f s xstar) (hxs : l0 xstar = s)
    (i : Fin n) (hi : i ∈ I0 xstar) (m : Fin n) (hm : |xstar m| = Ms s xstar) :
    f (xstar - EuclideanSpace.single m (xstar m)
        - EuclideanSpace.single i ((SignType.sign (xstar m * gradient f xstar i) : ℝ) * xstar m))
      ≤ f xstar - (SignType.sign (xstar m * gradient f xstar i) : ℝ) * xstar m * gradient f xstar i
        + L2 * xstar m ^ 2 := by
  classical
  by_cases hm0 : xstar m = 0
  · have hz (k : Fin n) : EuclideanSpace.single k (0 : ℝ) = (0 : EuclideanSpace ℝ (Fin n)) := by
      ext j
      simp [PiLp.single_apply]
    simp [hm0, hz]
  have hi0 : xstar i = 0 := (Finset.mem_filter.mp hi).2
  have hmi : m ≠ i := by intro h; exact hm0 (h ▸ hi0)
  have hg : gradient f xstar m = 0 :=
    (bf_aux f hf hbdd hs hsn xstar hcw.1 hcw).2.2 hxs m (by simp [I1, hm0])
  let σ : ℝ := SignType.sign (xstar m * gradient f xstar i)
  let d : EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.single m (-xstar m) + EuclideanSpace.single i (-σ * xstar m)
  have hd : ∀ k : Fin n, k ≠ m → k ≠ i → d k = 0 := by
    intro k hkm hki
    simp [d, PiLp.single_apply, hkm, hki]
  have heq : xstar + d = xstar - EuclideanSpace.single m (xstar m) -
      EuclideanSpace.single i (σ * xstar m) := by
    ext k
    simp [d, PiLp.single_apply]
    split_ifs <;> ring
  have hg' : ⟪gradient f xstar, d⟫ = -σ * xstar m * gradient f xstar i := by
    simp only [d, inner_add_right, EuclideanSpace.inner_single_right, conj_trivial, hg]
    ring
  have hσ : σ ^ 2 ≤ 1 := by
    dsimp [σ]
    generalize SignType.sign (xstar m * gradient f xstar i) = v
    cases v <;> norm_num
  have hsq : ‖d‖ ^ 2 ≤ 2 * xstar m ^ 2 := by
    rw [show d = EuclideanSpace.single m (-xstar m) +
      EuclideanSpace.single i (-σ * xstar m) from rfl, pair_sq m i hmi]
    have hh := mul_le_mul_of_nonneg_right hσ (sq_nonneg (xstar m))
    nlinarith
  have hL0 := local_nonneg f L2 hL2 m i hmi
  have hbound := mul_le_mul_of_nonneg_left hsq (div_nonneg hL0 (by norm_num : (0 : ℝ) ≤ 2))
  have hh := descent_aux f hf hbdd Lf hLf L2 hL2 m i hmi xstar d hd
  rw [heq, hg'] at hh
  change f (xstar - EuclideanSpace.single m (xstar m) - EuclideanSpace.single i (σ * xstar m))
    ≤ f xstar - σ * xstar m * gradient f xstar i + L2 * xstar m ^ 2
  linarith

private lemma getD_nonneg (l : List ℝ) (h : ∀ a ∈ l, 0 ≤ a) (k : ℕ) :
    0 ≤ l.getD k 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simpa using h a (by simp)
    | succ k => simpa using ih (fun a ha => h a (by simp [ha])) k

private lemma getD_mem_or_zero (l : List ℝ) (k : ℕ) :
    l.getD k 0 ∈ l ∨ l.getD k 0 = 0 := by
  induction l generalizing k with
  | nil => simp
  | cons a l ih =>
    cases k with
    | zero => simp
    | succ k =>
      simpa only [List.getD_cons_succ, List.mem_cons] using
        (ih k).imp (fun h => Or.inr h) id

private lemma sorted_getD_pos (l : List ℝ) (hsort : l.Pairwise (fun a b => b ≤ a))
    (k : ℕ) (hk : k < l.countP (fun a => decide (0 < a))) : 0 < l.getD k 0 := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    rcases List.pairwise_cons.mp hsort with ⟨ha, hl⟩
    cases k with
    | zero =>
      obtain ⟨b, hb, hbp⟩ := List.countP_pos_iff.mp hk
      have hb0 : 0 < b := of_decide_eq_true hbp
      rcases List.mem_cons.mp hb with rfl | hb
      · simpa using hb0
      · simpa using hb0.trans_le (ha b hb)
    | succ k =>
      have hh : k < l.countP (fun a => decide (0 < a)) := by
        rw [List.countP_cons] at hk
        split_ifs at hk <;> omega
      simpa using ih hl k hh

private lemma ms_nonneg {n : ℕ} (s : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ Ms s x := by
  apply getD_nonneg
  intro a ha
  simp only [Multiset.mem_sort, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at ha
  obtain ⟨i, rfl⟩ := ha
  exact abs_nonneg _

private lemma ms_pos {n s : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hs : 0 < s)
    (hxs : l0 x = s) : 0 < Ms s x := by
  classical
  let l := (Finset.univ.val.map (fun i : Fin n => |x i|)).sort (fun a b : ℝ => b ≤ a)
  have hc : l.countP (fun a => decide (0 < a)) = s := by
    change Multiset.countP (fun a : ℝ => 0 < a)
      (↑((Finset.univ.val.map (fun i : Fin n => |x i|)).sort
        (fun a b : ℝ => b ≤ a)) : Multiset ℝ) = s
    rw [Multiset.sort_eq, Multiset.countP_map]
    simpa only [l0, Finset.card_def, Finset.filter_val, abs_pos] using hxs
  apply sorted_getD_pos l (Multiset.pairwise_sort _ _) (s - 1)
  rw [hc]
  omega

private lemma ms_exists {n s : ℕ} (x : EuclideanSpace ℝ (Fin n)) (hs : 0 < s)
    (hxs : l0 x = s) : ∃ m : Fin n, x m ≠ 0 ∧ |x m| = Ms s x := by
  have hp := ms_pos x hs hxs
  rcases getD_mem_or_zero ((Finset.univ.val.map (fun i : Fin n => |x i|)).sort
      (fun a b : ℝ => b ≤ a)) (s - 1) with h | h
  · simp only [Multiset.mem_sort, Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
      true_and] at h
    obtain ⟨m, hm⟩ := h
    refine ⟨m, ?_, hm⟩
    apply abs_pos.mp
    rw [hm]
    exact hp
  · change Ms s x = 0 at h
    linarith

theorem solution {n s : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hbdd : ∃ γ : ℝ, ∀ x, γ ≤ f x) (hs : 0 < s) (hsn : s < n)
    (Lf : NNReal) (hLf : LipschitzWith Lf (gradient f))
    (L2 : ℝ) (hL2 : LocalLipschitz f L2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hcw : IsCWMin f s xstar) :
    (∀ i ∈ I0 xstar, |gradient f xstar i| ≤ L2 * Ms s xstar) ∧
      (∀ i ∈ I1 xstar, gradient f xstar i = 0) := by
  classical
  have hbf := bf_aux f hf hbdd hs hsn xstar hcw.1 hcw
  have hL0 : 0 ≤ L2 := local_nonneg f L2 hL2
    ⟨0, by omega⟩ ⟨1, by omega⟩ (by intro h; have := congrArg Fin.val h; simp at this)
  rcases hcw.2 with h | h
  · have hg := hbf.2.1 h.1
    constructor
    · intro i hi
      simpa [hg] using mul_nonneg hL0 (ms_nonneg s xstar)
    · intro i hi
      simp [hg]
  · refine ⟨?_, hbf.2.2 h.1⟩
    intro i hi
    obtain ⟨m, hm0, hm⟩ := ms_exists xstar hs h.1
    have hm1 : m ∈ I1 xstar := by simp [I1, hm0]
    let σ : ℝ := SignType.sign (xstar m * gradient f xstar i)
    have hmin := h.2 m hm1 i (-σ * xstar m)
    have heq : xstar - EuclideanSpace.single m (xstar m) +
        EuclideanSpace.single i (-σ * xstar m) =
      xstar - EuclideanSpace.single m (xstar m) - EuclideanSpace.single i (σ * xstar m) := by
      ext k
      simp [PiLp.single_apply]
      split_ifs <;> ring
    rw [heq] at hmin
    have hh := swap_aux f hf hbdd hs hsn Lf hLf L2 hL2 xstar hcw h.1 i hi m hm
    change f (xstar - EuclideanSpace.single m (xstar m) - EuclideanSpace.single i (σ * xstar m))
      ≤ f xstar - σ * xstar m * gradient f xstar i + L2 * xstar m ^ 2 at hh
    have hsign : σ * xstar m * gradient f xstar i = |xstar m| * |gradient f xstar i| := by
      calc
        σ * xstar m * gradient f xstar i = σ * (xstar m * gradient f xstar i) := by ring
        _ = |xstar m * gradient f xstar i| := sign_mul_self _
        _ = |xstar m| * |gradient f xstar i| := abs_mul _ _
    rw [hsign] at hh
    have hab : 0 < |xstar m| := abs_pos.mpr hm0
    rw [← hm]
    apply (mul_le_mul_iff_right₀ hab).mp
    have hsq : xstar m ^ 2 = |xstar m| * |xstar m| := by rw [← sq, sq_abs]
    rw [hsq] at hh
    nlinarith

