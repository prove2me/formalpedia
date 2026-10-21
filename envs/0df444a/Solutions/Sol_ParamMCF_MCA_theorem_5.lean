-- Prove2me | solution 1 for ParamMCF.MCA.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T23:58:46.712386+00:00
-- url     : https://prove2.me/submissions/43e392d7-da64-4057-94f2-f908226bf8d7

import Mathlib
import Definitions.Def_ParamMCF_MCA_Model
import Theorems.Thm_ParamMCF_MCA_lemma_4
import Theorems.Thm_ParamMCF_MCA_eq_18
import Theorems.Thm_ParamMCF_MCA_spline_abs_ge
import Theorems.Thm_ParamMCF_MCA_max_f2_eq

namespace ParamMCF.MCA

/-- A continuous function that is nonpositive on negatives is nonpositive at zero. -/
lemma pmcf_nonpos_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, s < 0 → φ s ≤ 0) :
    φ 0 ≤ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Iio 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- A continuous function that is nonnegative on positives is nonnegative at zero. -/
lemma pmcf_nonneg_at_zero (φ : ℝ → ℝ) (hφ : ContinuousAt φ 0) (h : ∀ s, 0 < s → 0 ≤ φ s) :
    0 ≤ φ 0 := by
  have ht : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds (φ 0)) :=
    hφ.tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => h s hs)

/-- Under the shape condition, `g'' = 0` on `(-∞, 0]`. -/
lemma pmcf_f2_zero_nonpos (g : ℝ → ℝ)
    (hg3 : Differentiable ℝ (deriv g) ∧ Differentiable ℝ (deriv (deriv g)))
    (hshape : MonotoneOn (deriv (deriv g)) (Set.Ici 0) ∧
      (∀ x, 0 ≤ x → 0 ≤ deriv (deriv g) x) ∧
      AntitoneOn (deriv (deriv g)) (Set.Iio 0) ∧
      (∀ x, x < 0 → deriv (deriv g) x ≤ 0)) :
    ∀ x, x ≤ 0 → deriv (deriv g) x = 0 := by
  have hc : Continuous (deriv (deriv g)) := hg3.2.continuous
  have h0 : deriv (deriv g) 0 = 0 := le_antisymm
    (pmcf_nonpos_at_zero _ hc.continuousAt hshape.2.2.2) (hshape.2.1 0 le_rfl)
  intro x hx
  rcases eq_or_lt_of_le hx with h | h
  · rw [h, h0]
  · apply le_antisymm (hshape.2.2.2 x h)
    have ht : Filter.Tendsto (deriv (deriv g)) (nhdsWithin 0 (Set.Iio 0))
        (nhds (deriv (deriv g) 0)) := hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hle : deriv (deriv g) 0 ≤ deriv (deriv g) x := by
      apply le_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsLT h] with y hy
      exact hshape.2.2.1 (Set.mem_Iio.2 h) (Set.mem_Iio.2 hy.2) hy.1.le
    linarith [hshape.2.1 0 le_rfl]

/-- On a closed mesh interval, the spline coincides with that interval's chord. -/
lemma pmcf_linSpline_eq_piece (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (g : ℝ → ℝ) (i : Fin K) (x : ℝ) (hx : x ∈ Set.Icc (xs i.castSucc) (xs i.succ)) :
    linSpline K xs g x = splinePiece K xs g i x := by
  have hK : 0 < K := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  unfold linSpline
  rw [dif_pos hK]
  have hmem : i ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := by
    simp [hx.2]
  have hne : (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).Nonempty := ⟨i, hmem⟩
  simp only
  rw [dif_pos hne]
  set j := (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).min' hne with hj
  have hjmem : j ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := Finset.min'_mem _ _
  have hjx : x ≤ xs j.succ := (Finset.mem_filter.1 hjmem).2
  have hji : j ≤ i := Finset.min'_le _ _ hmem
  rcases eq_or_lt_of_le hji with h | h
  · rw [h]
  · have hle : j.succ ≤ i.castSucc := by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.val_castSucc]; exact h
    have h1 : xs j.succ ≤ xs i.castSucc := hxs.monotone hle
    have hxe : x = xs j.succ := le_antisymm hjx (h1.trans hx.1)
    have hxe' : x = xs i.castSucc := le_antisymm (hjx.trans h1) hx.1
    unfold splinePiece
    have hne1 : xs j.succ - xs j.castSucc ≠ 0 :=
      sub_ne_zero.2 (hxs (Fin.castSucc_lt_succ (i := j))).ne'
    rw [show x - xs i.castSucc = 0 by rw [hxe']; ring, zero_div, zero_mul, add_zero]
    rw [show x - xs j.castSucc = xs j.succ - xs j.castSucc by rw [hxe], div_self hne1, one_mul]
    rw [show xs i.castSucc = xs j.succ by rw [← hxe, ← hxe']]
    ring

/-- Every point of `[x_0, x_K]` lies in some closed mesh interval. -/
lemma pmcf_exists_interval (K : ℕ) (xs : Fin (K + 1) → ℝ) (hK : 0 < K) (x : ℝ)
    (hl : x ≤ xs (Fin.last K)) (h0 : xs 0 ≤ x) :
    ∃ i : Fin K, x ∈ Set.Icc (xs i.castSucc) (xs i.succ) := by
  have hmem : (⟨K - 1, Nat.sub_lt hK one_pos⟩ : Fin K) ∈
      Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := by
    have : (⟨K - 1, Nat.sub_lt hK one_pos⟩ : Fin K).succ = Fin.last K := by
      ext; simp; omega
    simp [this, hl]
  have hne : (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).Nonempty := ⟨_, hmem⟩
  set i := (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).min' hne with hi
  have himem : i ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := Finset.min'_mem _ _
  refine ⟨i, ?_, (Finset.mem_filter.1 himem).2⟩
  rcases Nat.eq_zero_or_pos i.val with h | h
  · have : i.castSucc = 0 := by ext; simp [h]
    rw [this]; exact h0
  · set j : Fin K := ⟨i.val - 1, by omega⟩ with hj
    have hjs : j.succ = i.castSucc := by ext; simp [hj]; omega
    by_contra hcon
    push_neg at hcon
    have hjmem : j ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [hjs]; exact hcon.le
    have := Finset.min'_le _ _ hjmem
    rw [← hi, Fin.le_def] at this
    simp [hj] at this
    omega

/-- If `0` is a mesh point, no mesh interval straddles `0`. -/
lemma pmcf_side (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (hzero : ∃ j, xs j = 0)
    (i : Fin K) : xs i.succ ≤ 0 ∨ 0 ≤ xs i.castSucc := by
  obtain ⟨j, hj⟩ := hzero
  by_contra hcon
  push_neg at hcon
  have h1 : i.castSucc < j := hxs.lt_iff_lt.1 (by rw [hj]; exact hcon.2)
  have h2 : j < i.succ := hxs.lt_iff_lt.1 (by rw [hj]; exact hcon.1)
  rw [Fin.lt_def] at h1 h2
  simp at h1 h2
  omega

/-- A marginal cost vanishes at zero. -/
lemma pmcf_g_zero (g : ℝ → ℝ) (hg : IsMarginalCost g) : g 0 = 0 :=
  le_antisymm (pmcf_nonpos_at_zero g (hg.2.1.continuous.continuousAt) hg.2.2.2)
    (pmcf_nonneg_at_zero g (hg.2.1.continuous.continuousAt) hg.2.2.1)

lemma pmcf_g_nonneg (g : ℝ → ℝ) (hg : IsMarginalCost g) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ g x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, pmcf_g_zero g hg]
  · exact hg.2.2.1 x h

lemma pmcf_g_nonpos (g : ℝ → ℝ) (hg : IsMarginalCost g) (x : ℝ) (hx : x ≤ 0) : g x ≤ 0 := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [h, pmcf_g_zero g hg]
  · exact hg.2.2.2 x h

lemma pmcf_piece_strictMono (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs)
    (g : ℝ → ℝ) (hg : StrictMono g) (i : Fin K) : StrictMono (splinePiece K xs g i) := by
  intro x y hxy
  unfold splinePiece
  have hlt : xs i.castSucc < xs i.succ := hxs (Fin.castSucc_lt_succ (i := i))
  have h1 : 0 < g (xs i.succ) - g (xs i.castSucc) := sub_pos.2 (hg hlt)
  have h2 : (x - xs i.castSucc) / (xs i.succ - xs i.castSucc) <
      (y - xs i.castSucc) / (xs i.succ - xs i.castSucc) :=
    div_lt_div_of_pos_right (by linarith) (sub_pos.2 hlt)
  have := mul_lt_mul_of_pos_right h2 h1
  linarith

lemma pmcf_piece_cont (K : ℕ) (xs : Fin (K + 1) → ℝ) (g : ℝ → ℝ) (i : Fin K) :
    Continuous (splinePiece K xs g i) := by
  unfold splinePiece
  fun_prop

lemma pmcf_linSpline_left (K : ℕ) (xs : Fin (K + 1) → ℝ) (g : ℝ → ℝ) (hK : 0 < K) (x : ℝ)
    (hx : x ≤ xs (⟨0, hK⟩ : Fin K).succ) :
    linSpline K xs g x = splinePiece K xs g ⟨0, hK⟩ x := by
  unfold linSpline
  rw [dif_pos hK]
  have hmem : (⟨0, hK⟩ : Fin K) ∈ Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hx
  have hne : (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).Nonempty := ⟨_, hmem⟩
  simp only
  rw [dif_pos hne]
  have hle := Finset.min'_le _ _ hmem
  have : (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).min' hne = ⟨0, hK⟩ := by
    apply le_antisymm hle
    rw [Fin.le_def]; exact Nat.zero_le _
  rw [this]

lemma pmcf_linSpline_right (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (g : ℝ → ℝ)
    (hK : 0 < K) (x : ℝ) (hx : xs (Fin.last K) < x) :
    linSpline K xs g x = splinePiece K xs g ⟨K - 1, Nat.sub_lt hK one_pos⟩ x := by
  unfold linSpline
  rw [dif_pos hK]
  have hne : ¬ (Finset.univ.filter (fun j : Fin K => x ≤ xs j.succ)).Nonempty := by
    rintro ⟨j, hj⟩
    have h1 := (Finset.mem_filter.1 hj).2
    have h2 : xs j.succ ≤ xs (Fin.last K) := hxs.monotone (Fin.le_last _)
    linarith
  simp only
  rw [dif_neg hne]

lemma pmcf_last_eq (K : ℕ) (hK : 0 < K) :
    (⟨K - 1, Nat.sub_lt hK one_pos⟩ : Fin K).succ = Fin.last K := by
  ext; simp; omega

/-- The spline is continuous and strictly increasing on `(-∞, x_{k+1}]`. -/
lemma pmcf_spline_prefix (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (g : ℝ → ℝ)
    (hg : StrictMono g) :
    ∀ k (hk : k < K), StrictMonoOn (linSpline K xs g) (Set.Iic (xs (⟨k, hk⟩ : Fin K).succ)) ∧
      ContinuousOn (linSpline K xs g) (Set.Iic (xs (⟨k, hk⟩ : Fin K).succ)) := by
  intro k
  induction k with
  | zero =>
    intro hk
    have heq : Set.EqOn (splinePiece K xs g ⟨0, hk⟩) (linSpline K xs g)
        (Set.Iic (xs (⟨0, hk⟩ : Fin K).succ)) :=
      fun x hx => (pmcf_linSpline_left K xs g hk x hx).symm
    exact ⟨((pmcf_piece_strictMono K xs hxs g hg _).strictMonoOn _).congr heq,
      ((pmcf_piece_cont K xs g _).continuousOn).congr heq.symm⟩
  | succ k ih =>
    intro hk
    obtain ⟨ihm, ihc⟩ := ih (by omega)
    set i : Fin K := ⟨k + 1, hk⟩
    have hcs : (⟨k, by omega⟩ : Fin K).succ = i.castSucc := by ext; simp [i]
    have hlt : xs i.castSucc < xs i.succ := hxs (Fin.castSucc_lt_succ (i := i))
    have heq : Set.EqOn (splinePiece K xs g i) (linSpline K xs g)
        (Set.Icc (xs i.castSucc) (xs i.succ)) :=
      fun x hx => (pmcf_linSpline_eq_piece K xs hxs g i x hx).symm
    rw [hcs] at ihm ihc
    have hU : Set.Iic (xs i.castSucc) ∪ Set.Icc (xs i.castSucc) (xs i.succ) =
        Set.Iic (xs i.succ) := Set.Iic_union_Icc_eq_Iic hlt.le
    rw [← hU]
    refine ⟨ihm.union (((pmcf_piece_strictMono K xs hxs g hg i).strictMonoOn _).congr heq)
      isGreatest_Iic (isLeast_Icc hlt.le), ?_⟩
    exact ihc.union_of_isClosed (((pmcf_piece_cont K xs g i).continuousOn).congr heq.symm)
      isClosed_Iic isClosed_Icc

/-- The spline of a strictly increasing function on a nontrivial mesh is continuous and
strictly increasing. -/
lemma pmcf_spline_cont_mono (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (g : ℝ → ℝ)
    (hg : StrictMono g) (hK : 0 < K) :
    Continuous (linSpline K xs g) ∧ StrictMono (linSpline K xs g) := by
  obtain ⟨hm, hc⟩ := pmcf_spline_prefix K xs hxs g hg (K - 1) (Nat.sub_lt hK one_pos)
  rw [pmcf_last_eq K hK] at hm hc
  set j : Fin K := ⟨K - 1, Nat.sub_lt hK one_pos⟩
  have heq : Set.EqOn (splinePiece K xs g j) (linSpline K xs g) (Set.Ici (xs (Fin.last K))) := by
    intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.1 hx) with h | h
    · rw [← h]
      have hl : xs j.castSucc < xs j.succ := hxs (Fin.castSucc_lt_succ (i := j))
      rw [pmcf_last_eq K hK] at hl
      have := pmcf_linSpline_eq_piece K xs hxs g j (xs (Fin.last K))
        ⟨hl.le, by rw [pmcf_last_eq K hK]⟩
      exact this.symm
    · exact (pmcf_linSpline_right K xs hxs g hK x h).symm
  have hU : Set.Iic (xs (Fin.last K)) ∪ Set.Ici (xs (Fin.last K)) = Set.univ := Set.Iic_union_Ici
  have hm' := hm.union (((pmcf_piece_strictMono K xs hxs g hg j).strictMonoOn _).congr heq)
    isGreatest_Iic isLeast_Ici
  have hc' := hc.union_of_isClosed (((pmcf_piece_cont K xs g j).continuousOn).congr heq.symm)
    isClosed_Iic isClosed_Ici
  rw [hU] at hm' hc'
  exact ⟨continuousOn_univ.1 hc', strictMonoOn_univ.1 hm'⟩

/-- The spline interpolates at mesh points. -/
lemma pmcf_spline_node (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (g : ℝ → ℝ)
    (hK : 0 < K) (j : Fin (K + 1)) : linSpline K xs g (xs j) = g (xs j) := by
  rcases Nat.eq_zero_or_pos j.val with h | h
  · set i : Fin K := ⟨0, hK⟩
    have hj : j = i.castSucc := by ext; simp [i, h]
    have hl : xs i.castSucc < xs i.succ := hxs (Fin.castSucc_lt_succ (i := i))
    rw [hj, pmcf_linSpline_eq_piece K xs hxs g i _ ⟨le_rfl, hl.le⟩]
    unfold splinePiece; simp
  · set i : Fin K := ⟨j.val - 1, by omega⟩
    have hj : j = i.succ := by ext; simp [i]; omega
    have hl : xs i.castSucc < xs i.succ := hxs (Fin.castSucc_lt_succ (i := i))
    rw [hj, pmcf_linSpline_eq_piece K xs hxs g i _ ⟨hl.le, le_rfl⟩]
    unfold splinePiece
    rw [div_self (sub_ne_zero.2 hl.ne'), one_mul]; ring

/-- The spline of a marginal cost on a mesh containing `0` is a continuous marginal cost. -/
lemma pmcf_spline_marginal (K : ℕ) (xs : Fin (K + 1) → ℝ) (hxs : StrictMono xs) (g : ℝ → ℝ)
    (hg : IsMarginalCost g) (hK : 0 < K) (hzero : ∃ j, xs j = 0) :
    IsContinuousMarginalCost (linSpline K xs g) := by
  obtain ⟨hc, hm⟩ := pmcf_spline_cont_mono K xs hxs g hg.1 hK
  obtain ⟨j, hj⟩ := hzero
  have h0 : linSpline K xs g 0 = 0 := by
    rw [← hj, pmcf_spline_node K xs hxs g hK j, hj, pmcf_g_zero g hg]
  refine ⟨hc, hm, fun s hs => ?_, fun s hs => ?_⟩
  · rw [← h0]; exact (hm hs).le
  · rw [← h0]; exact (hm hs).le

lemma pmcf_sq_bound (δ A Q : ℝ) (hδ : 0 ≤ δ) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (h : δ * Real.sqrt A ≤ 2 * Real.sqrt 2 * Real.sqrt Q) : δ ^ 2 * A ≤ 8 * Q := by
  have := pow_le_pow_left₀ (mul_nonneg hδ (Real.sqrt_nonneg _)) h 2
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hQ,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at this
  nlinarith

theorem theorem_5_red {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (hG : G.IsAdmissible) (directed : Bool)
    (f : E → ℝ → ℝ) (hf : ∀ e, IsMarginalCost (f e))
    (hf3 : ∀ e, Differentiable ℝ (deriv (f e)) ∧
      Differentiable ℝ (deriv (deriv (f e))))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (alpha beta lamMax : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta)
    (hlamMax : 0 < lamMax) (hX : 0 < xmax b0 b lamMax)
    (K : E → ℕ) (xs : (e : E) → Fin (K e + 1) → ℝ)
    (hxs : ∀ e, StrictMono (xs e))
    (hfirst : ∀ e, xs e 0 = -xmax b0 b lamMax)
    (hlast : ∀ e, xs e (Fin.last (K e)) = xmax b0 b lamMax)
    (hzero : ∀ e, ∃ j, xs e j = 0)
    (hstep :
      (∀ e (i : Fin (K e)),
        let xi := xs e i.castSucc
        let xn := xs e i.succ
        let delta := xn - xi
        delta * Real.sqrt
            (sSup ((fun ξ => |deriv (deriv (f e)) ξ|) '' Set.Icc xi (xn + delta))) ≤
          2 * Real.sqrt 2 * Real.sqrt
            ((alpha - 1) / (1 + alpha) * min |f e xi| |f e xn| +
              beta / ((1 + alpha) * (Fintype.card E : ℝ) * xmax b0 b lamMax))) ∨
      ((∀ e,
          MonotoneOn (deriv (deriv (f e))) (Set.Ici 0) ∧
          (∀ x, 0 ≤ x → 0 ≤ deriv (deriv (f e)) x) ∧
          AntitoneOn (deriv (deriv (f e))) (Set.Iio 0) ∧
          (∀ x, x < 0 → deriv (deriv (f e)) x ≤ 0)) ∧
        ∀ e (i : Fin (K e)),
          let xi := xs e i.castSucc
          let xn := xs e i.succ
          let delta := xn - xi
          delta * max (Real.sqrt |deriv (deriv (f e)) xi|)
              (Real.sqrt |deriv (deriv (f e)) xn|) ≤
            2 * Real.sqrt 2 * Real.sqrt
              ((alpha - 1) * |f e xi| +
                beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax))))
    (xt : ℝ → E → ℝ)
    (hxt : ∀ lam ∈ Set.Icc 0 lamMax,
      IsMinCostFlow G directed (fun e => linSpline (K e) (xs e) (f e))
        (demand b0 b lam) (xt lam)) :
    IsApproxMinCostFlowFun G directed f b0 b lamMax alpha beta xt  := by
  have hK : ∀ e, 0 < K e := by
    intro e
    by_contra h
    have h0 : K e = 0 := by omega
    have h1 := hfirst e
    have h2 := hlast e
    have hl : Fin.last (K e) = 0 := Fin.ext (by simp [h0])
    rw [hl, h1] at h2
    linarith
  have hft : ∀ e, IsContinuousMarginalCost (linSpline (K e) (xs e) (f e)) := fun e =>
    pmcf_spline_marginal _ _ (hxs e) _ (hf e) (hK e) (hzero e)
  have ha1 : 0 < 1 + alpha := by linarith
  have hcX : 0 ≤ (Fintype.card E : ℝ) * xmax b0 b lamMax :=
    mul_nonneg (Nat.cast_nonneg _) hX.le
  refine lemma_4 G hG directed f (fun e => linSpline (K e) (xs e) (f e)) hf hft b0 b hb0 hb
    alpha beta lamMax halpha hbeta hlamMax hX ?_ xt hxt
  rcases hstep with hi | ⟨hshape, hii⟩
  · left
    intro e x hx
    obtain ⟨i, hxi⟩ := pmcf_exists_interval (K e) (xs e) (hK e) x
      (by rw [hlast e]; exact hx.2) (by rw [hfirst e]; exact hx.1)
    have hs := hi e i
    dsimp only at hs
    have hab : xs e i.castSucc < xs e i.succ := hxs e (Fin.castSucc_lt_succ (i := i))
    set a := xs e i.castSucc with ha
    set bb := xs e i.succ with hbb
    have hcont2 : Continuous (fun ξ => |deriv (deriv (f e)) ξ|) := (hf3 e).2.continuous.abs
    have hbdd : BddAbove ((fun ξ => |deriv (deriv (f e)) ξ|) '' Set.Icc a (bb + (bb - a))) :=
      (isCompact_Icc.image hcont2).bddAbove
    set M := sSup ((fun ξ => |deriv (deriv (f e)) ξ|) '' Set.Icc a (bb + (bb - a))) with hM
    have hMb : ∀ ξ ∈ Set.Icc a bb, |deriv (deriv (f e)) ξ| ≤ M := fun ξ hξ =>
      le_csSup hbdd ⟨ξ, ⟨hξ.1, by linarith [hξ.2]⟩, rfl⟩
    have h18 := eq_18 (f e) ⟨(hf e).2.1, (hf3 e).1⟩ (K e) (xs e) (hxs e) i x M hxi hMb
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMb a ⟨le_rfl, hab.le⟩)
    have hc0 : 0 ≤ (alpha - 1) / (1 + alpha) := div_nonneg (by linarith) ha1.le
    have hd0 : 0 ≤ beta / ((1 + alpha) * (Fintype.card E : ℝ) * xmax b0 b lamMax) :=
      div_nonneg hbeta (by rw [mul_assoc]; exact mul_nonneg ha1.le hcX)
    have hQ0 : 0 ≤ (alpha - 1) / (1 + alpha) * min |f e a| |f e bb| +
        beta / ((1 + alpha) * (Fintype.card E : ℝ) * xmax b0 b lamMax) :=
      add_nonneg (mul_nonneg hc0 (le_min (abs_nonneg _) (abs_nonneg _))) hd0
    have hsq := pmcf_sq_bound _ _ _ (sub_nonneg.2 hab.le) hM0 hQ0 hs
    have hmin : min |f e a| |f e bb| ≤ |f e x| := by
      have hmono := (hf e).1.monotone
      rcases pmcf_side (K e) (xs e) (hxs e) (hzero e) i with hside | hside
      · have h1 := hmono hxi.2
        have h2 := pmcf_g_nonpos (f e) (hf e) bb hside
        rw [abs_of_nonpos (h1.trans h2), abs_of_nonpos h2]
        exact min_le_of_right_le (by linarith)
      · have h1 := hmono hxi.1
        have h2 := pmcf_g_nonneg (f e) (hf e) a hside
        rw [abs_of_nonneg (h2.trans h1), abs_of_nonneg h2]
        exact min_le_of_left_le h1
    rw [abs_sub_comm]
    have := mul_le_mul_of_nonneg_left hmin hc0
    nlinarith
  · right
    intro e x hx
    refine ⟨spline_abs_ge (f e) (hf e) (hf3 e) (hshape e) _ (K e) (xs e) (hxs e) (hfirst e)
      (hlast e) (hzero e) x hx, ?_⟩
    obtain ⟨i, hxi⟩ := pmcf_exists_interval (K e) (xs e) (hK e) x
      (by rw [hlast e]; exact hx.2) (by rw [hfirst e]; exact hx.1)
    have hs := hii e i
    dsimp only at hs
    have hab : xs e i.castSucc < xs e i.succ := hxs e (Fin.castSucc_lt_succ (i := i))
    set a := xs e i.castSucc with ha
    set bb := xs e i.succ with hbb
    have hd0 : 0 ≤ beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax) := div_nonneg hbeta hcX
    have hR0 : 0 ≤ (alpha - 1) * |f e x| := mul_nonneg (by linarith) (abs_nonneg _)
    rw [abs_sub_comm]
    rcases pmcf_side (K e) (xs e) (hxs e) (hzero e) i with hside | hside
    · have hz := pmcf_f2_zero_nonpos (f e) (hf3 e) (hshape e)
      have h18 := eq_18 (f e) ⟨(hf e).2.1, (hf3 e).1⟩ (K e) (xs e) (hxs e) i x 0 hxi
        (fun ξ hξ => by rw [hz ξ (hξ.2.trans hside), abs_zero])
      rw [mul_zero] at h18
      linarith
    · set M := max |deriv (deriv (f e)) a| |deriv (deriv (f e)) bb| with hM
      have hcont2 : Continuous (fun ξ => |deriv (deriv (f e)) ξ|) := (hf3 e).2.continuous.abs
      have hbdd : BddAbove ((fun ξ => |deriv (deriv (f e)) ξ|) '' Set.Icc a bb) :=
        (isCompact_Icc.image hcont2).bddAbove
      have hsup := max_f2_eq (f e) (hf e) (hf3 e) (hshape e) (K e) (xs e) (hxs e) i
      have hMb : ∀ ξ ∈ Set.Icc a bb, |deriv (deriv (f e)) ξ| ≤ M := by
        intro ξ hξ
        rw [hM, ← hsup]
        exact le_csSup hbdd ⟨ξ, hξ, rfl⟩
      have h18 := eq_18 (f e) ⟨(hf e).2.1, (hf3 e).1⟩ (K e) (xs e) (hxs e) i x M hxi hMb
      have hQ0 : 0 ≤ (alpha - 1) * |f e a| + beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax) :=
        add_nonneg (mul_nonneg (by linarith) (abs_nonneg _)) hd0
      have hδ : 0 ≤ bb - a := sub_nonneg.2 hab.le
      have hs1 := pmcf_sq_bound _ _ _ hδ (abs_nonneg _) hQ0
        ((mul_le_mul_of_nonneg_left (le_max_left _ _) hδ).trans hs)
      have hs2 := pmcf_sq_bound _ _ _ hδ (abs_nonneg _) hQ0
        ((mul_le_mul_of_nonneg_left (le_max_right _ _) hδ).trans hs)
      have hsq : (bb - a) ^ 2 * M ≤ 8 * ((alpha - 1) * |f e a| +
          beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax)) := by
        rw [hM, mul_max_of_nonneg _ _ (sq_nonneg _)]
        exact max_le hs1 hs2
      have hfa : |f e a| ≤ |f e x| := by
        have h1 := (hf e).1.monotone hxi.1
        have h2 := pmcf_g_nonneg (f e) (hf e) a hside
        rw [abs_of_nonneg (h2.trans h1), abs_of_nonneg h2]
        exact h1
      have := mul_le_mul_of_nonneg_left hfa (by linarith : (0 : ℝ) ≤ alpha - 1)
      nlinarith

end ParamMCF.MCA

open ParamMCF.MCA in
theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (G : Network V E) (hG : G.IsAdmissible) (directed : Bool)
    (f : E → ℝ → ℝ) (hf : ∀ e, IsMarginalCost (f e))
    (hf3 : ∀ e, Differentiable ℝ (deriv (f e)) ∧
      Differentiable ℝ (deriv (deriv (f e))))
    (b0 b : V → ℝ) (hb0 : ∑ v, b0 v = 0) (hb : ∑ v, b v = 0)
    (alpha beta lamMax : ℝ) (halpha : 1 < alpha) (hbeta : 0 ≤ beta)
    (hlamMax : 0 < lamMax) (hX : 0 < xmax b0 b lamMax)
    (K : E → ℕ) (xs : (e : E) → Fin (K e + 1) → ℝ)
    (hxs : ∀ e, StrictMono (xs e))
    (hfirst : ∀ e, xs e 0 = -xmax b0 b lamMax)
    (hlast : ∀ e, xs e (Fin.last (K e)) = xmax b0 b lamMax)
    (hzero : ∀ e, ∃ j, xs e j = 0)
    (hstep :
      (∀ e (i : Fin (K e)),
        let xi := xs e i.castSucc
        let xn := xs e i.succ
        let delta := xn - xi
        delta * Real.sqrt
            (sSup ((fun ξ => |deriv (deriv (f e)) ξ|) '' Set.Icc xi (xn + delta))) ≤
          2 * Real.sqrt 2 * Real.sqrt
            ((alpha - 1) / (1 + alpha) * min |f e xi| |f e xn| +
              beta / ((1 + alpha) * (Fintype.card E : ℝ) * xmax b0 b lamMax))) ∨
      ((∀ e,
          MonotoneOn (deriv (deriv (f e))) (Set.Ici 0) ∧
          (∀ x, 0 ≤ x → 0 ≤ deriv (deriv (f e)) x) ∧
          AntitoneOn (deriv (deriv (f e))) (Set.Iio 0) ∧
          (∀ x, x < 0 → deriv (deriv (f e)) x ≤ 0)) ∧
        ∀ e (i : Fin (K e)),
          let xi := xs e i.castSucc
          let xn := xs e i.succ
          let delta := xn - xi
          delta * max (Real.sqrt |deriv (deriv (f e)) xi|)
              (Real.sqrt |deriv (deriv (f e)) xn|) ≤
            2 * Real.sqrt 2 * Real.sqrt
              ((alpha - 1) * |f e xi| +
                beta / ((Fintype.card E : ℝ) * xmax b0 b lamMax))))
    (xt : ℝ → E → ℝ)
    (hxt : ∀ lam ∈ Set.Icc 0 lamMax,
      IsMinCostFlow G directed (fun e => linSpline (K e) (xs e) (f e))
        (demand b0 b lam) (xt lam)) :
    IsApproxMinCostFlowFun G directed f b0 b lamMax alpha beta xt  :=
  theorem_5_red G hG directed f hf hf3 b0 b hb0 hb alpha beta lamMax halpha hbeta hlamMax hX
    K xs hxs hfirst hlast hzero hstep xt hxt
