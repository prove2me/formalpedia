-- Prove2me | solution 1 for StochGradTrack.Dimin.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-27T12:47:19.978884+00:00
-- url     : https://prove2.me/submissions/ad92f1db-513a-424e-a861-d46dd9bd9c2c

import Mathlib
import Definitions.Def_StochGradTrack_Dimin_Model
import Definitions.Def_StochGradTrack_Dimin_StepSystem

set_option autoImplicit false

namespace SGTRho

open Finset Matrix

/-- Variance decomposition for a doubly stochastic `W`:
`|(W - J)x|^2 + Σ_i Σ_j W_ij (x_j - (Wx)_i)^2 + (Σx)^2/n = |x|^2`. -/
lemma key_identity {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hn : 0 < n)
    (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1) (x a : Fin n → ℝ)
    (ha : ∀ i, a i = ∑ j, W i j * x j) :
    ∑ i, (a i - (n : ℝ)⁻¹ * ∑ j, x j) ^ 2 + ∑ i, ∑ j, W i j * (x j - a i) ^ 2
      + (n : ℝ)⁻¹ * (∑ j, x j) ^ 2 = ∑ j, x j ^ 2 := by
  have hsa : ∑ i, a i = ∑ j, x j := by
    simp only [ha]; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_mul, hcol, one_mul]
  have h1 : ∑ i, ∑ j, W i j * (x j - a i) ^ 2 = ∑ j, x j ^ 2 - ∑ i, a i ^ 2 := by
    have hi : ∀ i, ∑ j, W i j * (x j - a i) ^ 2 = ∑ j, W i j * x j ^ 2 - a i ^ 2 := by
      intro i
      have e : ∀ j, W i j * (x j - a i) ^ 2
          = W i j * x j ^ 2 - 2 * a i * (W i j * x j) + a i ^ 2 * W i j := fun j => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hrow i,
        ← ha i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hi i), Finset.sum_sub_distrib, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl; intro j _; rw [← Finset.sum_mul, hcol, one_mul]
  have h2 : ∑ i, (a i - (n : ℝ)⁻¹ * ∑ j, x j) ^ 2
      = ∑ i, a i ^ 2 - (n : ℝ)⁻¹ * (∑ j, x j) ^ 2 := by
    have e : ∀ i, (a i - (n : ℝ)⁻¹ * ∑ j, x j) ^ 2
        = a i ^ 2 - 2 * ((n : ℝ)⁻¹ * ∑ j, x j) * a i + ((n : ℝ)⁻¹ * ∑ j, x j) ^ 2 :=
      fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsa,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    ring
  linarith

/-- Constancy along the support graph from the equality case. -/
lemma const_of_eq {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (x a : Fin n → ℝ)
    (hx : ∀ i j, 0 < W i j → x j = a i) (i0 : Fin n) (hi0 : 0 < W i0 i0)
    (hsymm : ∀ i j, 0 < W i j → 0 < W j i)
    (hconn : (SimpleGraph.fromRel (fun i j : Fin n => 0 < W i j)).Connected) :
    ∀ j, x j = x i0 := by
  let P : Fin n → Prop := fun j => x j = x i0 ∧ ∀ k, 0 < W j k → x k = x i0
  have base : P i0 := ⟨rfl, fun k hk => by rw [hx i0 k hk, hx i0 i0 hi0]⟩
  have step : ∀ u v, (SimpleGraph.fromRel (fun i j : Fin n => 0 < W i j)).Adj u v → P u → P v := by
    intro u v huv hu
    rw [SimpleGraph.fromRel_adj] at huv
    have hw : 0 < W u v := by
      rcases huv.2 with h | h
      · exact h
      · exact hsymm _ _ h
    have hv : x v = x i0 := hu.2 v hw
    refine ⟨hv, fun l hl => ?_⟩
    have hvu : 0 < W v u := hsymm _ _ hw
    rw [hx v l hl, ← hx v u hvu, hu.1]
  have reach : ∀ (u v : Fin n),
      (SimpleGraph.fromRel (fun i j : Fin n => 0 < W i j)).Walk u v → P u → P v := by
    intro u v p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hu => ih (step _ _ h hu)
  intro j
  obtain ⟨p⟩ := hconn.preconnected i0 j
  exact (reach _ _ p base).1

/-- Strict contraction on nonzero vectors. -/
lemma strict {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hA : StochGradTrack.Dimin.Assumption34 W)
    (hn : 0 < n) (x : Fin n → ℝ) (hx0 : x ≠ 0) :
    ∑ i, ((W - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x) i ^ 2 < ∑ j, x j ^ 2 := by
  set a : Fin n → ℝ := fun i => ∑ j, W i j * x j with ha_def
  have hrow := hA.row_sum
  have hcol := hA.col_sum
  have hmv : ∀ i, ((W - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ x) i
      = a i - (n : ℝ)⁻¹ * ∑ j, x j := by
    intro i
    simp [Matrix.mulVec, dotProduct, ha_def, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
  simp only [hmv]
  have hid := key_identity W hn hrow hcol x a (fun i => rfl)
  have hD : 0 ≤ ∑ i, ∑ j, W i j * (x j - a i) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hA.nonneg i j) (sq_nonneg _)
  have hS : 0 ≤ (n : ℝ)⁻¹ * (∑ j, x j) ^ 2 := by positivity
  by_contra hcon
  push Not at hcon
  have hD0 : ∑ i, ∑ j, W i j * (x j - a i) ^ 2 = 0 := by linarith
  have hS0 : (n : ℝ)⁻¹ * (∑ j, x j) ^ 2 = 0 := by linarith
  have hsum : ∑ j, x j = 0 := by
    have hn' : (n : ℝ)⁻¹ ≠ 0 := by positivity
    rcases mul_eq_zero.mp hS0 with h | h
    · exact absurd h hn'
    · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  have hx : ∀ i j, 0 < W i j → x j = a i := by
    intro i j hij
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hA.nonneg i j) (sq_nonneg _))).mp hD0 i (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (hA.nonneg i j) (sq_nonneg (x j - a i)))).mp h1 j (Finset.mem_univ _)
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · have := pow_eq_zero_iff (two_ne_zero) |>.mp h; linarith
  obtain ⟨i0, hi0⟩ := hA.diag_pos
  have hc := const_of_eq W x a hx i0 hi0 hA.symm_support hA.connected
  have hxi0 : x i0 = 0 := by
    have : ∑ j, x j = n * x i0 := by
      simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hsum] at this
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hn'
    · exact h
  exact hx0 (funext fun j => by rw [hc j, hxi0]; rfl)

end SGTRho

open StochGradTrack.Dimin Matrix in
/-- `ρ_w < 1` under Assumptions 3–4. -/
theorem rhoW_lt_one {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (hA : Assumption34 W) :
    rhoW W < 1 := by
  have hne : Nonempty (Fin n) := hA.connected.nonempty
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hne
  obtain ⟨i0⟩ := hne
  set T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (W - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))) with hT
  have hlt : ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → ‖T v‖ < ‖v‖ := by
    intro v hv
    have hv' : (WithLp.ofLp v) ≠ 0 := by
      intro h; apply hv; exact (WithLp.ofLp_eq_zero 2).mp h
    have h := SGTRho.strict W hA hn (WithLp.ofLp v) hv'
    have e1 : ‖T v‖ ^ 2 = ∑ i, ((W - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ)))
        *ᵥ WithLp.ofLp v) i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; try rfl
    have e2 : ‖v‖ ^ 2 = ∑ j, (WithLp.ofLp v) j ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]; try rfl
    have : ‖T v‖ ^ 2 < ‖v‖ ^ 2 := by rw [e1, e2]; exact h
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) this
  have hcomp : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) := isCompact_sphere _ _
  have hnes : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    ⟨EuclideanSpace.single i0 1, by simp⟩
  obtain ⟨v0, hv0, hmax⟩ := hcomp.exists_isMaxOn hnes
    (f := fun v => ‖T v‖) (continuous_norm.comp T.continuous).continuousOn
  have hv0n : ‖v0‖ = 1 := by simpa using hv0
  have hv00 : v0 ≠ 0 := by intro h; rw [h, norm_zero] at hv0n; exact zero_ne_one hv0n
  have hM : ‖T v0‖ < 1 := by have := hlt v0 hv00; rwa [hv0n] at this
  have hle : ‖T‖ ≤ ‖T v0‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun v => ?_)
    by_cases hv : v = 0
    · simp [hv]
    · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      set u := ‖v‖⁻¹ • v with hu
      have hu1 : u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simp [hu, norm_smul, hvpos.ne']
      have h1 : ‖T u‖ ≤ ‖T v0‖ := hmax hu1
      have h2 : ‖T u‖ = ‖v‖⁻¹ * ‖T v‖ := by
        rw [hu, map_smul, norm_smul, norm_inv, norm_norm]
      rw [h2] at h1
      have := (inv_mul_le_iff₀ hvpos).mp h1
      linarith [mul_comm ‖T v0‖ ‖v‖]
  unfold rhoW
  exact lt_of_le_of_lt hle hM


set_option autoImplicit false
set_option warn.classDefReducibility false
set_option linter.unusedSectionVars false

namespace SGTMeas

open MeasureTheory in
lemma pi_meas {Ω : Type*} {m : MeasurableSpace Ω} {ι : Type*} [Fintype ι] {β : Type*}
    [MeasurableSpace β] (f : Ω → ι → β) (h : ∀ i, Measurable[m] (fun ω => f ω i)) :
    Measurable[m] f := by
  letI := m; exact measurable_pi_lambda _ h

open MeasureTheory ProbabilityTheory StochGradTrack.Dimin

variable {n p d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- `F_k = σ(ξ_{j,i} : j < k)`. -/
noncomputable def Fk (ξ : ℕ → Fin n → Ω → E d) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ q ∈ {q : ℕ × Fin n | q.1 < k}, MeasurableSpace.comap (ξ q.1 q.2) inferInstance

/-- `G_k = σ(ξ_{k,i} : i)`. -/
noncomputable def Gk (ξ : ℕ → Fin n → Ω → E d) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ q ∈ {q : ℕ × Fin n | q.1 = k}, MeasurableSpace.comap (ξ q.1 q.2) inferInstance

lemma Fk_mono (ξ : ℕ → Fin n → Ω → E d) {k l : ℕ} (h : k ≤ l) : Fk ξ k ≤ Fk ξ l := by
  unfold Fk
  refine iSup₂_le fun q hq => ?_
  exact le_iSup₂ (f := fun q (_ : q ∈ {q : ℕ × Fin n | q.1 < l}) =>
    MeasurableSpace.comap (ξ q.1 q.2) inferInstance) q (lt_of_lt_of_le hq h)

lemma Fk_le (ξ : ℕ → Fin n → Ω → E d) (hξ : ∀ k i, Measurable (ξ k i)) (k : ℕ) :
    Fk ξ k ≤ mΩ :=
  iSup₂_le fun q _ => (hξ q.1 q.2).comap_le

lemma xi_meas_F (ξ : ℕ → Fin n → Ω → E d) (k : ℕ) (i : Fin n) :
    Measurable[Fk ξ (k + 1)] (ξ k i) := by
  have h : MeasurableSpace.comap (ξ k i) inferInstance ≤ Fk ξ (k + 1) :=
    le_iSup₂ (f := fun q (_ : q ∈ {q : ℕ × Fin n | q.1 < k + 1}) =>
      MeasurableSpace.comap (ξ q.1 q.2) inferInstance) (k, i) (Nat.lt_succ_self k)
  exact Measurable.mono (comap_measurable (ξ k i)) h le_rfl

lemma Z_meas_G (ξ : ℕ → Fin n → Ω → E d) (k : ℕ) :
    Measurable[Gk ξ k] (fun ω i => ξ k i ω) := by
  refine pi_meas _ fun i => ?_
  have h : MeasurableSpace.comap (ξ k i) inferInstance ≤ Gk ξ k :=
    le_iSup₂ (f := fun q (_ : q ∈ {q : ℕ × Fin n | q.1 = k}) =>
      MeasurableSpace.comap (ξ q.1 q.2) inferInstance) (k, i) rfl
  exact Measurable.mono (comap_measurable (ξ k i)) h le_rfl

lemma indep_FG (P : Measure Ω) (ξ : ℕ → Fin n → Ω → E d) (hξ : ∀ k i, Measurable (ξ k i))
    (hind : iIndepFun (fun q : ℕ × Fin n => ξ q.1 q.2) P) (k : ℕ) :
    Indep (Fk ξ k) (Gk ξ k) P := by
  have hind' : iIndep (fun q : ℕ × Fin n => MeasurableSpace.comap (ξ q.1 q.2) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ P).mp hind
  have hd : Disjoint {q : ℕ × Fin n | q.1 < k} {q : ℕ × Fin n | q.1 = k} :=
    Set.disjoint_left.mpr fun q h1 h2 => by
      have h1' : q.1 < k := h1
      have h2' : q.1 = k := h2
      omega
  exact indep_iSup_of_disjoint (m := fun q : ℕ × Fin n =>
    MeasurableSpace.comap (ξ q.1 q.2) inferInstance) (fun q => (hξ q.1 q.2).comap_le) hind' hd

/-- Anything `F_k`-measurable is independent of the time-`k` noise vector. -/
lemma indepFun_of_meas (P : Measure Ω) (ξ : ℕ → Fin n → Ω → E d) (hξ : ∀ k i, Measurable (ξ k i))
    (hind : iIndepFun (fun q : ℕ × Fin n => ξ q.1 q.2) P) (k : ℕ) {S : Type*}
    [MeasurableSpace S] (X : Ω → S) (hX : Measurable[Fk ξ k] X) :
    IndepFun X (fun ω i => ξ k i ω) P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left
    (indep_of_indep_of_le_right (indep_FG P ξ hξ hind k) (Z_meas_G ξ k).comap_le) hX.comap_le

lemma mix_meas {m : MeasurableSpace Ω} (W : Matrix (Fin n) (Fin n) ℝ) (x : Ω → Fin n → E p)
    (hx : Measurable[m] x) : Measurable[m] (fun ω => mix W (x ω)) := by
  refine pi_meas _ fun i => ?_
  unfold mix
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_const_smul (W i j)).comp
      (show Measurable[m] (fun ω => x ω j) from (measurable_pi_apply j).comp hx)

lemma xs_succ (α : ℕ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → E p → E d → E p)
    (ξ : ℕ → Fin n → Ω → E d) (x0 : Fin n → E p) (k : ℕ) (ω : Ω) :
    xs α W g ξ x0 (k + 1) ω = mix W (fun i => xs α W g ξ x0 k ω i - α k • ys α W g ξ x0 k ω i) :=
  rfl

lemma ys_succ (α : ℕ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → E p → E d → E p)
    (ξ : ℕ → Fin n → Ω → E d) (x0 : Fin n → E p) (k : ℕ) (ω : Ω) :
    ys α W g ξ x0 (k + 1) ω = fun i => mix W (ys α W g ξ x0 k ω) i +
      (g i (xs α W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω) - g i (xs α W g ξ x0 k ω i) (ξ k i ω)) :=
  rfl

lemma ys_zero (α : ℕ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → E p → E d → E p)
    (ξ : ℕ → Fin n → Ω → E d) (x0 : Fin n → E p) (ω : Ω) :
    ys α W g ξ x0 0 ω = fun i => g i (x0 i) (ξ 0 i ω) := rfl

lemma xs_zero (α : ℕ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → E p → E d → E p)
    (ξ : ℕ → Fin n → Ω → E d) (x0 : Fin n → E p) (ω : Ω) :
    xs α W g ξ x0 0 ω = x0 := rfl

/-- `G(x, ξ_k)` as a stacked map is `F_{k+1}`-measurable when `x` is. -/
lemma gstack_meas (g : Fin n → E p → E d → E p) (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (ξ : ℕ → Fin n → Ω → E d) (k : ℕ) (x : Ω → Fin n → E p)
    (hx : Measurable[Fk ξ (k + 1)] x) :
    Measurable[Fk ξ (k + 1)] (fun ω i => g i (x ω i) (ξ k i ω)) := by
  refine pi_meas _ fun i => ?_
  exact (hg i).comp (((measurable_pi_apply i).comp hx).prodMk (xi_meas_F ξ k i))

/-- Adaptedness: `x_k` is `F_k`-measurable and `y_k` is `F_{k+1}`-measurable. -/
lemma meas_xy (α : ℕ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → E p → E d → E p)
    (hg : ∀ i, Measurable (Function.uncurry (g i)))
    (ξ : ℕ → Fin n → Ω → E d) (x0 : Fin n → E p) (k : ℕ) :
    Measurable[Fk ξ k] (xs α W g ξ x0 k) ∧ Measurable[Fk ξ (k + 1)] (ys α W g ξ x0 k) := by
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · have : xs α W g ξ x0 0 = fun _ => x0 := funext fun ω => xs_zero α W g ξ x0 ω
      rw [this]; exact measurable_const
    · have : ys α W g ξ x0 0 = fun ω i => g i (x0 i) (ξ 0 i ω) :=
        funext fun ω => ys_zero α W g ξ x0 ω
      rw [this]
      exact gstack_meas g hg ξ 0 (fun _ => x0) measurable_const
  | succ k ih =>
    have hx : Measurable[Fk ξ (k + 1)] (xs α W g ξ x0 (k + 1)) := by
      have e : xs α W g ξ x0 (k + 1) = fun ω =>
          mix W (fun i => xs α W g ξ x0 k ω i - α k • ys α W g ξ x0 k ω i) :=
        funext fun ω => xs_succ α W g ξ x0 k ω
      rw [e]
      apply mix_meas
      have h1 : Measurable[Fk ξ (k + 1)] (xs α W g ξ x0 k) := ih.1.mono (Fk_mono ξ (by omega)) le_rfl
      refine pi_meas _ fun i => ?_
      exact ((measurable_pi_apply i).comp h1).sub
        ((measurable_const_smul (α k)).comp (show Measurable[Fk ξ (k + 1)]
          (fun ω => ys α W g ξ x0 k ω i) from (measurable_pi_apply i).comp ih.2))
    refine ⟨hx, ?_⟩
    have e : ys α W g ξ x0 (k + 1) = fun ω i => mix W (ys α W g ξ x0 k ω) i +
        (g i (xs α W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω) - g i (xs α W g ξ x0 k ω i) (ξ k i ω)) :=
      funext fun ω => ys_succ α W g ξ x0 k ω
    rw [e]
    have hy : Measurable[Fk ξ (k + 2)] (ys α W g ξ x0 k) := ih.2.mono (Fk_mono ξ (by omega)) le_rfl
    have hx2 : Measurable[Fk ξ (k + 2)] (xs α W g ξ x0 (k + 1)) := hx.mono (Fk_mono ξ (by omega)) le_rfl
    have hx1 : Measurable[Fk ξ (k + 1)] (xs α W g ξ x0 k) := ih.1.mono (Fk_mono ξ (by omega)) le_rfl
    have hG1 := gstack_meas g hg ξ (k + 1) _ hx2
    have hG0 := (gstack_meas g hg ξ k _ hx1).mono (Fk_mono ξ (show k + 1 ≤ k + 2 by omega)) le_rfl
    refine pi_meas _ fun i => ?_
    exact ((measurable_pi_apply i).comp (mix_meas W _ hy)).add
      (((measurable_pi_apply i).comp hG1).sub ((measurable_pi_apply i).comp hG0))

/-- Freezing lemma (lintegral form). -/
lemma freeze_lintegral (P : Measure Ω) [IsProbabilityMeasure P] {S T : Type*} [MeasurableSpace S]
    [MeasurableSpace T] (X : Ω → S) (Z : Ω → T) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (Φ : S → T → ENNReal) (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ ω, Φ (X ω) (Z ω) ∂P = ∫⁻ ω, (∫⁻ ω', Φ (X ω) (Z ω') ∂P) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).mp hXZ
  have e1 : ∫⁻ ω, Φ (X ω) (Z ω) ∂P = ∫⁻ q, Function.uncurry Φ q ∂(P.map fun ω => (X ω, Z ω)) := by
    rw [lintegral_map hΦ (hX.prodMk hZ)]; rfl
  rw [e1, hmap, lintegral_prod _ hΦ.aemeasurable, lintegral_map _ hX]
  · congr 1; ext ω
    rw [lintegral_map _ hZ]
    · rfl
    · exact hΦ.comp (measurable_const.prodMk measurable_id)
  · exact hΦ.lintegral_prod_right'

/-- Freezing lemma (Bochner form). -/
lemma freeze_integral (P : Measure Ω) [IsProbabilityMeasure P] {S T : Type*} [MeasurableSpace S]
    [MeasurableSpace T] (X : Ω → S) (Z : Ω → T) (hX : Measurable X) (hZ : Measurable Z)
    (hXZ : IndepFun X Z P) (Φ : S → T → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (hint : Integrable (fun ω => Φ (X ω) (Z ω)) P) :
    ∫ ω, Φ (X ω) (Z ω) ∂P = ∫ ω, (∫ ω', Φ (X ω) (Z ω') ∂P) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hZ.aemeasurable).mp hXZ
  have hint' : Integrable (Function.uncurry Φ) ((P.map X).prod (P.map Z)) := by
    rw [← hmap, integrable_map_measure hΦ.aestronglyMeasurable (hX.prodMk hZ).aemeasurable]
    exact hint
  have e1 : ∫ ω, Φ (X ω) (Z ω) ∂P = ∫ q, Function.uncurry Φ q ∂(P.map fun ω => (X ω, Z ω)) := by
    rw [integral_map (hX.prodMk hZ).aemeasurable hΦ.aestronglyMeasurable]; rfl
  rw [e1, hmap, integral_prod _ hint', integral_map hX.aemeasurable]
  · congr 1; ext ω
    rw [integral_map hZ.aemeasurable]
    · rfl
    · exact (hΦ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · exact hint'.integral_prod_left.aestronglyMeasurable

end SGTMeas

namespace SGTMeas

open MeasureTheory ProbabilityTheory StochGradTrack.Dimin

variable {n p d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma gradf_cont {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (i : Fin n) : Continuous (gradf i) := by
  have hL : ∀ x y, dist (gradf i x) (gradf i y) ≤ (Real.toNNReal L) * dist x y := fun x y => by
    rw [dist_eq_norm, dist_eq_norm]
    exact (hA2.lipschitz i x y).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal L) (norm_nonneg _))
  exact (LipschitzWith.of_dist_le_mul hL).continuous

lemma noise_lint (P : Measure Ω) [IsProbabilityMeasure P] {gradf : Fin n → E p → E p}
    {g : Fin n → E p → E d → E p} {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hgc : ∀ i, Measurable (gradf i)) (k : ℕ)
    (X : Ω → Fin n → E p) (hX : Measurable[Fk ξ k] X) (i : Fin n) :
    ∫⁻ ω, ENNReal.ofReal (‖g i (X ω i) (ξ k i ω) - gradf i (X ω i)‖ ^ 2) ∂P
      ≤ ENNReal.ofReal (σ ^ 2) := by
  have hXm : Measurable X := hX.mono (Fk_le ξ hA1.meas_xi k) le_rfl
  have hZ : Measurable (fun ω i => ξ k i ω) := measurable_pi_lambda _ fun i => hA1.meas_xi k i
  have hind := indepFun_of_meas P ξ hA1.meas_xi hA1.indep k X hX
  let Φ : (Fin n → E p) → (Fin n → E d) → ENNReal :=
    fun x z => ENNReal.ofReal (‖g i (x i) (z i) - gradf i (x i)‖ ^ 2)
  have hΦ : Measurable (Function.uncurry Φ) := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.pow_const
    apply Measurable.norm
    apply Measurable.sub
    · have hpair : Measurable (fun q : (Fin n → E p) × (Fin n → E d) => (q.1 i, q.2 i)) :=
        ((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd)
      exact (hA1.meas_g i).comp hpair
    · exact (hgc i).comp ((measurable_pi_apply i).comp measurable_fst)
  have h := freeze_lintegral P X (fun ω i => ξ k i ω) hXm hZ hind Φ hΦ
  simp only [Φ] at h
  rw [h]
  calc ∫⁻ ω, ∫⁻ ω', ENNReal.ofReal (‖g i (X ω i) (ξ k i ω') - gradf i (X ω i)‖ ^ 2) ∂P ∂P
      ≤ ∫⁻ _, ENNReal.ofReal (σ ^ 2) ∂P := by
        apply lintegral_mono; intro ω
        dsimp only
        rw [← ofReal_integral_eq_lintegral_ofReal (hA1.variance k i (X ω i)).1
          (Filter.Eventually.of_forall fun _ => by positivity)]
        exact ENNReal.ofReal_le_ofReal (hA1.variance k i (X ω i)).2
    _ = ENNReal.ofReal (σ ^ 2) := by simp

lemma noise_memLp (P : Measure Ω) [IsProbabilityMeasure P] {gradf : Fin n → E p → E p}
    {g : Fin n → E p → E d → E p} {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hgc : ∀ i, Measurable (gradf i)) (k : ℕ)
    (X : Ω → Fin n → E p) (hX : Measurable[Fk ξ k] X) (i : Fin n) :
    MemLp (fun ω => g i (X ω i) (ξ k i ω) - gradf i (X ω i)) 2 P := by
  have hXm : Measurable X := hX.mono (Fk_le ξ hA1.meas_xi k) le_rfl
  have hm : Measurable (fun ω => g i (X ω i) (ξ k i ω) - gradf i (X ω i)) :=
    ((hA1.meas_g i).comp (((measurable_pi_apply i).comp hXm).prodMk (hA1.meas_xi k i))).sub
      ((hgc i).comp ((measurable_pi_apply i).comp hXm))
  rw [memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable]
  refine ⟨(hm.norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => by positivity)]
  exact lt_of_le_of_lt (noise_lint P hA1 hgc k X hX i) ENNReal.ofReal_lt_top

lemma gradf_memLp (P : Measure Ω) [IsProbabilityMeasure P] {f : Fin n → E p → ℝ}
    {gradf : Fin n → E p → E p} {μ L : ℝ} (hA2 : Assumption2 f gradf μ L) (i : Fin n)
    (Y : Ω → E p) (hY : MemLp Y 2 P) (hYm : Measurable Y) :
    MemLp (fun ω => gradf i (Y ω)) 2 P := by
  refine MemLp.of_le ((hY.norm.const_mul L).add (memLp_const ‖gradf i 0‖))
    ((gradf_cont hA2 i).measurable.comp hYm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  have h1 := hA2.lipschitz i (Y ω) 0
  rw [sub_zero] at h1
  have h2 : ‖gradf i (Y ω)‖ ≤ L * ‖Y ω‖ + ‖gradf i 0‖ := by
    have := norm_sub_norm_le (gradf i (Y ω)) (gradf i 0)
    linarith
  simp only [Pi.add_apply, Real.norm_eq_abs]
  exact h2.trans (le_abs_self _)

lemma g_memLp (P : Measure Ω) [IsProbabilityMeasure P] {f : Fin n → E p → ℝ}
    {gradf : Fin n → E p → E p} {μ L : ℝ} {g : Fin n → E p → E d → E p}
    {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L) (k : ℕ)
    (X : Ω → Fin n → E p) (hX : Measurable[Fk ξ k] X) (hXL : ∀ i, MemLp (fun ω => X ω i) 2 P)
    (i : Fin n) : MemLp (fun ω => g i (X ω i) (ξ k i ω)) 2 P := by
  have hgc : ∀ i, Measurable (gradf i) := fun i => (gradf_cont hA2 i).measurable
  have hXm : Measurable X := hX.mono (Fk_le ξ hA1.meas_xi k) le_rfl
  have h1 := noise_memLp P hA1 hgc k X hX i
  have h2 := gradf_memLp P hA2 i (fun ω => X ω i) (hXL i) ((measurable_pi_apply i).comp hXm)
  convert h1.add h2 using 1
  funext ω; simp

/-- C2: all DSGT iterates are square integrable. -/
theorem dsgt_memLp (P : Measure Ω) [IsProbabilityMeasure P] {f : Fin n → E p → ℝ}
    {gradf : Fin n → E p → E p} {μ L : ℝ} {g : Fin n → E p → E d → E p}
    {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L)
    (α : ℕ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (x0 : Fin n → E p) (k : ℕ) :
    (∀ i, MemLp (fun ω => xs α W g ξ x0 k ω i) 2 P) ∧
      (∀ i, MemLp (fun ω => ys α W g ξ x0 k ω i) 2 P) := by
  induction k with
  | zero =>
    refine ⟨fun i => by simpa [xs_zero] using memLp_const (x0 i), fun i => ?_⟩
    have := g_memLp P hA1 hA2 0 (fun _ => x0) measurable_const (fun i => memLp_const (x0 i)) i
    simpa [ys_zero] using this
  | succ k ih =>
    have hx : ∀ i, MemLp (fun ω => xs α W g ξ x0 (k + 1) ω i) 2 P := by
      intro i
      have : (fun ω => xs α W g ξ x0 (k + 1) ω i) = fun ω =>
          ∑ j, W i j • (xs α W g ξ x0 k ω j - α k • ys α W g ξ x0 k ω j) := by
        funext ω; rw [xs_succ]; rfl
      rw [this]
      exact memLp_finsetSum Finset.univ (f := fun j ω =>
        W i j • (xs α W g ξ x0 k ω j - α k • ys α W g ξ x0 k ω j))
        fun j _ => ((ih.1 j).sub ((ih.2 j).const_smul (α k))).const_smul (W i j)
    refine ⟨hx, fun i => ?_⟩
    have : (fun ω => ys α W g ξ x0 (k + 1) ω i) = fun ω =>
        ∑ j, W i j • ys α W g ξ x0 k ω j + (g i (xs α W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω)
          - g i (xs α W g ξ x0 k ω i) (ξ k i ω)) := by
      funext ω; rw [ys_succ]; rfl
    rw [this]
    have hm := meas_xy α W g hA1.meas_g ξ x0
    have hs := memLp_finsetSum Finset.univ (f := fun j ω => W i j • ys α W g ξ x0 k ω j)
      fun j _ => (ih.2 j).const_smul (W i j)
    exact hs.add ((g_memLp P hA1 hA2 (k + 1)
      _ (hm (k + 1)).1 hx i).sub (g_memLp P hA1 hA2 k _ (hm k).1 ih.1 i))

end SGTMeas
set_option autoImplicit false

namespace SGTPath

open Finset Matrix StochGradTrack.Dimin

variable {n p : ℕ}

lemma coord_sum {ι : Type*} (s : Finset ι) (f : ι → E p) (l : Fin p) :
    (∑ j ∈ s, f j) l = ∑ j ∈ s, f j l := by
  change WithLp.ofLp (∑ j ∈ s, f j) l = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]

lemma avg_mix (W : Matrix (Fin n) (Fin n) ℝ) (hcol : ∀ j, ∑ i, W i j = 1) (z : Fin n → E p) :
    avg (mix W z) = avg z := by
  unfold avg mix
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_smul, hcol, one_smul]

lemma sum_sub_avg (hn : 0 < n) (z : Fin n → E p) : ∑ j, (z j - avg z) = 0 := by
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  unfold avg
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (by exact_mod_cast hn.ne')
  rw [this, one_smul, sub_self]

lemma mix_sub_avg (hn : 0 < n) (W : Matrix (Fin n) (Fin n) ℝ) (hrow : ∀ i, ∑ j, W i j = 1)
    (z : Fin n → E p) (i : Fin n) :
    mix W z i - avg z = ∑ j, (W i j - (n : ℝ)⁻¹) • (z j - avg z) := by
  have h1 : ∑ j, (W i j - (n : ℝ)⁻¹) • (z j - avg z)
      = ∑ j, W i j • (z j - avg z) - (n : ℝ)⁻¹ • ∑ j, (z j - avg z) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; rw [sub_smul]
  rw [h1, sum_sub_avg hn, smul_zero, sub_zero]
  unfold mix
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hrow i, one_smul]

/-- One coordinate of the mixing contraction. -/
lemma coord_contract (W : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    ∑ i, ((W - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))) *ᵥ v) i ^ 2
      ≤ rhoW W ^ 2 * ∑ j, v j ^ 2 := by
  set T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
    (W - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ))) with hT
  have h := T.le_opNorm (WithLp.toLp 2 v)
  have e1 : ‖T (WithLp.toLp 2 v)‖ ^ 2 = ∑ i, ((W - (n : ℝ)⁻¹ • Matrix.of (fun _ _ => (1 : ℝ)))
      *ᵥ v) i ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; try rfl
  have e2 : ‖WithLp.toLp 2 v‖ ^ 2 = ∑ j, v j ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]; try rfl
  rw [← e1, ← e2]
  have h0 : 0 ≤ ‖T (WithLp.toLp 2 v)‖ := norm_nonneg _
  have : ‖T (WithLp.toLp 2 v)‖ ^ 2 ≤ (‖T‖ * ‖WithLp.toLp 2 v‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  rw [mul_pow] at this
  exact this

/-- Pathwise mixing contraction `‖(I - J) W z‖² ≤ ρ_w² ‖(I - J) z‖²`. -/
lemma consErr_mix_le (W : Matrix (Fin n) (Fin n) ℝ) (hrow : ∀ i, ∑ j, W i j = 1)
    (hcol : ∀ j, ∑ i, W i j = 1) (z : Fin n → E p) :
    consErr (mix W z) ≤ rhoW W ^ 2 * consErr z := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [consErr]
  unfold consErr
  rw [avg_mix W hcol]
  have hc : ∀ (x : E p), ‖x‖ ^ 2 = ∑ l, x l ^ 2 := fun x => EuclideanSpace.real_norm_sq_eq x
  simp only [hc]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i l => (z i - avg z) l ^ 2), Finset.mul_sum]
  apply Finset.sum_le_sum
  intro l _
  have hv := coord_contract W (fun j => (z j - avg z) l)
  refine le_trans (le_of_eq ?_) hv
  apply Finset.sum_congr rfl; intro i _
  rw [mix_sub_avg hn W hrow z i, coord_sum]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply,
    smul_eq_mul, mul_one]
  apply Finset.sum_congr rfl; intro j _
  rw [PiLp.smul_apply, smul_eq_mul]

lemma young (a b : E p) (η : ℝ) (hη : 0 < η) :
    ‖a - b‖ ^ 2 ≤ (1 + η) * ‖a‖ ^ 2 + (1 + 1 / η) * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  have h2 : 2 * ‖a‖ * ‖b‖ ≤ η * ‖a‖ ^ 2 + ‖b‖ ^ 2 / η := by
    rw [← sub_nonneg]
    have e : η * ‖a‖ ^ 2 + ‖b‖ ^ 2 / η - 2 * ‖a‖ * ‖b‖ = (η * ‖a‖ - ‖b‖) ^ 2 / η := by
      field_simp; ring
    rw [e]; positivity
  have e2 : (1 + 1 / η) * ‖b‖ ^ 2 = ‖b‖ ^ 2 + ‖b‖ ^ 2 / η := by ring
  linarith

lemma avg_sub_smul (x y : Fin n → E p) (α : ℝ) :
    avg (fun i => x i - α • y i) = avg x - α • avg y := by
  unfold avg
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, smul_sub, smul_comm]

lemma consErr_sub_le (x y : Fin n → E p) (α η : ℝ) (hη : 0 < η) :
    consErr (fun i => x i - α • y i) ≤ (1 + η) * consErr x + (1 + 1 / η) * α ^ 2 * consErr y := by
  unfold consErr
  rw [avg_sub_smul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro i _
  have e : x i - α • y i - (avg x - α • avg y) = (x i - avg x) - α • (y i - avg y) := by
    rw [smul_sub]; abel
  rw [e]
  have h := young (x i - avg x) (α • (y i - avg y)) η hη
  have e2 : ‖α • (y i - avg y)‖ ^ 2 = α ^ 2 * ‖y i - avg y‖ ^ 2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [e2] at h
  linarith

/-- Row V, pathwise: `‖(I-J)x_{k+1}‖² ≤ ρ²(1+η)‖(I-J)x_k‖² + ρ²(1+1/η)α²‖(I-J)y_k‖²`. -/
lemma rowV_path (W : Matrix (Fin n) (Fin n) ℝ) (hrow : ∀ i, ∑ j, W i j = 1)
    (hcol : ∀ j, ∑ i, W i j = 1) (x y : Fin n → E p) (α η : ℝ) (hη : 0 < η) :
    consErr (mix W (fun i => x i - α • y i))
      ≤ rhoW W ^ 2 * (1 + η) * consErr x + rhoW W ^ 2 * (1 + 1 / η) * α ^ 2 * consErr y := by
  have h1 := consErr_mix_le W hrow hcol (fun i => x i - α • y i)
  have h2 := consErr_sub_le x y α η hη
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (rhoW W))
  linarith

/-- Gradient tracking: `ȳ_k = (1/n) Σ_i g_i(x_{i,k}, ξ_{i,k})`. -/
lemma avg_ys {d : ℕ} {Ω : Type*} (α : ℕ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (hcol : ∀ j, ∑ i, W i j = 1) (g : Fin n → E p → E d → E p) (ξ : ℕ → Fin n → Ω → E d)
    (x0 : Fin n → E p) (k : ℕ) (ω : Ω) :
    avg (ys α W g ξ x0 k ω) = avg (fun i => g i (xs α W g ξ x0 k ω i) (ξ k i ω)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : ys α W g ξ x0 (k + 1) ω = fun i => mix W (ys α W g ξ x0 k ω) i +
        (g i (xs α W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω) - g i (xs α W g ξ x0 k ω i) (ξ k i ω)) :=
      rfl
    have hlin : ∀ a b c : Fin n → E p, avg (fun i => a i + (b i - c i)) = avg a + (avg b - avg c) := by
      intro a b c; unfold avg
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, smul_add, smul_sub]
    rw [e, hlin, avg_mix W hcol, ih]
    abel

end SGTPath

namespace SGTExp

open MeasureTheory ProbabilityTheory StochGradTrack.Dimin SGTMeas SGTPath

variable {n p d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma int_sq {P : Measure Ω} {Y : Ω → E p} (h : MemLp Y 2 P) :
    Integrable (fun ω => ‖Y ω‖ ^ 2) P :=
  h.norm.integrable_sq

lemma int_inner {P : Measure Ω} {F G : Ω → E p} (hF : MemLp F 2 P) (hG : MemLp G 2 P) :
    Integrable (fun ω => inner ℝ (F ω) (G ω)) P := by
  refine Integrable.mono' ((int_sq hF).add (int_sq hG))
    (hF.aestronglyMeasurable.inner hG.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (F ω) (G ω)
  have h2 : ‖F ω‖ * ‖G ω‖ ≤ ‖F ω‖ ^ 2 + ‖G ω‖ ^ 2 := by
    linarith [sq_nonneg (‖F ω‖ - ‖G ω‖), sq_nonneg ‖F ω‖, sq_nonneg ‖G ω‖]
  show _ ≤ ‖F ω‖ ^ 2 + ‖G ω‖ ^ 2
  linarith

lemma memLp_avg {P : Measure Ω} {X : Ω → Fin n → E p} (hX : ∀ i, MemLp (fun ω => X ω i) 2 P) :
    MemLp (fun ω => avg (X ω)) 2 P := by
  unfold avg
  exact (memLp_finsetSum Finset.univ (f := fun i ω => X ω i) fun i _ => hX i).const_smul ((n : ℝ)⁻¹)

lemma int_consErr {P : Measure Ω} {X : Ω → Fin n → E p}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 P) : Integrable (fun ω => consErr (X ω)) P := by
  unfold consErr
  exact integrable_finsetSum _ fun i _ => int_sq ((hX i).sub (memLp_avg hX))

lemma int_frobSq {P : Measure Ω} {X : Ω → Fin n → E p}
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 P) : Integrable (fun ω => frobSq (X ω)) P := by
  unfold frobSq
  exact integrable_finsetSum _ fun i _ => int_sq (hX i)

lemma int_U {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → Fin n → E p} (hX : ∀ i, MemLp (fun ω => X ω i) 2 P)
    (c : E p) : Integrable (fun ω => ‖avg (X ω) - c‖ ^ 2) P :=
  int_sq ((memLp_avg hX).sub (memLp_const c))

/-! ### Independence of disjoint blocks of the noise. -/

lemma indep_disj (P : Measure Ω) (ξ : ℕ → Fin n → Ω → E d) (hξ : ∀ k i, Measurable (ξ k i))
    (hind : iIndepFun (fun q : ℕ × Fin n => ξ q.1 q.2) P) (S T : Set (ℕ × Fin n))
    (hST : Disjoint S T) :
    Indep (⨆ q ∈ S, MeasurableSpace.comap (ξ q.1 q.2) inferInstance)
      (⨆ q ∈ T, MeasurableSpace.comap (ξ q.1 q.2) inferInstance) P := by
  have hind' : iIndep (fun q : ℕ × Fin n => MeasurableSpace.comap (ξ q.1 q.2) inferInstance) P :=
    (iIndepFun_iff_iIndep _ _ P).mp hind
  exact indep_iSup_of_disjoint (m := fun q : ℕ × Fin n =>
    MeasurableSpace.comap (ξ q.1 q.2) inferInstance) (fun q => (hξ q.1 q.2).comap_le) hind' hST

lemma comap_le_sup (ξ : ℕ → Fin n → Ω → E d) (S : Set (ℕ × Fin n)) (q : ℕ × Fin n)
    (hq : q ∈ S) :
    MeasurableSpace.comap (ξ q.1 q.2) inferInstance
      ≤ ⨆ q ∈ S, MeasurableSpace.comap (ξ q.1 q.2) inferInstance :=
  le_iSup₂ (f := fun q (_ : q ∈ S) => MeasurableSpace.comap (ξ q.1 q.2) inferInstance) q hq

/-- `(X, ξ_{k,i})` is independent of `ξ_{k,j}` for `X` `F_k`-measurable and `i ≠ j`. -/
lemma indep_pair (P : Measure Ω) (ξ : ℕ → Fin n → Ω → E d) (hξ : ∀ k i, Measurable (ξ k i))
    (hind : iIndepFun (fun q : ℕ × Fin n => ξ q.1 q.2) P) (k : ℕ) {S : Type*}
    [MeasurableSpace S] (X : Ω → S) (hX : Measurable[Fk ξ k] X) (i j : Fin n) (hij : i ≠ j) :
    IndepFun (fun ω => (X ω, ξ k i ω)) (ξ k j) P := by
  rw [IndepFun_iff_Indep]
  let A : Set (ℕ × Fin n) := {q | q.1 < k ∨ q = (k, i)}
  let B : Set (ℕ × Fin n) := {q | q = (k, j)}
  have hAB : Disjoint A B := Set.disjoint_left.mpr fun q h1 h2 => by
    have h2' : q = (k, j) := h2
    rcases h1 with h | h
    · rw [h2'] at h; exact lt_irrefl k h
    · rw [h2'] at h; exact hij (Prod.ext_iff.mp h).2.symm
  have hI := indep_disj P ξ hξ hind A B hAB
  refine indep_of_indep_of_le_left (indep_of_indep_of_le_right hI ?_) ?_
  · exact comap_le_sup ξ B (k, j) rfl
  · have hFA : Fk ξ k ≤ ⨆ q ∈ A, MeasurableSpace.comap (ξ q.1 q.2) inferInstance :=
      iSup₂_le fun q hq => comap_le_sup ξ A q (Or.inl hq)
    have hX' : Measurable[⨆ q ∈ A, MeasurableSpace.comap (ξ q.1 q.2) inferInstance] X :=
      hX.mono hFA le_rfl
    have hξ' : Measurable[⨆ q ∈ A, MeasurableSpace.comap (ξ q.1 q.2) inferInstance] (ξ k i) :=
      Measurable.mono (comap_measurable (ξ k i)) (comap_le_sup ξ A (k, i) (Or.inr rfl)) le_rfl
    exact (hX'.prodMk hξ').comap_le

/-- Zero-mean cross term by freezing. -/
lemma zero_cross (P : Measure Ω) [IsProbabilityMeasure P] {gradf : Fin n → E p → E p}
    {g : Fin n → E p → E d → E p} {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hgc : ∀ i, Measurable (gradf i)) (k : ℕ) (j : Fin n)
    {T : Type*} [MeasurableSpace T] (X : Ω → T) (hX : Measurable X)
    (hind : IndepFun X (ξ k j) P) (A : T → E p) (B : T → E p) (hA : Measurable A)
    (hB : Measurable B)
    (hint : Integrable (fun ω => inner ℝ (A (X ω)) (g j (B (X ω)) (ξ k j ω) - gradf j (B (X ω))))
      P) :
    ∫ ω, inner ℝ (A (X ω)) (g j (B (X ω)) (ξ k j ω) - gradf j (B (X ω))) ∂P = 0 := by
  let Φ : T → E d → ℝ := fun t z => inner ℝ (A t) (g j (B t) z - gradf j (B t))
  have hΦ : Measurable (Function.uncurry Φ) := by
    show Measurable (fun q : T × E d => inner ℝ (A q.1) (g j (B q.1) q.2 - gradf j (B q.1)))
    apply Measurable.inner
    · exact hA.comp measurable_fst
    · exact ((hA1.meas_g j).comp ((hB.comp measurable_fst).prodMk measurable_snd)).sub
        ((hgc j).comp (hB.comp measurable_fst))
  have h := freeze_integral P X (ξ k j) hX (hA1.meas_xi k j) hind Φ hΦ hint
  simp only [Φ] at h
  rw [h]
  have h0 : ∀ ω, ∫ ω', inner ℝ (A (X ω)) (g j (B (X ω)) (ξ k j ω') - gradf j (B (X ω))) ∂P
      = 0 := by
    intro ω
    have hu := hA1.unbiased k j (B (X ω))
    have hi := integral_inner (𝕜 := ℝ) (f := fun ω' => g j (B (X ω)) (ξ k j ω') - gradf j (B (X ω)))
      (hu.1.sub (integrable_const _)) (A (X ω))
    rw [hi, integral_sub hu.1 (integrable_const _), hu.2]
    simp
  simp only [h0, integral_zero]

/-! ### Row V in expectation. -/

theorem rowV_exp (P : Measure Ω) [IsProbabilityMeasure P] {f : Fin n → E p → ℝ}
    {gradf : Fin n → E p → E p} {μ L : ℝ} {g : Fin n → E p → E d → E p}
    {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L)
    (W : Matrix (Fin n) (Fin n) ℝ) (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1)
    (ρ : ℝ) (hρ : ρ = rhoW W) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (α : ℕ → ℝ) (x0 : Fin n → E p) (k : ℕ) :
    ∫ ω, consErr (xs α W g ξ x0 (k + 1) ω) ∂P
      ≤ (1 + ρ ^ 2) / 2 * ∫ ω, consErr (xs α W g ξ x0 k ω) ∂P
        + α k ^ 2 * ((1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2)) * ∫ ω, consErr (ys α W g ξ x0 k ω) ∂P := by
  obtain ⟨hx, hy⟩ := dsgt_memLp P hA1 hA2 α W x0 k
  obtain ⟨hx', -⟩ := dsgt_memLp P hA1 hA2 α W x0 (k + 1)
  have hρ2 : ρ ^ 2 < 1 := pow_lt_one₀ hρ0.le hρ1 (by norm_num)
  have hη : 0 < (1 - ρ ^ 2) / (2 * ρ ^ 2) := by
    apply div_pos (by linarith); positivity
  have e1 : ρ ^ 2 * (1 + (1 - ρ ^ 2) / (2 * ρ ^ 2)) = (1 + ρ ^ 2) / 2 := by
    field_simp; ring
  have e2 : ρ ^ 2 * (1 + 1 / ((1 - ρ ^ 2) / (2 * ρ ^ 2))) = (1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2) := by
    have : (1 - ρ ^ 2) ≠ 0 := by linarith
    field_simp; ring
  calc ∫ ω, consErr (xs α W g ξ x0 (k + 1) ω) ∂P
      ≤ ∫ ω, ((1 + ρ ^ 2) / 2 * consErr (xs α W g ξ x0 k ω)
          + α k ^ 2 * ((1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2)) * consErr (ys α W g ξ x0 k ω)) ∂P := by
        refine integral_mono (int_consErr hx') (((int_consErr hx).const_mul _).add
          ((int_consErr hy).const_mul _)) fun ω => ?_
        have h := rowV_path W hrow hcol (xs α W g ξ x0 k ω) (ys α W g ξ x0 k ω) (α k) _ hη
        rw [← hρ, e1, e2] at h
        rw [xs_succ]
        dsimp only
        linarith
    _ = _ := by
        rw [integral_add, integral_const_mul, integral_const_mul]
        · exact (int_consErr hx).const_mul _
        · exact (int_consErr hy).const_mul _

/-! ### Row U: deterministic part. -/

lemma norm_avg_sq (v : Fin n → E p) : ‖avg v‖ ^ 2 ≤ (n : ℝ)⁻¹ * ∑ i, ‖v i‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [avg]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : ‖((n : ℝ))⁻¹‖ = (n : ℝ)⁻¹ := by simp
  unfold avg
  rw [norm_smul, hn1, mul_pow]
  have h1 : ‖∑ i, v i‖ ^ 2 ≤ (∑ i, ‖v i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
  have h2 : (∑ i, ‖v i‖) ^ 2 ≤ (n : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖v i‖)
    simpa using this
  calc (n : ℝ)⁻¹ ^ 2 * ‖∑ i, v i‖ ^ 2 ≤ (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * ∑ i, ‖v i‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
    _ = _ := by field_simp

lemma gradAvg_sub (gradf : Fin n → E p → E p) (x x' : E p) :
    gradAvg gradf x - gradAvg gradf x' = avg (fun i => gradf i x - gradf i x') := by
  unfold gradAvg avg; rw [← smul_sub, ← Finset.sum_sub_distrib]

lemma gradAvg_strong {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (hn : 0 < n) (x x' : E p) :
    μ * ‖x - x'‖ ^ 2 ≤ inner ℝ (gradAvg gradf x - gradAvg gradf x') (x - x') := by
  rw [gradAvg_sub]; unfold avg
  rw [real_inner_smul_left, sum_inner]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : ∑ _i : Fin n, μ * ‖x - x'‖ ^ 2 ≤ ∑ i, inner ℝ (gradf i x - gradf i x') (x - x') :=
    Finset.sum_le_sum fun i _ => hA2.strong i x x'
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  calc μ * ‖x - x'‖ ^ 2 = (n : ℝ)⁻¹ * ((n : ℝ) * (μ * ‖x - x'‖ ^ 2)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

lemma gradAvg_lip_sq {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (hn : 0 < n) (x x' : E p) :
    ‖gradAvg gradf x - gradAvg gradf x'‖ ^ 2 ≤ L ^ 2 * ‖x - x'‖ ^ 2 := by
  rw [gradAvg_sub]
  refine (norm_avg_sq _).trans ?_
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi : ∀ i, ‖gradf i x - gradf i x'‖ ^ 2 ≤ L ^ 2 * ‖x - x'‖ ^ 2 := fun i => by
    have h := hA2.lipschitz i x x'
    calc ‖gradf i x - gradf i x'‖ ^ 2 ≤ (L * ‖x - x'‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by ring
  calc (n : ℝ)⁻¹ * ∑ i, ‖gradf i x - gradf i x'‖ ^ 2
      ≤ (n : ℝ)⁻¹ * ∑ _i : Fin n, L ^ 2 * ‖x - x'‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) (by positivity)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

lemma contract {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (hn : 0 < n) (x xs : E p) (α : ℝ) (hα : 0 ≤ α) :
    ‖(x - xs) - α • (gradAvg gradf x - gradAvg gradf xs)‖ ^ 2
      ≤ (1 - 2 * α * μ + α ^ 2 * L ^ 2) * ‖x - xs‖ ^ 2 := by
  rw [norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_right]
  have h1 := gradAvg_strong hA2 hn x xs
  have h2 := gradAvg_lip_sq hA2 hn x xs
  rw [real_inner_comm] at h1
  have h3 := mul_le_mul_of_nonneg_left h1 hα
  have h4 := mul_le_mul_of_nonneg_left h2 (sq_nonneg α)
  linarith

lemma hAgg_close {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (x : Fin n → E p) :
    ‖hAgg gradf x - gradAvg gradf (avg x)‖ ^ 2 ≤ L ^ 2 / n * consErr x := by
  have e : hAgg gradf x - gradAvg gradf (avg x) = avg (fun i => gradf i (x i) - gradf i (avg x)) := by
    unfold hAgg gradAvg avg; rw [← smul_sub, ← Finset.sum_sub_distrib]
  rw [e]
  refine (norm_avg_sq _).trans ?_
  unfold consErr
  have hi : ∀ i, ‖gradf i (x i) - gradf i (avg x)‖ ^ 2 ≤ L ^ 2 * ‖x i - avg x‖ ^ 2 := by
    intro i
    have h := hA2.lipschitz i (x i) (avg x)
    calc ‖gradf i (x i) - gradf i (avg x)‖ ^ 2 ≤ (L * ‖x i - avg x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := by ring
  calc (n : ℝ)⁻¹ * ∑ i, ‖gradf i (x i) - gradf i (avg x)‖ ^ 2
      ≤ (n : ℝ)⁻¹ * ∑ i, L ^ 2 * ‖x i - avg x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) (by positivity)
    _ = L ^ 2 / n * ∑ i, ‖x i - avg x‖ ^ 2 := by rw [← Finset.mul_sum]; ring

lemma rowU_det {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (hn : 0 < n) (xstar : E p)
    (hgrad0 : gradAvg gradf xstar = 0) (x : Fin n → E p) (α ε : ℝ) (hα : 0 ≤ α) (hε : 0 < ε) :
    ‖avg x - xstar - α • hAgg gradf x‖ ^ 2
      ≤ (1 + ε) * (1 - 2 * α * μ + α ^ 2 * L ^ 2) * ‖avg x - xstar‖ ^ 2
        + (1 + 1 / ε) * α ^ 2 * (L ^ 2 / n) * consErr x := by
  have e : avg x - xstar - α • hAgg gradf x
      = ((avg x - xstar) - α • (gradAvg gradf (avg x) - gradAvg gradf xstar))
        - α • (hAgg gradf x - gradAvg gradf (avg x)) := by
    rw [hgrad0, sub_zero, smul_sub]; abel
  rw [e]
  have h1 := young ((avg x - xstar) - α • (gradAvg gradf (avg x) - gradAvg gradf xstar))
    (α • (hAgg gradf x - gradAvg gradf (avg x))) ε hε
  have h2 := contract hA2 hn (avg x) xstar α hα
  have h3 := hAgg_close hA2 x
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at h1
  have hε1 : 0 ≤ 1 + ε := by linarith
  have hε2 : 0 ≤ (1 + 1 / ε) * α ^ 2 := by positivity
  have h4 := mul_le_mul_of_nonneg_left h2 hε1
  have h5 := mul_le_mul_of_nonneg_left h3 hε2
  linarith

/-! ### Row U: stochastic part. -/

lemma avg_G_split (gradf : Fin n → E p → E p) (g : Fin n → E p → E d → E p) (x : Fin n → E p)
    (z : Fin n → E d) :
    avg (fun i => g i (x i) (z i)) = hAgg gradf x + avg (fun i => g i (x i) (z i) - gradf i (x i)) := by
  unfold avg hAgg
  rw [← smul_add, ← Finset.sum_add_distrib]
  simp

lemma grad_zero {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (hn : 0 < n) (xstar : E p) (hmin : IsMinimizer f xstar) :
    gradAvg gradf xstar = 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hF : HasFDerivAt (∑ i, f i)
      (∑ i, (InnerProductSpace.toDual ℝ (E p)) (gradf i xstar)) xstar :=
    HasFDerivAt.sum fun i _ => hasGradientAt_iff_hasFDerivAt.mp (hA2.hasGrad i xstar)
  have hmin' : IsLocalMin (∑ i, f i) xstar :=
    Filter.Eventually.of_forall fun x => by
      simp only [Finset.sum_apply]
      exact (div_le_div_iff_of_pos_right hnR).mp (hmin x)
  have h0 := hmin'.hasFDerivAt_eq_zero hF
  rw [← map_sum] at h0
  have h1 : ∑ i, gradf i xstar = 0 :=
    (InnerProductSpace.toDual ℝ (E p)).injective (by rw [h0, map_zero])
  unfold gradAvg; rw [h1, smul_zero]

set_option maxHeartbeats 1000000 in
theorem rowU_gen (P : Measure Ω) [IsProbabilityMeasure P] {f : Fin n → E p → ℝ}
    {gradf : Fin n → E p → E p} {μ L : ℝ} {g : Fin n → E p → E d → E p}
    {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L) (hn : 0 < n)
    (xstar : E p) (hgrad0 : gradAvg gradf xstar = 0) (k : ℕ) (X Y : Ω → Fin n → E p)
    (hXF : Measurable[Fk ξ k] X) (hx : ∀ i, MemLp (fun ω => X ω i) 2 P) (α ε : ℝ)
    (hα : 0 ≤ α) (hε : 0 < ε)
    (hY : ∀ ω, avg (Y ω) = avg (X ω) - α • avg (fun i => g i (X ω i) (ξ k i ω))) :
    ∫ ω, ‖avg (Y ω) - xstar‖ ^ 2 ∂P
      ≤ (1 + ε) * (1 - 2 * α * μ + α ^ 2 * L ^ 2) * ∫ ω, ‖avg (X ω) - xstar‖ ^ 2 ∂P
        + (1 + 1 / ε) * α ^ 2 * (L ^ 2 / n) * ∫ ω, consErr (X ω) ∂P + α ^ 2 * (σ ^ 2 / n) := by
  have hgc : ∀ i, Measurable (gradf i) := fun i => (gradf_cont hA2 i).measurable
  have hXm : Measurable X := hXF.mono (Fk_le ξ hA1.meas_xi k) le_rfl
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : ∀ i, MemLp (fun ω => g i (X ω i) (ξ k i ω) - gradf i (X ω i)) 2 P :=
    fun i => noise_memLp P hA1 hgc k X hXF i
  have hNb : MemLp (fun ω => avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i))) 2 P :=
    memLp_avg (X := fun ω i => g i (X ω i) (ξ k i ω) - gradf i (X ω i)) hN
  have hH : MemLp (fun ω => hAgg gradf (X ω)) 2 P := by
    unfold hAgg
    exact (memLp_finsetSum Finset.univ (f := fun i ω => gradf i (X ω i)) fun i _ =>
      gradf_memLp P hA2 i _ (hx i) ((measurable_pi_apply i).comp hXm)).const_smul ((n : ℝ)⁻¹)
  have ha : MemLp (fun ω => avg (X ω) - xstar - α • hAgg gradf (X ω)) 2 P :=
    ((memLp_avg hx).sub (memLp_const xstar)).sub (hH.const_smul α)
  have hexp : ∀ ω, ‖avg (Y ω) - xstar‖ ^ 2 =
      ‖avg (X ω) - xstar - α • hAgg gradf (X ω)‖ ^ 2
        - 2 * α * inner ℝ (avg (X ω) - xstar - α • hAgg gradf (X ω))
            (avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i)))
        + α ^ 2 * ‖avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i))‖ ^ 2 := by
    intro ω
    rw [hY ω, avg_G_split gradf g (X ω) (fun i => ξ k i ω)]
    have e : avg (X ω) - α • (hAgg gradf (X ω)
          + avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i))) - xstar
        = (avg (X ω) - xstar - α • hAgg gradf (X ω))
          - α • avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i)) := by
      rw [smul_add]; abel
    rw [e, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hAm : Measurable (fun x : Fin n → E p => avg x - xstar - α • hAgg gradf x) := by
    have c1 : Continuous (fun x : Fin n → E p => avg x) := by
      unfold avg
      exact (continuous_finset_sum Finset.univ fun i _ => continuous_apply i).const_smul ((n : ℝ)⁻¹)
    have c2 : Continuous (fun x : Fin n → E p => hAgg gradf x) := by
      unfold hAgg
      exact (continuous_finset_sum Finset.univ fun i _ =>
        (gradf_cont hA2 i).comp (continuous_apply i)).const_smul ((n : ℝ)⁻¹)
    have c : Continuous (fun x : Fin n → E p => avg x - xstar - α • hAgg gradf x) :=
      (c1.sub continuous_const).sub (c2.const_smul α)
    exact c.measurable
  have hcross : ∫ ω, inner ℝ (avg (X ω) - xstar - α • hAgg gradf (X ω))
      (avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i))) ∂P = 0 := by
    have e : ∀ ω, inner ℝ (avg (X ω) - xstar - α • hAgg gradf (X ω))
        (avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i)))
        = (n : ℝ)⁻¹ * ∑ j, inner ℝ (avg (X ω) - xstar - α • hAgg gradf (X ω))
          (g j (X ω j) (ξ k j ω) - gradf j (X ω j)) := by
      intro ω
      conv_lhs => rw [show avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i))
        = (n : ℝ)⁻¹ • ∑ i, (g i (X ω i) (ξ k i ω) - gradf i (X ω i)) from rfl]
      rw [real_inner_smul_right, inner_sum]
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul,
      integral_finset_sum]
    · rw [Finset.sum_eq_zero, mul_zero]
      intro j _
      exact zero_cross P hA1 hgc k j X hXm
        ((indepFun_of_meas P ξ hA1.meas_xi hA1.indep k X hXF).comp measurable_id
          (measurable_pi_apply j))
        (fun x => avg x - xstar - α • hAgg gradf x) (fun x => x j) hAm (measurable_pi_apply j)
        (int_inner ha (hN j))
    · intro j _; exact int_inner ha (hN j)
  have hnoise : ∫ ω, ‖avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i))‖ ^ 2 ∂P
      ≤ σ ^ 2 / n := by
    have e : ∀ ω, ‖avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i))‖ ^ 2
        = (n : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, inner ℝ (g i (X ω i) (ξ k i ω) - gradf i (X ω i))
          (g j (X ω j) (ξ k j ω) - gradf j (X ω j)) := by
      intro ω
      have hn1 : ‖((n : ℝ))⁻¹‖ = (n : ℝ)⁻¹ := by simp
      rw [show avg (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i))
        = (n : ℝ)⁻¹ • ∑ i, (g i (X ω i) (ξ k i ω) - gradf i (X ω i)) from rfl]
      rw [norm_smul, hn1, mul_pow, ← real_inner_self_eq_norm_sq, sum_inner]
      simp_rw [inner_sum]
    have hrow : ∀ i, ∫ ω, ∑ j, inner ℝ (g i (X ω i) (ξ k i ω) - gradf i (X ω i))
        (g j (X ω j) (ξ k j ω) - gradf j (X ω j)) ∂P ≤ σ ^ 2 := by
      intro i
      rw [integral_finset_sum]
      · rw [Finset.sum_eq_single i]
        · simp_rw [real_inner_self_eq_norm_sq]
          rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity)
            (int_sq (hN i)).1]
          exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg σ) (noise_lint P hA1 hgc k X hXF i)
        · intro j _ hji
          have hAi : Measurable (fun t : (Fin n → E p) × E d => g i (t.1 i) t.2 - gradf i (t.1 i)) := by
            apply Measurable.sub
            · have hpair : Measurable (fun t : (Fin n → E p) × E d => (t.1 i, t.2)) :=
                ((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd
              exact (hA1.meas_g i).comp hpair
            · exact (hgc i).comp ((measurable_pi_apply i).comp measurable_fst)
          exact zero_cross P hA1 hgc k j (fun ω => (X ω, ξ k i ω)) (hXm.prodMk (hA1.meas_xi k i))
            (indep_pair P ξ hA1.meas_xi hA1.indep k X hXF i j (Ne.symm hji))
            (fun t : (Fin n → E p) × E d => g i (t.1 i) t.2 - gradf i (t.1 i)) (fun t => t.1 j)
            hAi ((measurable_pi_apply j).comp measurable_fst)
            (int_inner (hN i) (hN j))
        · intro h; exact absurd (Finset.mem_univ i) h
      · intro j _; exact int_inner (hN i) (hN j)
    rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, integral_finset_sum]
    · calc (n : ℝ)⁻¹ ^ 2 * ∑ i, ∫ ω, ∑ j, inner ℝ (g i (X ω i) (ξ k i ω) - gradf i (X ω i))
            (g j (X ω j) (ξ k j ω) - gradf j (X ω j)) ∂P
          ≤ (n : ℝ)⁻¹ ^ 2 * ∑ _i : Fin n, σ ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hrow i) (by positivity)
        _ = σ ^ 2 / n := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    · intro i _
      exact integrable_finsetSum _ fun j _ => int_inner (hN i) (hN j)
  have hdet : ∫ ω, ‖avg (X ω) - xstar - α • hAgg gradf (X ω)‖ ^ 2 ∂P
      ≤ (1 + ε) * (1 - 2 * α * μ + α ^ 2 * L ^ 2) * ∫ ω, ‖avg (X ω) - xstar‖ ^ 2 ∂P
        + (1 + 1 / ε) * α ^ 2 * (L ^ 2 / n) * ∫ ω, consErr (X ω) ∂P := by
    calc ∫ ω, ‖avg (X ω) - xstar - α • hAgg gradf (X ω)‖ ^ 2 ∂P
        ≤ ∫ ω, ((1 + ε) * (1 - 2 * α * μ + α ^ 2 * L ^ 2) * ‖avg (X ω) - xstar‖ ^ 2
          + (1 + 1 / ε) * α ^ 2 * (L ^ 2 / n) * consErr (X ω)) ∂P :=
          integral_mono (int_sq ha) (((int_U hx xstar).const_mul _).add
            ((int_consErr hx).const_mul _))
            fun ω => rowU_det hA2 hn xstar hgrad0 (X ω) α ε hα hε
      _ = _ := by
        rw [integral_add, integral_const_mul, integral_const_mul]
        · exact (int_U hx xstar).const_mul _
        · exact (int_consErr hx).const_mul _
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp), integral_add, integral_sub,
    integral_const_mul, integral_const_mul, hcross]
  · have h5 := mul_le_mul_of_nonneg_left hnoise (sq_nonneg α)
    linarith
  · exact int_sq ha
  · exact (int_inner ha hNb).const_mul _
  · exact (int_sq ha).sub ((int_inner ha hNb).const_mul _)
  · exact (int_sq hNb).const_mul _

lemma avg_x_succ (α : ℕ → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (hcol : ∀ j, ∑ i, W i j = 1)
    (g : Fin n → E p → E d → E p) (ξ : ℕ → Fin n → Ω → E d) (x0 : Fin n → E p) (k : ℕ) (ω : Ω) :
    avg (xs α W g ξ x0 (k + 1) ω) = avg (xs α W g ξ x0 k ω)
      - α k • avg (fun i => g i (xs α W g ξ x0 k ω i) (ξ k i ω)) := by
  rw [xs_succ, avg_mix W hcol, avg_sub_smul, avg_ys α W hcol g ξ x0 k ω]

theorem rowU_exp (P : Measure Ω) [IsProbabilityMeasure P] {f : Fin n → E p → ℝ}
    {gradf : Fin n → E p → E p} {μ L : ℝ} {g : Fin n → E p → E d → E p}
    {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L) (hn : 0 < n)
    (W : Matrix (Fin n) (Fin n) ℝ) (hcol : ∀ j, ∑ i, W i j = 1)
    (xstar : E p) (hmin : IsMinimizer f xstar) (α : ℕ → ℝ) (x0 : Fin n → E p) (k : ℕ) (ε : ℝ)
    (hα : 0 ≤ α k) (hε : 0 < ε) :
    ∫ ω, ‖avg (xs α W g ξ x0 (k + 1) ω) - xstar‖ ^ 2 ∂P
      ≤ (1 + ε) * (1 - 2 * α k * μ + α k ^ 2 * L ^ 2)
          * ∫ ω, ‖avg (xs α W g ξ x0 k ω) - xstar‖ ^ 2 ∂P
        + (1 + 1 / ε) * α k ^ 2 * (L ^ 2 / n) * ∫ ω, consErr (xs α W g ξ x0 k ω) ∂P
        + α k ^ 2 * (σ ^ 2 / n) :=
  rowU_gen P hA1 hA2 hn xstar (grad_zero hA2 hn xstar hmin) k (xs α W g ξ x0 k)
    (xs α W g ξ x0 (k + 1)) (meas_xy α W g hA1.meas_g ξ x0 k).1
    (dsgt_memLp P hA1 hA2 α W x0 k).1 (α k) ε hα hε (avg_x_succ α W hcol g ξ x0 k)

end SGTExp

namespace SGTRowW

open MeasureTheory ProbabilityTheory StochGradTrack.Dimin SGTMeas SGTPath SGTExp

variable {n p d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma sq_add_le (a b : E p) : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  linarith [sq_nonneg (‖a‖ - ‖b‖)]

lemma sq_sub_le (a b : E p) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  linarith [sq_nonneg (‖a‖ - ‖b‖)]

lemma fS_add (a b : Fin n → E p) :
    frobSq (fun i => a i + b i) ≤ 2 * frobSq a + 2 * frobSq b := by
  unfold frobSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => sq_add_le (a i) (b i)

lemma fS_sub (a b : Fin n → E p) :
    frobSq (fun i => a i - b i) ≤ 2 * frobSq a + 2 * frobSq b := by
  unfold frobSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => sq_sub_le (a i) (b i)

lemma fS_smul (c : ℝ) (a : Fin n → E p) : frobSq (fun i => c • a i) = c ^ 2 * frobSq a := by
  unfold frobSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

lemma n_avg_sq (a : Fin n → E p) : (n : ℝ) * ‖avg a‖ ^ 2 ≤ frobSq a := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [frobSq]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_left (norm_avg_sq a) hnR.le
  rw [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul] at h
  exact h

lemma consErr_le4 (a : Fin n → E p) : consErr a ≤ 4 * frobSq a := by
  have h1 : ∀ i, ‖a i - avg a‖ ^ 2 ≤ 2 * ‖a i‖ ^ 2 + 2 * ‖avg a‖ ^ 2 := fun i => sq_sub_le _ _
  have h3 := n_avg_sq a
  have e : ∑ i, (2 * ‖a i‖ ^ 2 + 2 * ‖avg a‖ ^ 2) = 2 * frobSq a + 2 * ((n : ℝ) * ‖avg a‖ ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    unfold frobSq; ring
  have h4 : consErr a ≤ ∑ i, (2 * ‖a i‖ ^ 2 + 2 * ‖avg a‖ ^ 2) := Finset.sum_le_sum fun i _ => h1 i
  linarith

lemma consErr_add (a b : Fin n → E p) (η : ℝ) (hη : 0 < η) :
    consErr (fun i => a i + b i) ≤ (1 + η) * consErr a + (1 + 1 / η) * consErr b := by
  have e : (fun i => a i + b i) = fun i => a i - (-1 : ℝ) • b i := by
    funext i; rw [neg_one_smul, sub_neg_eq_add]
  rw [e]
  calc _ ≤ _ := consErr_sub_le a b (-1) η hη
    _ = _ := by ring

lemma fS_mix (W : Matrix (Fin n) (Fin n) ℝ) (hnn : ∀ i j, 0 ≤ W i j) (hrow : ∀ i, ∑ j, W i j = 1)
    (z : Fin n → E p) : frobSq (mix W z) ≤ (n : ℝ) ^ 2 * frobSq z := by
  have hi : ∀ i, ‖mix W z i‖ ^ 2 ≤ (n : ℝ) * frobSq z := by
    intro i
    unfold mix
    have h1 : ‖∑ j, W i j • z j‖ ^ 2 ≤ (∑ j, ‖W i j • z j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    have h2 := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => ‖W i j • z j‖)
    simp only [Finset.card_univ, Fintype.card_fin] at h2
    have h3 : ∀ j, ‖W i j • z j‖ ^ 2 ≤ ‖z j‖ ^ 2 := fun j => by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      have hw1 : W i j ≤ 1 := by
        rw [← hrow i]; exact Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ j)
      have hw2 : W i j ^ 2 ≤ 1 := pow_le_one₀ (hnn i j) hw1
      have := mul_le_mul_of_nonneg_right hw2 (sq_nonneg ‖z j‖)
      linarith
    have h4 : ∑ j, ‖W i j • z j‖ ^ 2 ≤ frobSq z := Finset.sum_le_sum fun j _ => h3 j
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
  calc frobSq (mix W z) = ∑ i, ‖mix W z i‖ ^ 2 := rfl
    _ ≤ ∑ _i : Fin n, (n : ℝ) * frobSq z := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

lemma mix_sub_const (W : Matrix (Fin n) (Fin n) ℝ) (hrow : ∀ i, ∑ j, W i j = 1)
    (z : Fin n → E p) (c : E p) : mix W (fun i => z i - c) = fun i => mix W z i - c := by
  funext i; unfold mix
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hrow i, one_smul]

lemma mix_sub_smul (W : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → E p) (α : ℝ) :
    mix W (fun j => x j - α • y j) = fun i => mix W x i - α • mix W y i := by
  funext i; unfold mix
  rw [Finset.smul_sum]
  simp only [smul_sub, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl; intro j _; rw [smul_comm]

lemma fS_step (W : Matrix (Fin n) (Fin n) ℝ) (hnn : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) (x y : Fin n → E p) (α : ℝ) :
    frobSq (fun i => mix W (fun j => x j - α • y j) i - x i)
      ≤ (4 * (n : ℝ) ^ 2 + 4) * consErr x + 2 * α ^ 2 * (n : ℝ) ^ 2 * frobSq y := by
  have e : (fun i => mix W (fun j => x j - α • y j) i - x i)
      = fun i => (mix W (fun j => x j - avg x) i - (x i - avg x)) - α • mix W y i := by
    funext i
    simp only [mix_sub_smul W x y α, mix_sub_const W hrow x (avg x)]
    abel
  rw [e]
  have h1 := fS_sub (fun i => mix W (fun j => x j - avg x) i - (x i - avg x)) (fun i => α • mix W y i)
  have h2 := fS_sub (mix W (fun j => x j - avg x)) (fun j => x j - avg x)
  have h3 := fS_mix W hnn hrow (fun j => x j - avg x)
  have h4 := fS_smul α (mix W y)
  have h5 := fS_mix W hnn hrow y
  have hc : frobSq (fun j => x j - avg x) = consErr x := rfl
  rw [hc] at h2 h3
  have h6 := mul_le_mul_of_nonneg_left h5 (sq_nonneg α)
  beta_reduce at h1 h2
  linarith

lemma fS_lip {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (x' x : Fin n → E p) :
    frobSq (fun i => gradf i (x' i) - gradf i (x i)) ≤ L ^ 2 * frobSq (fun i => x' i - x i) := by
  unfold frobSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  have h := hA2.lipschitz i (x' i) (x i)
  calc ‖gradf i (x' i) - gradf i (x i)‖ ^ 2 ≤ (L * ‖x' i - x i‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by ring

lemma fS_le_cE (y G : Fin n → E p) (hyG : avg y = avg G) :
    frobSq y ≤ 2 * consErr y + 2 * frobSq G := by
  have h1 : ∀ i, ‖y i‖ ^ 2 ≤ 2 * ‖y i - avg y‖ ^ 2 + 2 * ‖avg y‖ ^ 2 := fun i => by
    have := sq_add_le (y i - avg y) (avg y)
    rwa [sub_add_cancel] at this
  have h3 := n_avg_sq G
  rw [← hyG] at h3
  have e : ∑ i, (2 * ‖y i - avg y‖ ^ 2 + 2 * ‖avg y‖ ^ 2)
      = 2 * consErr y + 2 * ((n : ℝ) * ‖avg y‖ ^ 2) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    unfold consErr; ring
  have h4 : frobSq y ≤ ∑ i, (2 * ‖y i - avg y‖ ^ 2 + 2 * ‖avg y‖ ^ 2) :=
    Finset.sum_le_sum fun i _ => h1 i
  linarith

lemma fS_grad {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (x : Fin n → E p) (xstar : E p) :
    frobSq (fun i => gradf i (x i)) ≤ 4 * L ^ 2 * consErr x
      + 4 * L ^ 2 * (n : ℝ) * ‖avg x - xstar‖ ^ 2 + 2 * ∑ i, ‖gradf i xstar‖ ^ 2 := by
  have hi : ∀ i, ‖gradf i (x i)‖ ^ 2 ≤ 4 * L ^ 2 * ‖x i - avg x‖ ^ 2
      + 4 * L ^ 2 * ‖avg x - xstar‖ ^ 2 + 2 * ‖gradf i xstar‖ ^ 2 := by
    intro i
    have h1 := sq_add_le (gradf i (x i) - gradf i xstar) (gradf i xstar)
    rw [sub_add_cancel] at h1
    have h2 : ‖gradf i (x i) - gradf i xstar‖ ^ 2 ≤ L ^ 2 * ‖x i - xstar‖ ^ 2 := by
      calc ‖gradf i (x i) - gradf i xstar‖ ^ 2 ≤ (L * ‖x i - xstar‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (hA2.lipschitz i (x i) xstar) 2
        _ = _ := by ring
    have h3 := sq_add_le (x i - avg x) (avg x - xstar)
    rw [sub_add_sub_cancel] at h3
    have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg L)
    linarith
  calc frobSq (fun i => gradf i (x i)) ≤ ∑ i, (4 * L ^ 2 * ‖x i - avg x‖ ^ 2
      + 4 * L ^ 2 * ‖avg x - xstar‖ ^ 2 + 2 * ‖gradf i xstar‖ ^ 2) := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, ← Finset.mul_sum]
      unfold consErr; ring

lemma rowW_path {f : Fin n → E p → ℝ} {gradf : Fin n → E p → E p} {μ L : ℝ}
    (hA2 : Assumption2 f gradf μ L) (W : Matrix (Fin n) (Fin n) ℝ) (hnn : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1)
    (x y x' G G' : Fin n → E p) (α η : ℝ) (hη : 0 < η) (xstar : E p)
    (hx' : x' = mix W (fun j => x j - α • y j)) (hyG : avg y = avg G) :
    consErr (fun i => mix W y i + (G' i - G i)) ≤
      ((1 + η) * rhoW W ^ 2 + 64 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α ^ 2) * consErr y
      + 512 * (1 + 1 / η) * L ^ 4 * (n : ℝ) ^ 3 * α ^ 2 * ‖avg x - xstar‖ ^ 2
      + (16 * (1 + 1 / η) * L ^ 2 * (4 * (n : ℝ) ^ 2 + 4)
          + 512 * (1 + 1 / η) * L ^ 4 * (n : ℝ) ^ 2 * α ^ 2) * consErr x
      + 8 * (1 + 1 / η) * frobSq (fun i => G' i - gradf i (x' i))
      + (16 * (1 + 1 / η) + 128 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α ^ 2)
          * frobSq (fun i => G i - gradf i (x i))
      + 256 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α ^ 2 * ∑ i, ‖gradf i xstar‖ ^ 2 := by
  have hc : 0 ≤ 1 + 1 / η := by positivity
  have hA : consErr (fun i => mix W y i + (G' i - G i))
      ≤ (1 + η) * (rhoW W ^ 2 * consErr y) + (1 + 1 / η) * (4 * frobSq (fun i => G' i - G i)) := by
    refine (consErr_add (mix W y) (fun i => G' i - G i) η hη).trans ?_
    have h1 := consErr_mix_le W hrow hcol y
    have h2 := consErr_le4 (fun i => G' i - G i)
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + η)
    have h4 := mul_le_mul_of_nonneg_left h2 hc
    linarith
  have hB : frobSq (fun i => G' i - G i) ≤ 2 * frobSq (fun i => G' i - gradf i (x' i))
      + 4 * (L ^ 2 * frobSq (fun i => x' i - x i)) + 4 * frobSq (fun i => G i - gradf i (x i)) := by
    have e : (fun i => G' i - G i) = fun i => (G' i - gradf i (x' i))
        + ((gradf i (x' i) - gradf i (x i)) - (G i - gradf i (x i))) := by
      funext i; abel
    rw [e]
    have h1 := fS_add (fun i => G' i - gradf i (x' i))
      (fun i => (gradf i (x' i) - gradf i (x i)) - (G i - gradf i (x i)))
    have h2 := fS_sub (fun i => gradf i (x' i) - gradf i (x i)) (fun i => G i - gradf i (x i))
    have h3 := fS_lip hA2 x' x
    beta_reduce at h1 h2
    linarith
  have hC : frobSq (fun i => x' i - x i)
      ≤ (4 * (n : ℝ) ^ 2 + 4) * consErr x + 2 * α ^ 2 * (n : ℝ) ^ 2 * frobSq y := by
    subst hx'; exact fS_step W hnn hrow x y α
  have hD := fS_le_cE y G hyG
  have hE : frobSq G ≤ 2 * frobSq (fun i => G i - gradf i (x i)) + 2 * frobSq (fun i => gradf i (x i)) := by
    have h := fS_add (fun i => G i - gradf i (x i)) (fun i => gradf i (x i))
    beta_reduce at h
    simp only [sub_add_cancel] at h
    exact h
  have hF := fS_grad hA2 x xstar
  have hSy : frobSq y ≤ 2 * consErr y + 4 * frobSq (fun i => G i - gradf i (x i))
      + 16 * L ^ 2 * consErr x + 16 * L ^ 2 * (n : ℝ) * ‖avg x - xstar‖ ^ 2
      + 8 * ∑ i, ‖gradf i xstar‖ ^ 2 := by linarith
  have hS2 : frobSq (fun i => x' i - x i) ≤ (4 * (n : ℝ) ^ 2 + 4) * consErr x
      + 2 * α ^ 2 * (n : ℝ) ^ 2 * (2 * consErr y + 4 * frobSq (fun i => G i - gradf i (x i))
      + 16 * L ^ 2 * consErr x + 16 * L ^ 2 * (n : ℝ) * ‖avg x - xstar‖ ^ 2
      + 8 * ∑ i, ‖gradf i xstar‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_left hSy (by positivity : (0 : ℝ) ≤ 2 * α ^ 2 * (n : ℝ) ^ 2)
    linarith
  have hS1 := mul_le_mul_of_nonneg_left hS2 (sq_nonneg L)
  have hfin : frobSq (fun i => G' i - G i) ≤ 2 * frobSq (fun i => G' i - gradf i (x' i))
      + 4 * (L ^ 2 * ((4 * (n : ℝ) ^ 2 + 4) * consErr x
      + 2 * α ^ 2 * (n : ℝ) ^ 2 * (2 * consErr y + 4 * frobSq (fun i => G i - gradf i (x i))
      + 16 * L ^ 2 * consErr x + 16 * L ^ 2 * (n : ℝ) * ‖avg x - xstar‖ ^ 2
      + 8 * ∑ i, ‖gradf i xstar‖ ^ 2))) + 4 * frobSq (fun i => G i - gradf i (x i)) := by
    linarith
  have h7 := mul_le_mul_of_nonneg_left hfin (by positivity : (0 : ℝ) ≤ (1 + 1 / η) * 4)
  linarith

/-- Linearity of the integral for five integrable functions plus a constant. -/
lemma int_lin5 (P : Measure Ω) [IsProbabilityMeasure P] (F1 F2 F3 F4 F5 : Ω → ℝ)
    (h1 : Integrable F1 P) (h2 : Integrable F2 P) (h3 : Integrable F3 P) (h4 : Integrable F4 P)
    (h5 : Integrable F5 P) (a1 a2 a3 a4 a5 a6 : ℝ) :
    ∫ ω, (a1 * F1 ω + a2 * F2 ω + a3 * F3 ω + a4 * F4 ω + a5 * F5 ω + a6) ∂P
      = a1 * ∫ ω, F1 ω ∂P + a2 * ∫ ω, F2 ω ∂P + a3 * ∫ ω, F3 ω ∂P + a4 * ∫ ω, F4 ω ∂P
        + a5 * ∫ ω, F5 ω ∂P + a6 := by
  have i1 := h1.const_mul a1
  have i2 := h2.const_mul a2
  have i3 := h3.const_mul a3
  have i4 := h4.const_mul a4
  have i5 := h5.const_mul a5
  rw [integral_add (f := fun ω => a1 * F1 ω + a2 * F2 ω + a3 * F3 ω + a4 * F4 ω + a5 * F5 ω)
      (g := fun _ => a6) ((((i1.add i2).add i3).add i4).add i5) (integrable_const _),
    integral_add (f := fun ω => a1 * F1 ω + a2 * F2 ω + a3 * F3 ω + a4 * F4 ω)
      (g := fun ω => a5 * F5 ω) (((i1.add i2).add i3).add i4) i5,
    integral_add (f := fun ω => a1 * F1 ω + a2 * F2 ω + a3 * F3 ω)
      (g := fun ω => a4 * F4 ω) ((i1.add i2).add i3) i4,
    integral_add (f := fun ω => a1 * F1 ω + a2 * F2 ω)
      (g := fun ω => a3 * F3 ω) (i1.add i2) i3,
    integral_add (f := fun ω => a1 * F1 ω) (g := fun ω => a2 * F2 ω) i1 i2]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul]

lemma noise_fS (P : Measure Ω) [IsProbabilityMeasure P] {gradf : Fin n → E p → E p}
    {g : Fin n → E p → E d → E p} {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hgc : ∀ i, Measurable (gradf i)) (k : ℕ)
    (X : Ω → Fin n → E p) (hX : Measurable[Fk ξ k] X) :
    ∫ ω, frobSq (fun i => g i (X ω i) (ξ k i ω) - gradf i (X ω i)) ∂P ≤ (n : ℝ) * σ ^ 2 := by
  unfold frobSq
  rw [integral_finset_sum]
  · calc ∑ i, ∫ ω, ‖g i (X ω i) (ξ k i ω) - gradf i (X ω i)‖ ^ 2 ∂P ≤ ∑ _i : Fin n, σ ^ 2 := by
          apply Finset.sum_le_sum; intro i _
          rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => by positivity)
            (int_sq (noise_memLp P hA1 hgc k X hX i)).1]
          exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg σ) (noise_lint P hA1 hgc k X hX i)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · intro i _; exact int_sq (noise_memLp P hA1 hgc k X hX i)

set_option maxHeartbeats 1000000 in
theorem rowW_exp (P : Measure Ω) [IsProbabilityMeasure P] {f : Fin n → E p → ℝ}
    {gradf : Fin n → E p → E p} {μ L : ℝ} {g : Fin n → E p → E d → E p}
    {ξ : ℕ → Fin n → Ω → E d} {σ : ℝ}
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L)
    (W : Matrix (Fin n) (Fin n) ℝ) (hnn : ∀ i j, 0 ≤ W i j)
    (hrow : ∀ i, ∑ j, W i j = 1) (hcol : ∀ j, ∑ i, W i j = 1)
    (α : ℕ → ℝ) (x0 : Fin n → E p) (k : ℕ) (η : ℝ) (hη : 0 < η) (xstar : E p) :
    ∫ ω, consErr (ys α W g ξ x0 (k + 1) ω) ∂P ≤
      ((1 + η) * rhoW W ^ 2 + 64 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α k ^ 2)
          * ∫ ω, consErr (ys α W g ξ x0 k ω) ∂P
      + 512 * (1 + 1 / η) * L ^ 4 * (n : ℝ) ^ 3 * α k ^ 2
          * ∫ ω, ‖avg (xs α W g ξ x0 k ω) - xstar‖ ^ 2 ∂P
      + (16 * (1 + 1 / η) * L ^ 2 * (4 * (n : ℝ) ^ 2 + 4)
          + 512 * (1 + 1 / η) * L ^ 4 * (n : ℝ) ^ 2 * α k ^ 2) * ∫ ω, consErr (xs α W g ξ x0 k ω) ∂P
      + (8 * (1 + 1 / η) + 16 * (1 + 1 / η) + 128 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α k ^ 2)
          * ((n : ℝ) * σ ^ 2)
      + 256 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α k ^ 2 * ∑ i, ‖gradf i xstar‖ ^ 2 := by
  have hgc : ∀ i, Measurable (gradf i) := fun i => (gradf_cont hA2 i).measurable
  have hc : 0 ≤ 1 + 1 / η := by positivity
  obtain ⟨hx, hy⟩ := dsgt_memLp P hA1 hA2 α W x0 k
  obtain ⟨hx1, hy1⟩ := dsgt_memLp P hA1 hA2 α W x0 (k + 1)
  have hm0 := (meas_xy α W g hA1.meas_g ξ x0 k).1
  have hm1 := (meas_xy α W g hA1.meas_g ξ x0 (k + 1)).1
  have hN1 := noise_fS P hA1 hgc (k + 1) _ hm1
  have hN0 := noise_fS P hA1 hgc k _ hm0
  have iN1 : Integrable (fun ω => frobSq (fun i => g i (xs α W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω)
      - gradf i (xs α W g ξ x0 (k + 1) ω i))) P :=
    int_frobSq (X := fun ω i => g i (xs α W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω)
      - gradf i (xs α W g ξ x0 (k + 1) ω i)) fun i => noise_memLp P hA1 hgc (k + 1) _ hm1 i
  have iN0 : Integrable (fun ω => frobSq (fun i => g i (xs α W g ξ x0 k ω i) (ξ k i ω)
      - gradf i (xs α W g ξ x0 k ω i))) P :=
    int_frobSq (X := fun ω i => g i (xs α W g ξ x0 k ω i) (ξ k i ω)
      - gradf i (xs α W g ξ x0 k ω i)) fun i => noise_memLp P hA1 hgc k _ hm0 i
  calc ∫ ω, consErr (ys α W g ξ x0 (k + 1) ω) ∂P
      ≤ ∫ ω, (((1 + η) * rhoW W ^ 2 + 64 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α k ^ 2)
            * consErr (ys α W g ξ x0 k ω)
          + 512 * (1 + 1 / η) * L ^ 4 * (n : ℝ) ^ 3 * α k ^ 2 * ‖avg (xs α W g ξ x0 k ω) - xstar‖ ^ 2
          + (16 * (1 + 1 / η) * L ^ 2 * (4 * (n : ℝ) ^ 2 + 4)
              + 512 * (1 + 1 / η) * L ^ 4 * (n : ℝ) ^ 2 * α k ^ 2) * consErr (xs α W g ξ x0 k ω)
          + 8 * (1 + 1 / η) * frobSq (fun i => g i (xs α W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω)
              - gradf i (xs α W g ξ x0 (k + 1) ω i))
          + (16 * (1 + 1 / η) + 128 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α k ^ 2)
              * frobSq (fun i => g i (xs α W g ξ x0 k ω i) (ξ k i ω) - gradf i (xs α W g ξ x0 k ω i))
          + 256 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α k ^ 2 * ∑ i, ‖gradf i xstar‖ ^ 2) ∂P := by
        refine integral_mono (int_consErr hy1) ?_ fun ω => ?_
        · exact (((((int_consErr hy).const_mul _).add ((int_U hx xstar).const_mul _)).add
            ((int_consErr hx).const_mul _)).add (iN1.const_mul _)).add (iN0.const_mul _) |>.add
            (integrable_const _)
        · rw [ys_succ]
          exact rowW_path hA2 W hnn hrow hcol (xs α W g ξ x0 k ω) (ys α W g ξ x0 k ω)
            (xs α W g ξ x0 (k + 1) ω) (fun i => g i (xs α W g ξ x0 k ω i) (ξ k i ω))
            (fun i => g i (xs α W g ξ x0 (k + 1) ω i) (ξ (k + 1) i ω)) (α k) η hη xstar
            (xs_succ α W g ξ x0 k ω) (avg_ys α W hcol g ξ x0 k ω)
    _ = _ := int_lin5 P _ _ _ _ _ (int_consErr hy) (int_U hx xstar) (int_consErr hx) iN1 iN0 _ _ _ _ _ _
    _ ≤ _ := by
        have h8 := mul_le_mul_of_nonneg_left hN1 (by positivity : (0 : ℝ) ≤ 8 * (1 + 1 / η))
        have h9 := mul_le_mul_of_nonneg_left hN0
          (by positivity : (0 : ℝ) ≤ 16 * (1 + 1 / η) + 128 * (1 + 1 / η) * L ^ 2 * (n : ℝ) ^ 2 * α k ^ 2)
        linarith

end SGTRowW
set_option autoImplicit false

namespace SGTRate

/-- Bernoulli: for `s > 0` and `a ≥ 1`, `1 - a/s ≤ s^a/(s+1)^a`. -/
lemma bern (s a : ℝ) (hs : 0 < s) (ha : 1 ≤ a) : 1 - a / s ≤ s ^ a / (s + 1) ^ a := by
  have h0 : 1 / (s + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h1 : (-1:ℝ) ≤ -(1 / (s + 1)) := by linarith
  have h2 := one_add_mul_self_le_rpow_one_add h1 ha
  have h3 : (1 + -(1 / (s + 1))) = s / (s + 1) := by field_simp; ring
  rw [h3, Real.div_rpow hs.le (by linarith)] at h2
  have h4 : a / (s + 1) ≤ a / s := by
    gcongr <;> linarith
  have h5 : a * -(1 / (s + 1)) = -(a / (s + 1)) := by ring
  linarith

/-- Rate lemma for the optimality gap: `u_{k+1} ≤ (1 - a/s_k) u_k + c/s_k² + d/s_k³` eventually,
`s_k = m + k`, gives `u_k ≤ 2c/((a-1)s_k) + B/s_k^a`. -/
lemma rate_U (m a c d : ℝ) (K : ℕ) (u : ℕ → ℝ) (hm : 0 < m) (ha : 1 < a) (hc : 0 < c)
    (hd : 0 ≤ d)
    (hstep : ∀ k : ℕ, K ≤ k →
      u (k + 1) ≤ (1 - a / (m + k)) * u k + c / (m + k) ^ 2 + d / (m + k) ^ 3)
    (hcoef : ∀ k : ℕ, K ≤ k → 0 ≤ 1 - a / (m + k)) :
    ∃ B : ℝ, ∀ k : ℕ, u k ≤ 2 * c / ((a - 1) * (m + k)) + B / (m + k) ^ a := by
  obtain ⟨K1, hK1⟩ := exists_nat_gt (d / c)
  set N := max K K1 with hN
  set B : ℝ := ∑ j ∈ Finset.range (N + 1), |u j| * (m + j) ^ a with hB
  have hnn : ∀ j : ℕ, 0 ≤ |u j| * (m + j) ^ a := fun j =>
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => hnn j)
  refine ⟨B, ?_⟩
  have hA : ∀ k : ℕ, 0 ≤ 2 * c / ((a - 1) * (m + k)) := fun k => by
    have : 0 < (a - 1) * (m + k) := mul_pos (by linarith) (by positivity)
    positivity
  have base : ∀ k : ℕ, k ≤ N → u k ≤ 2 * c / ((a - 1) * (m + k)) + B / (m + k) ^ a := by
    intro k hk
    have hs : 0 < (m + k : ℝ) ^ a := Real.rpow_pos_of_pos (by positivity) _
    have h1 : |u k| * (m + k) ^ a ≤ B :=
      Finset.single_le_sum (f := fun j : ℕ => |u j| * (m + j) ^ a) (fun j _ => hnn j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have h2 : u k ≤ B / (m + k) ^ a := by
      rw [le_div_iff₀ hs]; nlinarith [le_abs_self (u k)]
    linarith [hA k]
  intro k
  induction k with
  | zero => exact base 0 (Nat.zero_le _)
  | succ k ih =>
    by_cases hk : k + 1 ≤ N
    · exact base _ hk
    · push Not at hk
      have hKk : K ≤ k := by omega
      have hK1k : K1 ≤ k := by omega
      set s : ℝ := m + k with hs_def
      have hs : 0 < s := by positivity
      have hcast : (m + ((k + 1 : ℕ) : ℝ)) = s + 1 := by push_cast; ring
      rw [hcast]
      have hds : d ≤ c * s := by
        have h1 : (K1 : ℝ) ≤ k := by exact_mod_cast hK1k
        have h2 : d / c < s := by linarith
        rw [div_lt_iff₀ hc] at h2; linarith
      have hst := hstep k hKk
      have hco := hcoef k hKk
      have hsa : 0 < s ^ a := Real.rpow_pos_of_pos hs _
      have hs1a : 0 < (s + 1) ^ a := Real.rpow_pos_of_pos (by linarith) _
      -- B part
      have hBpart : (1 - a / s) * (B / s ^ a) ≤ B / (s + 1) ^ a := by
        have hb := bern s a hs ha.le
        have : (1 - a / s) * (B / s ^ a) ≤ s ^ a / (s + 1) ^ a * (B / s ^ a) :=
          mul_le_mul_of_nonneg_right hb (div_nonneg hB0 hsa.le)
        calc (1 - a / s) * (B / s ^ a) ≤ s ^ a / (s + 1) ^ a * (B / s ^ a) := this
          _ = B / (s + 1) ^ a := by field_simp
      -- A part
      have hApart : (1 - a / s) * (2 * c / ((a - 1) * s)) + c / s ^ 2 + d / s ^ 3
          ≤ 2 * c / ((a - 1) * (s + 1)) := by
        have ha1 : 0 < a - 1 := by linarith
        have hid : 2 * c / ((a - 1) * (s + 1))
            - ((1 - a / s) * (2 * c / ((a - 1) * s)) + c / s ^ 2 + d / s ^ 3)
            = (c * (a - 1) * s ^ 2 + c * (a + 1) * s - d * (a - 1) * (s + 1))
              / ((a - 1) * s ^ 3 * (s + 1)) := by
          field_simp
          ring
        have hnum : 0 ≤ c * (a - 1) * s ^ 2 + c * (a + 1) * s - d * (a - 1) * (s + 1) := by
          have e1 : d * (a - 1) * (s + 1) ≤ c * s * (a - 1) * (s + 1) := by
            have : 0 ≤ (a - 1) * (s + 1) := by positivity
            nlinarith
          nlinarith
        have : 0 ≤ 2 * c / ((a - 1) * (s + 1))
            - ((1 - a / s) * (2 * c / ((a - 1) * s)) + c / s ^ 2 + d / s ^ 3) := by
          rw [hid]; positivity
        linarith
      have hmul : (1 - a / s) * u k ≤ (1 - a / s) * (2 * c / ((a - 1) * s) + B / s ^ a) :=
        mul_le_mul_of_nonneg_left ih hco
      nlinarith

/-- Contraction with an `O(1/s²)` forcing gives an `O(1/s²)` sequence. -/
lemma rate_V (m q D : ℝ) (K : ℕ) (v : ℕ → ℝ) (hm : 0 < m) (hq0 : 0 ≤ q) (hq : q < 1)
    (hD : 0 ≤ D)
    (hstep : ∀ k : ℕ, K ≤ k → v (k + 1) ≤ q * v k + D / (m + k) ^ 2) :
    ∃ C : ℝ, ∀ k : ℕ, v k ≤ C / (m + k) ^ 2 := by
  obtain ⟨K1, hK1⟩ := exists_nat_gt (6 / (1 - q) + 1)
  set N := max K K1 with hN
  set C : ℝ := ∑ j ∈ Finset.range (N + 1), |v j| * (m + j) ^ 2 + 8 * D / (1 - q) with hC
  have hnn : ∀ j : ℕ, 0 ≤ |v j| * (m + j) ^ 2 := fun j => by positivity
  have h1q : 0 < 1 - q := by linarith
  have hC8 : 8 * D / (1 - q) ≤ C := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.range (N + 1)) => hnn j)
    linarith
  refine ⟨C, ?_⟩
  have base : ∀ k : ℕ, k ≤ N → v k ≤ C / (m + k) ^ 2 := by
    intro k hk
    have hs : 0 < (m + k : ℝ) ^ 2 := by positivity
    have h1 : |v k| * (m + k) ^ 2 ≤ ∑ j ∈ Finset.range (N + 1), |v j| * (m + j) ^ 2 :=
      Finset.single_le_sum (f := fun j : ℕ => |v j| * (m + j) ^ 2) (fun j _ => hnn j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    have h8 : 0 ≤ 8 * D / (1 - q) := by positivity
    rw [le_div_iff₀ hs]; nlinarith [le_abs_self (v k)]
  intro k
  induction k with
  | zero => exact base 0 (Nat.zero_le _)
  | succ k ih =>
    by_cases hk : k + 1 ≤ N
    · exact base _ hk
    · push Not at hk
      have hKk : K ≤ k := by omega
      have hK1k : K1 ≤ k := by omega
      set s : ℝ := m + k with hs_def
      have hs : 0 < s := by positivity
      have hcast : (m + ((k + 1 : ℕ) : ℝ)) = s + 1 := by push_cast; ring
      rw [hcast]
      have hsbig : 6 / (1 - q) + 1 ≤ s := by
        have h1 : (K1 : ℝ) ≤ k := by exact_mod_cast hK1k
        linarith
      have hs1 : 1 ≤ s := by
        have : 0 ≤ 6 / (1 - q) := by positivity
        linarith
      have h6 : 6 ≤ (1 - q) * s := by
        have h := hsbig
        have : 6 / (1 - q) ≤ s := by linarith
        rw [div_le_iff₀ h1q] at this; linarith
      -- q (s+1)^2 ≤ ((1+q)/2) s^2
      have hqs : q * (s + 1) ^ 2 ≤ (1 + q) / 2 * s ^ 2 := by nlinarith
      have hst := hstep k hKk
      have hC0 : 0 ≤ C := le_trans (by positivity) hC8
      have hDC : 8 * D ≤ (1 - q) * C := by
        rw [div_le_iff₀ h1q] at hC8; linarith
      have hmul : q * v k ≤ q * (C / s ^ 2) := mul_le_mul_of_nonneg_left ih hq0
      have key : q * (C / s ^ 2) + D / s ^ 2 ≤ C / (s + 1) ^ 2 := by
        have hre : q * (C / s ^ 2) + D / s ^ 2 = (q * C + D) / s ^ 2 := by ring
        rw [hre, div_le_div_iff₀ (by positivity) (by positivity)]
        have hs4 : (s + 1) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left hqs hC0, mul_le_mul_of_nonneg_left hs4 hD]
      linarith

/-- The coupled system is eventually bounded in its third coordinate. -/
lemma box (m a q c D1 D2 D3 Q M : ℝ) (K : ℕ) (U V W : ℕ → ℝ) (hm : 0 < m) (ha : 0 < a)
    (hq0 : 0 ≤ q) (hq : q < 1) (hc : 0 ≤ c) (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hD3 : 0 ≤ D3)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M)
    (hU0 : ∀ k, 0 ≤ U k) (hV0 : ∀ k, 0 ≤ V k) (hW0 : ∀ k, 0 ≤ W k)
    (hcoef : ∀ k : ℕ, K ≤ k → 0 ≤ 1 - a / (m + k))
    (hUs : ∀ k : ℕ, K ≤ k →
      U (k + 1) ≤ (1 - a / (m + k)) * U k + D1 / (m + k) * V k + c / (m + k) ^ 2)
    (hVs : ∀ k : ℕ, K ≤ k → V (k + 1) ≤ q * V k + D2 / (m + k) ^ 2 * W k)
    (hWs : ∀ k : ℕ, K ≤ k → W (k + 1) ≤ D3 / (m + k) * U k + Q * V k + q * W k + M) :
    ∃ K' : ℕ, K ≤ K' ∧ ∃ Wb : ℝ, ∀ k : ℕ, K' ≤ k → W k ≤ Wb := by
  have h1q : 0 < 1 - q := by linarith
  set ε : ℝ := (1 - q) / (4 * (Q + 1)) with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨K1, hK1⟩ := exists_nat_gt (1 + D2 / ((1 - q) * ε) + 4 * D3 * D1 * ε / (a * (1 - q)))
  set K' := max K K1 with hK'
  refine ⟨K', le_max_left _ _, ?_⟩
  set s0 : ℝ := m + K' with hs0
  have g1 : 0 ≤ D2 / ((1 - q) * ε) := by positivity
  have g2 : 0 ≤ 4 * D3 * D1 * ε / (a * (1 - q)) := by positivity
  have hs0big : 1 + D2 / ((1 - q) * ε) + 4 * D3 * D1 * ε / (a * (1 - q)) ≤ s0 := by
    have : (K1 : ℝ) ≤ K' := by exact_mod_cast le_max_right K K1
    have : (0 : ℝ) ≤ K' := by positivity
    linarith
  have hs01 : 1 ≤ s0 := by linarith
  have hs0p : 0 < s0 := by linarith
  set R : ℝ := D3 * U K' / s0 + D3 * c / (a * s0) + M with hR
  have hR0 : 0 ≤ R := by
    have h1 := hU0 K'
    exact add_nonneg (add_nonneg (div_nonneg (mul_nonneg hD3 h1) hs0p.le)
      (div_nonneg (mul_nonneg hD3 hc) (by positivity))) hM
  set Z : ℝ := W K' + V K' / ε + 2 * R / (1 - q) with hZ
  have hZ0 : 0 ≤ Z := by
    have := hW0 K'
    have : 0 ≤ V K' / ε := div_nonneg (hV0 K') hε0.le
    have : 0 ≤ 2 * R / (1 - q) := by positivity
    linarith
  have hZR : 2 * R ≤ (1 - q) * Z := by
    have h : 2 * R / (1 - q) ≤ Z := by
      have := hW0 K'
      have : 0 ≤ V K' / ε := div_nonneg (hV0 K') hε0.le
      linarith
    rw [div_le_iff₀ h1q] at h; linarith
  set Ub : ℝ := U K' + (D1 * ε * Z + c) / a with hUb
  have haUb : a * Ub = a * U K' + (D1 * ε * Z + c) := by
    rw [hUb, mul_add, mul_div_cancel₀ _ ha.ne']
  have hUb0 : 0 ≤ Ub := by
    have := hU0 K'
    have : 0 ≤ (D1 * ε * Z + c) / a := by positivity
    linarith
  have f2 : D2 ≤ (1 - q) * ε * s0 := by
    have : D2 / ((1 - q) * ε) ≤ s0 := by linarith
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have f3 : 4 * D3 * D1 * ε ≤ a * (1 - q) * s0 := by
    have : 4 * D3 * D1 * ε / (a * (1 - q)) ≤ s0 := by linarith
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have fQ : Q * ε ≤ (1 - q) / 4 := by
    have : Q * ε = (1 - q) / 4 * (Q / (Q + 1)) := by rw [hε]; field_simp
    rw [this]
    have : Q / (Q + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have : 0 ≤ (1 - q) / 4 := by positivity
    nlinarith
  suffices H : ∀ k : ℕ, K' ≤ k → U k ≤ Ub ∧ V k ≤ ε * Z ∧ W k ≤ Z from
    ⟨Z, fun k hk => (H k hk).2.2⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    refine ⟨?_, ?_, ?_⟩
    · have : 0 ≤ (D1 * ε * Z + c) / a := by positivity
      linarith
    · have h : V K' / ε ≤ Z := by
        have := hW0 K'
        have : 0 ≤ 2 * R / (1 - q) := by positivity
        linarith
      rw [div_le_iff₀ hε0] at h; linarith
    · have : 0 ≤ V K' / ε := div_nonneg (hV0 K') hε0.le
      have : 0 ≤ 2 * R / (1 - q) := by positivity
      linarith
  | succ k hk ih =>
    obtain ⟨iU, iV, iW⟩ := ih
    have hKk : K ≤ k := le_trans (le_max_left _ _) hk
    set s : ℝ := m + k with hs
    have hss0 : s0 ≤ s := by
      have : (K' : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hs1 : 1 ≤ s := le_trans hs01 hss0
    have hsp : 0 < s := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have e1 := hUs k hKk
      have e2 : (1 - a / s) * U k ≤ (1 - a / s) * Ub :=
        mul_le_mul_of_nonneg_left iU (hcoef k hKk)
      have e3 : D1 / s * V k ≤ D1 / s * (ε * Z) := mul_le_mul_of_nonneg_left iV (by positivity)
      have e4 : c / s ^ 2 ≤ c / s := by
        apply div_le_div_of_nonneg_left hc hsp
        calc s = s * 1 := (mul_one s).symm
          _ ≤ s * s := mul_le_mul_of_nonneg_left hs1 hsp.le
          _ = s ^ 2 := (sq s).symm
      have e5 : (1 - a / s) * Ub + D1 / s * (ε * Z) + c / s
          = Ub - (a * Ub - D1 * ε * Z - c) / s := by field_simp; ring
      have e6 : 0 ≤ (a * Ub - D1 * ε * Z - c) / s := by
        apply div_nonneg _ hsp.le
        have : a * Ub - D1 * ε * Z - c = a * U K' := by rw [haUb]; ring
        rw [this]; exact mul_nonneg ha.le (hU0 K')
      linarith
    · have e1 := hVs k hKk
      have e2 : q * V k ≤ q * (ε * Z) := mul_le_mul_of_nonneg_left iV hq0
      have e3 : D2 / s ^ 2 ≤ (1 - q) * ε := by
        rw [div_le_iff₀ (by positivity)]
        have : (1 - q) * ε * s0 ≤ (1 - q) * ε * s ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc s0 ≤ s := hss0
            _ = s * 1 := (mul_one s).symm
            _ ≤ s * s := mul_le_mul_of_nonneg_left hs1 hsp.le
            _ = s ^ 2 := (sq s).symm
        linarith
      have e4 : D2 / s ^ 2 * W k ≤ (1 - q) * ε * Z := by
        calc D2 / s ^ 2 * W k ≤ D2 / s ^ 2 * Z :=
              mul_le_mul_of_nonneg_left iW (by positivity)
          _ ≤ (1 - q) * ε * Z := mul_le_mul_of_nonneg_right e3 hZ0
      linarith
    · have e1 := hWs k hKk
      have e2 : D3 / s * U k ≤ D3 / s0 * Ub := by
        calc D3 / s * U k ≤ D3 / s * Ub := mul_le_mul_of_nonneg_left iU (by positivity)
          _ ≤ D3 / s0 * Ub :=
            mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hD3 hs0p hss0) hUb0
      have e3 : D3 / s0 * Ub = D3 * U K' / s0 + D3 * c / (a * s0)
          + D3 * D1 * ε * Z / (a * s0) := by
        rw [hUb]; field_simp; ring
      have e4 : D3 * D1 * ε * Z / (a * s0) ≤ (1 - q) / 4 * Z := by
        rw [div_le_iff₀ (by positivity)]
        have := mul_le_mul_of_nonneg_right f3 hZ0
        linarith only [this]
      have e5 : Q * V k ≤ (1 - q) / 4 * Z := by
        calc Q * V k ≤ Q * (ε * Z) := mul_le_mul_of_nonneg_left iV hQ
          _ = Q * ε * Z := by ring
          _ ≤ (1 - q) / 4 * Z := mul_le_mul_of_nonneg_right fQ hZ0
      have e6 : q * W k ≤ q * Z := mul_le_mul_of_nonneg_left iW hq0
      linarith only [e1, e2, e3, e4, e5, e6, hZR, hR]

end SGTRate

/-- Generic deterministic rate (C4g): eventual recursions of the shape of (29) with free constants
give (15a)-(15b). -/
theorem C4g_rate {n : ℕ} (hn : 0 < n) (θ m μ σ q D1 D2 D3 Q M : ℝ) (K : ℕ)
    (U V Wt : ℕ → ℝ) (hU : ∀ k, 0 ≤ U k) (hV : ∀ k, 0 ≤ V k) (hW : ∀ k, 0 ≤ Wt k)
    (hμ : 0 < μ) (hσ : 0 < σ) (hθ : 1 / μ < θ) (hma : θ * μ < m)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hD10 : 0 ≤ D1) (hD20 : 0 ≤ D2) (hD30 : 0 ≤ D3)
    (hQ0 : 0 ≤ Q) (hM0 : 0 ≤ M)
    (rowU : ∀ k : ℕ, K ≤ k → U (k + 1) ≤ (1 - θ * μ / (m + k)) * U k + D1 / (m + k) * V k
      + θ ^ 2 * σ ^ 2 / n / (m + k) ^ 2)
    (rowV : ∀ k : ℕ, K ≤ k → V (k + 1) ≤ q * V k + D2 / (m + k) ^ 2 * Wt k)
    (rowW : ∀ k : ℕ, K ≤ k → Wt (k + 1) ≤ D3 / (m + k) * U k + Q * V k + q * Wt k + M) :
    ∃ C₁ C₂ C₃ : ℝ, ∀ k : ℕ,
      U k ≤ 2 * θ ^ 2 * σ ^ 2 / (n * (θ * μ - 1) * (m + k)) + C₁ / (m + k) ^ (θ * μ)
        + C₂ / (m + k) ^ 2 ∧ V k ≤ C₃ / (m + k) ^ 2 := by
  have hθμ : 1 < θ * μ := by rwa [div_lt_iff₀ hμ] at hθ
  have hm0 : 0 < m := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : ∀ k : ℕ, 0 < m + k := fun k => by positivity
  have hsm : ∀ k : ℕ, m ≤ m + k := fun k => by
    have : (0 : ℝ) ≤ k := by positivity
    linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = θ ^ 2 * σ ^ 2 / n := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by have : 0 < 1 / μ := by positivity
                         linarith
  have hc0 : 0 < c := by rw [hc]; exact div_pos (mul_pos (pow_pos hθ0 2) (pow_pos hσ 2)) hnR
  have rowU' : ∀ k : ℕ, K ≤ k →
      U (k + 1) ≤ (1 - θ * μ / (m + k)) * U k + D1 / (m + k) * V k + c / (m + k) ^ 2 := by
    intro k hk; rw [hc]; exact rowU k hk
  have hcoef : ∀ k : ℕ, K ≤ k → 0 ≤ 1 - θ * μ / (m + k) := by
    intro k _
    have : θ * μ / (m + k) ≤ 1 := by
      rw [div_le_one (hs k)]; linarith [hsm k]
    linarith
  obtain ⟨K', hK', Wb, hWb⟩ := SGTRate.box m (θ * μ) q c D1 D2 D3 Q M K U V Wt
    hm0 (by linarith) hq0 hq1 hc0.le hD10 hD20 hD30 hQ0 hM0 hU hV hW hcoef rowU' rowV rowW
  obtain ⟨C₃, hC₃⟩ := SGTRate.rate_V m q (D2 * |Wb|) K' V hm0 hq0 hq1
    (mul_nonneg hD20 (abs_nonneg _)) (by
      intro k hk
      have r := rowV k (le_trans hK' hk)
      have h1 : Wt k ≤ |Wb| := le_trans (hWb k hk) (le_abs_self _)
      have h2 : D2 / (m + k) ^ 2 * Wt k ≤ D2 / (m + k) ^ 2 * |Wb| :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hD20 (by positivity))
      have h3 : D2 / (m + k) ^ 2 * |Wb| = D2 * |Wb| / (m + k) ^ 2 := by ring
      linarith)
  obtain ⟨B, hB⟩ := SGTRate.rate_U m (θ * μ) c (D1 * |C₃|) K U hm0 hθμ hc0
    (mul_nonneg hD10 (abs_nonneg _)) (by
      intro k hk
      have r := rowU' k hk
      have h1 : D1 / (m + k) * V k ≤ D1 / (m + k) * (C₃ / (m + k) ^ 2) :=
        mul_le_mul_of_nonneg_left (hC₃ k) (div_nonneg hD10 (hs k).le)
      have h2 : D1 / (m + k) * (C₃ / (m + k) ^ 2) = D1 * C₃ / (m + k) ^ 3 := by
        have := (hs k).ne'; field_simp
      have h3 : D1 * C₃ / (m + k) ^ 3 ≤ D1 * |C₃| / (m + k) ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self _) hD10)
          (by positivity)
      linarith) hcoef
  refine ⟨B, 0, C₃, fun k => ⟨?_, hC₃ k⟩⟩
  have e : 2 * c / ((θ * μ - 1) * (m + k)) = 2 * θ ^ 2 * σ ^ 2 / (n * (θ * μ - 1) * (m + k)) := by
    rw [hc]; field_simp
  have := hB k
  rw [zero_div, add_zero]
  linarith


set_option maxHeartbeats 1000000 in
open MeasureTheory ProbabilityTheory StochGradTrack.Dimin in
theorem solution
    {n p d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Fin n → E p → ℝ) (gradf : Fin n → E p → E p) (μ L : ℝ)
    (g : Fin n → E p → E d → E p) (ξ : ℕ → Fin n → Ω → E d) (σ : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (xstar : E p) (x0 : Fin n → E p)
    (hA1 : Assumption1 P gradf g ξ σ) (hA2 : Assumption2 f gradf μ L) (hA34 : Assumption34 W)
    (hxstar : IsMinimizer f xstar)
    (ρ : ℝ) (hρdef : ρ = rhoW W) (hρ : 0 < ρ)
    (w : ℝ) (hw : w = frobNorm (W - 1))
    (θ m : ℝ) (hθ : 1 / μ < θ)
    (hm1 : max (θ / 2 * (μ + L))
      ((4 * θ * L * ρ ^ 2 + 2 * θ * L * ρ * Real.sqrt (1 + 3 * ρ ^ 2)) / (1 - ρ ^ 2)) < m)
    (hm2 : (1 - ρ ^ 2) ^ 2 / (θ ^ 2 * (1 + ρ ^ 2) * ρ ^ 2) * ((1 - ρ ^ 2) / 2 - (2 * m + 1) / (m + 1) ^ 2)
      > 1 / (θ * μ - 1) * (1 / μ + θ / m) * (4 * θ ^ 2 * L ^ 5 / m ^ 3) + 2 * Cconst θ m L ρ w / m ^ 2) :
    (∀ k : ℕ, Integrable (fun ω => ‖avg (xs (stepDimin θ m) W g ξ x0 k ω) - xstar‖ ^ 2) P ∧
      Integrable (fun ω => consErr (xs (stepDimin θ m) W g ξ x0 k ω)) P) ∧
    ∃ C₁ C₂ C₃ : ℝ, ∀ k : ℕ,
      ∫ ω, ‖avg (xs (stepDimin θ m) W g ξ x0 k ω) - xstar‖ ^ 2 ∂P
          ≤ 2 * θ ^ 2 * σ ^ 2 / (n * (θ * μ - 1) * (m + k)) + C₁ / (m + k) ^ (θ * μ)
            + C₂ / (m + k) ^ 2 ∧
        ∫ ω, consErr (xs (stepDimin θ m) W g ξ x0 k ω) ∂P ≤ C₃ / (m + k) ^ 2 := by
  have hne : Nonempty (Fin n) := hA34.connected.nonempty
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr hne
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ1 : ρ < 1 := by rw [hρdef]; exact rhoW_lt_one W hA34
  have hρ2 : ρ ^ 2 < 1 := by nlinarith
  have hμ : 0 < μ := hA2.mu_pos
  have hσ : 0 < σ := hA1.sigma_pos
  have hθ0 : 0 < θ := lt_trans (by positivity) hθ
  have hLμ : μ ≤ L := by
    obtain ⟨i⟩ := hne
    obtain ⟨v, hv⟩ : ∃ v : E p, v = EuclideanSpace.single (⟨0, hA2.dim_pos⟩ : Fin p) (1 : ℝ) :=
      ⟨_, rfl⟩
    have hv1 : ‖v‖ = 1 := by rw [hv, EuclideanSpace.norm_single]; simp
    have h1 := hA2.strong i v 0
    have h2 := hA2.lipschitz i v 0
    have h3 := real_inner_le_norm (gradf i v - gradf i 0) (v - 0)
    simp only [sub_zero, hv1, one_pow, mul_one] at h1 h2 h3
    linarith
  have hL0 : 0 < L := lt_of_lt_of_le hμ hLμ
  have hma : θ * μ < m := by
    have h1 := (le_max_left _ _).trans_lt hm1
    have h3 := mul_le_mul_of_nonneg_left hLμ hθ0.le
    have h2 : θ * μ ≤ θ / 2 * (μ + L) := by linarith only [h3]
    linarith only [h1, h2]
  have hm0 : 0 < m := by linarith only [hma, mul_pos hθ0 hμ]
  have hmem := fun k => SGTMeas.dsgt_memLp P hA1 hA2 (stepDimin θ m) W x0 k
  refine ⟨fun k => ⟨SGTExp.int_U (hmem k).1 xstar, SGTExp.int_consErr (hmem k).1⟩, ?_⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (1 - ρ ^ 2) / (2 * ρ ^ 2) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact div_pos (by linarith) (by positivity)
  have hηρ : (1 + η) * ρ ^ 2 = (1 + ρ ^ 2) / 2 := by rw [hηdef]; field_simp; ring
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = 1 + 1 / η := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; positivity
  have hcn : 0 < c * (256 * L ^ 2 * (n : ℝ) ^ 2) := mul_pos hc (by positivity)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (min (μ / (4 * L ^ 2))
      ((1 - ρ ^ 2) / (c * (256 * L ^ 2 * (n : ℝ) ^ 2)))) := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [hδdef]; exact lt_min one_pos (lt_min (by positivity) (div_pos (by linarith) hcn))
  obtain ⟨K, hK⟩ := exists_nat_ge (θ / δ)
  have hs : ∀ k : ℕ, 0 < m + k := fun k => by positivity
  have hsm : ∀ k : ℕ, m ≤ m + k := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hαpos : ∀ k : ℕ, 0 < stepDimin θ m k := fun k => div_pos hθ0 (hs k)
  have hαs : ∀ k : ℕ, stepDimin θ m k * (m + k) = θ := fun k => by
    unfold stepDimin; field_simp
  have hαm : ∀ k : ℕ, stepDimin θ m k ≤ θ / m := fun k =>
    div_le_div_of_nonneg_left hθ0.le hm0 (hsm k)
  have hαδ : ∀ k : ℕ, K ≤ k → stepDimin θ m k ≤ δ := by
    intro k hk
    unfold stepDimin
    rw [div_le_iff₀ (hs k)]
    have h1 : θ ≤ K * δ := (div_le_iff₀ hδ).mp hK
    have h2 : (K : ℝ) ≤ k := by exact_mod_cast hk
    linarith only [h1, mul_le_mul_of_nonneg_right h2 hδ.le, mul_pos hm0 hδ]
  have hUnn : ∀ k : ℕ, 0 ≤ ∫ ω, ‖avg (xs (stepDimin θ m) W g ξ x0 k ω) - xstar‖ ^ 2 ∂P :=
    fun k => integral_nonneg fun ω => by positivity
  have hVnn : ∀ k : ℕ, 0 ≤ ∫ ω, consErr (xs (stepDimin θ m) W g ξ x0 k ω) ∂P :=
    fun k => integral_nonneg fun ω => by unfold consErr; positivity
  have hWnn : ∀ k : ℕ, 0 ≤ ∫ ω, consErr (ys (stepDimin θ m) W g ξ x0 k ω) ∂P :=
    fun k => integral_nonneg fun ω => by unfold consErr; positivity
  have hK0 : 0 ≤ ∑ i, ‖gradf i xstar‖ ^ 2 := by positivity
  refine C4g_rate hn θ m μ σ ((3 + ρ ^ 2) / 4) ((θ ^ 2 / m + 2 * θ / μ) * (L ^ 2 / n))
    (θ ^ 2 * ((1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2)))
    (c * (512 * L ^ 4 * (n : ℝ) ^ 3 * θ ^ 2 / m))
    (c * (16 * L ^ 2 * (4 * (n : ℝ) ^ 2 + 4) + 512 * L ^ 4 * (n : ℝ) ^ 2 * (θ ^ 2 / m ^ 2)))
    (c * ((24 + 128 * L ^ 2 * (n : ℝ) ^ 2 * (θ ^ 2 / m ^ 2)) * ((n : ℝ) * σ ^ 2)
      + 256 * L ^ 2 * (n : ℝ) ^ 2 * (θ ^ 2 / m ^ 2) * ∑ i, ‖gradf i xstar‖ ^ 2)) K
    (fun k => ∫ ω, ‖avg (xs (stepDimin θ m) W g ξ x0 k ω) - xstar‖ ^ 2 ∂P)
    (fun k => ∫ ω, consErr (xs (stepDimin θ m) W g ξ x0 k ω) ∂P)
    (fun k => ∫ ω, consErr (ys (stepDimin θ m) W g ξ x0 k ω) ∂P) hUnn hVnn hWnn hμ hσ hθ hma
    (by positivity) (by linarith) (by positivity)
    (mul_nonneg (sq_nonneg θ) (div_nonneg (by positivity) (by linarith)))
    (mul_nonneg hc.le (by positivity)) (mul_nonneg hc.le (by positivity))
    (mul_nonneg hc.le (add_nonneg (by positivity) (mul_nonneg (by positivity) hK0))) ?_ ?_ ?_
  · -- row U
    intro k hk
    have hε : 0 < stepDimin θ m k * μ / 2 := by have := hαpos k; positivity
    have h := SGTExp.rowU_exp P hA1 hA2 hn W hA34.col_sum xstar hxstar (stepDimin θ m) x0 k
      (stepDimin θ m k * μ / 2) (hαpos k).le hε
    have hc3 : stepDimin θ m k ^ 2 * (σ ^ 2 / n) = θ ^ 2 * σ ^ 2 / n / (m + k) ^ 2 := by
      unfold stepDimin; rw [div_pow]; ring
    have he : θ * μ / (m + k) = stepDimin θ m k * μ := by unfold stepDimin; ring
    have hαδk := hαδ k hk
    have hαsk := hαs k
    have hαmk := hαm k
    have hsk := hs k
    rw [hc3] at h
    rw [he]
    obtain ⟨α, hαdef⟩ : ∃ α, α = stepDimin θ m k := ⟨_, rfl⟩
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = m + k := ⟨_, rfl⟩
    rw [← hαdef] at h hαδk hαsk hαmk ⊢
    rw [← hsdef] at h hαsk hsk ⊢
    have hα0 : 0 < α := by rw [hαdef]; exact hαpos k
    have hαL : α * L ^ 2 ≤ μ / 4 := by
      have h1 : α ≤ μ / (4 * L ^ 2) := by
        rw [hδdef] at hαδk; exact hαδk.trans ((min_le_right _ _).trans (min_le_left _ _))
      rw [le_div_iff₀ (by positivity)] at h1; linarith only [h1]
    have hαμ : α * μ ≤ 1 / 4 := by
      have h1 : α * μ ^ 2 ≤ α * L ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hμ.le hLμ 2) hα0.le
      have h2 : (α * μ) * μ ≤ 1 / 4 * μ := by linarith only [h1, hαL]
      exact le_of_mul_le_mul_right h2 hμ
    have hc1 : (1 + α * μ / 2) * (1 - 2 * α * μ + α ^ 2 * L ^ 2) ≤ 1 - α * μ := by
      have p1 := mul_le_mul_of_nonneg_left hαL hα0.le
      have p2 : (α * L ^ 2) * (α * μ) ≤ (μ / 4) * (1 / 4) :=
        mul_le_mul hαL hαμ (by positivity) (by positivity)
      have p3 := mul_le_mul_of_nonneg_left p2 hα0.le
      linarith only [p1, p3, sq_nonneg (α * μ), mul_pos hα0 hμ]
    have hc2 : (1 + 1 / (α * μ / 2)) * α ^ 2 * (L ^ 2 / n)
        ≤ (θ ^ 2 / m + 2 * θ / μ) * (L ^ 2 / n) / s := by
      rw [le_div_iff₀ hsk]
      have e1 : (1 + 1 / (α * μ / 2)) * α ^ 2 = α ^ 2 + 2 * α / μ := by field_simp
      rw [e1, show (α ^ 2 + 2 * α / μ) * (L ^ 2 / n) * s
        = (α * (α * s) + 2 * (α * s) / μ) * (L ^ 2 / n) by ring, hαsk]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have h1 := mul_le_mul_of_nonneg_right hαmk hθ0.le
      have h2 : θ / m * θ = θ ^ 2 / m := by ring
      linarith only [h1, h2]
    have q1 := mul_le_mul_of_nonneg_right hc1 (hUnn k)
    have q2 := mul_le_mul_of_nonneg_right hc2 (hVnn k)
    linarith only [h, q1, q2]
  · -- row V
    intro k _
    have h := SGTExp.rowV_exp P hA1 hA2 W hA34.row_sum hA34.col_sum ρ hρdef hρ hρ1
      (stepDimin θ m) x0 k
    have e : stepDimin θ m k ^ 2 * ((1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2))
        = θ ^ 2 * ((1 + ρ ^ 2) * ρ ^ 2 / (1 - ρ ^ 2)) / (m + k) ^ 2 := by
      unfold stepDimin; rw [div_pow]; ring
    rw [e] at h
    have h2 := mul_le_mul_of_nonneg_right (show (1 + ρ ^ 2) / 2 ≤ (3 + ρ ^ 2) / 4 by linarith)
      (hVnn k)
    linarith only [h, h2]
  · -- row W
    intro k hk
    have h := SGTRowW.rowW_exp P hA1 hA2 W hA34.nonneg hA34.row_sum hA34.col_sum
      (stepDimin θ m) x0 k η hη xstar
    rw [← hρdef, hηρ, ← hcdef] at h
    have hαδk := hαδ k hk
    have hαsk := hαs k
    have hαmk := hαm k
    have hsk := hs k
    obtain ⟨α, hαdef⟩ : ∃ α, α = stepDimin θ m k := ⟨_, rfl⟩
    obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = m + k := ⟨_, rfl⟩
    rw [← hαdef] at h hαδk hαsk hαmk
    rw [← hsdef] at hαsk hsk ⊢
    have hα0 : 0 < α := by rw [hαdef]; exact hαpos k
    have hα1 : α ≤ 1 := by rw [hδdef] at hαδk; exact hαδk.trans (min_le_left _ _)
    have hα3 : α ≤ (1 - ρ ^ 2) / (c * (256 * L ^ 2 * (n : ℝ) ^ 2)) := by
      rw [hδdef] at hαδk; exact hαδk.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ hcn] at hα3
    have hα2m : α ^ 2 ≤ θ ^ 2 / m ^ 2 := by
      rw [← div_pow]; exact pow_le_pow_left₀ hα0.le hαmk 2
    have hW1 : (1 + ρ ^ 2) / 2 + 64 * c * L ^ 2 * (n : ℝ) ^ 2 * α ^ 2 ≤ (3 + ρ ^ 2) / 4 := by
      have hA : α ^ 2 ≤ α := by
        have := mul_le_mul_of_nonneg_left hα1 hα0.le
        linarith only [this]
      have hC := mul_le_mul_of_nonneg_left hA (mul_nonneg hc.le (by positivity) :
        (0 : ℝ) ≤ c * (64 * L ^ 2 * (n : ℝ) ^ 2))
      linarith only [hC, hα3]
    have hW2 : 512 * c * L ^ 4 * (n : ℝ) ^ 3 * α ^ 2
        ≤ c * (512 * L ^ 4 * (n : ℝ) ^ 3 * θ ^ 2 / m) / s := by
      rw [le_div_iff₀ hsk, show 512 * c * L ^ 4 * (n : ℝ) ^ 3 * α ^ 2 * s
        = c * (512 * L ^ 4 * (n : ℝ) ^ 3) * α * (α * s) by ring, hαsk]
      have h1 := mul_le_mul_of_nonneg_left hαmk (mul_nonneg (mul_nonneg hc.le (by positivity) :
        (0 : ℝ) ≤ c * (512 * L ^ 4 * (n : ℝ) ^ 3)) hθ0.le)
      have h2 : c * (512 * L ^ 4 * (n : ℝ) ^ 3) * θ * (θ / m)
          = c * (512 * L ^ 4 * (n : ℝ) ^ 3 * θ ^ 2 / m) := by ring
      linarith only [h1, h2]
    have hW3 := mul_le_mul_of_nonneg_left hα2m (mul_nonneg hc.le (by positivity) :
      (0 : ℝ) ≤ c * (512 * L ^ 4 * (n : ℝ) ^ 2))
    have hW4 := mul_le_mul_of_nonneg_left hα2m (mul_nonneg hc.le (by positivity) :
      (0 : ℝ) ≤ c * (128 * L ^ 2 * (n : ℝ) ^ 2 * ((n : ℝ) * σ ^ 2)))
    have hW5 := mul_le_mul_of_nonneg_left hα2m (mul_nonneg hc.le
      (mul_nonneg (by positivity) hK0) :
      (0 : ℝ) ≤ c * (256 * L ^ 2 * (n : ℝ) ^ 2 * ∑ i, ‖gradf i xstar‖ ^ 2))
    have q1 := mul_le_mul_of_nonneg_right hW1 (hWnn k)
    have q2 := mul_le_mul_of_nonneg_right hW2 (hUnn k)
    have q3 := mul_le_mul_of_nonneg_right hW3 (hVnn k)
    linarith only [h, q1, q2, q3, hW4, hW5]
