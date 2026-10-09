-- Prove2me | solution 1 for StochApproxDyn.SubgaussianNoise.subgaussian_A1_ae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T02:47:05.130913+00:00
-- url     : https://prove2.me/submissions/be49e0a4-e4c1-4acb-b751-7dc24592f13b

import Mathlib
import Definitions.Def_StochApproxDyn_MartingaleNoise_Interpolation
import Definitions.Def_StochApproxDyn_MartingaleNoise_AssumptionA1
import Definitions.Def_StochApproxDyn_MartingaleNoise_RobbinsMonro
import Definitions.Def_StochApproxDyn_SubgaussianNoise_Subgaussian

set_option autoImplicit false

namespace SAD_eee949e0
open MeasureTheory Filter Topology StochApproxDyn.MartingaleNoise StochApproxDyn.SubgaussianNoise
open StochApproxDyn.Interpolation
open scoped InnerProductSpace ENNReal

/-! ## Deterministic part -/

/-- partial sums `S_k = Σ_{i<k} γ_{i+1} u_{i+1}`. -/
noncomputable def psum {d : ℕ} (γ : ℕ → ℝ) (u : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  ∑ i ∈ Finset.range k, γ (i + 1) • u (i + 1)

lemma tau_succ (γ : ℕ → ℝ) (n : ℕ) : tau γ (n + 1) = tau γ n + γ (n + 1) := by
  simp [tau, Finset.sum_range_succ]

lemma tau_mono {γ : ℕ → ℝ} (h0 : ∀ n, 0 ≤ γ (n + 1)) : Monotone (tau γ) :=
  monotone_nat_of_le_succ fun n => by rw [tau_succ]; linarith [h0 n]

lemma tau_zero (γ : ℕ → ℝ) : tau γ 0 = 0 := by simp [tau]

lemma stepIndex_eq {γ : ℕ → ℝ} (h0 : ∀ n, 0 ≤ γ (n + 1)) {i : ℕ} {t : ℝ}
    (h1 : tau γ i ≤ t) (h2 : t < tau γ (i + 1)) : stepIndex γ t = i := by
  have hb : ∀ k ∈ {k : ℕ | tau γ k ≤ t}, k ≤ i := by
    intro k hk
    by_contra hki
    push Not at hki
    have := tau_mono h0 (show i + 1 ≤ k by omega)
    simp only [Set.mem_setOf_eq] at hk
    linarith
  unfold stepIndex
  exact le_antisymm (csSup_le ⟨i, h1⟩ hb) (le_csSup ⟨i, hb⟩ h1)

lemma stepIndex_bdd {γ : ℕ → ℝ} (hγ : IsStepSequence γ) (t : ℝ) :
    BddAbove {k : ℕ | tau γ k ≤ t} := by
  have ht : Tendsto (tau γ) atTop atTop := hγ.2.1
  obtain ⟨K, hK⟩ := (ht.eventually_gt_atTop t).exists_forall_of_atTop
  refine ⟨K, fun k hk => ?_⟩
  by_contra hkK
  push Not at hkK
  have := hK k hkK.le
  simp only [Set.mem_setOf_eq] at hk
  linarith

lemma stepIndex_spec {γ : ℕ → ℝ} (hγ : IsStepSequence γ) {t : ℝ} (ht : 0 ≤ t) :
    tau γ (stepIndex γ t) ≤ t ∧ t < tau γ (stepIndex γ t + 1) := by
  have hne : ({k : ℕ | tau γ k ≤ t}).Nonempty := ⟨0, by simp [tau_zero, ht]⟩
  have hmem : stepIndex γ t ∈ {k : ℕ | tau γ k ≤ t} := Nat.sSup_mem hne (stepIndex_bdd hγ t)
  refine ⟨hmem, ?_⟩
  by_contra h
  push Not at h
  have := le_csSup (stepIndex_bdd hγ t) (show stepIndex γ t + 1 ∈ {k : ℕ | tau γ k ≤ t} from h)
  exact absurd this (by unfold stepIndex; omega)

lemma le_stepIndex {γ : ℕ → ℝ} (hγ : IsStepSequence γ) {k : ℕ} {t : ℝ} (h : tau γ k ≤ t) :
    k ≤ stepIndex γ t :=
  le_csSup (stepIndex_bdd hγ t) h

lemma stepIndex_mono {γ : ℕ → ℝ} (hγ : IsStepSequence γ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    stepIndex γ s ≤ stepIndex γ t :=
  le_stepIndex hγ ((stepIndex_spec hγ hs).1.trans hst)

lemma noisePath_piece {d : ℕ} {γ : ℕ → ℝ} (h0 : ∀ n, 0 ≤ γ (n + 1))
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) {x : ℝ} (h1 : tau γ i ≤ x)
    (h2 : x ≤ tau γ (i + 1)) :
    IntervalIntegrable (noisePath γ u) volume (tau γ i) x ∧
      ∫ s in (tau γ i)..x, noisePath γ u s = (x - tau γ i) • u (i + 1) := by
  have heq : Set.EqOn (noisePath γ u) (fun _ => u (i + 1)) (Set.Ioo (tau γ i) x) := by
    intro s hs
    simp only [noisePath]
    rw [stepIndex_eq h0 hs.1.le (lt_of_lt_of_le hs.2 h2)]
  constructor
  · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le h1]
    exact (integrableOn_const (by simp [Real.volume_Ioo])).congr_fun heq.symm measurableSet_Ioo
  · rw [intervalIntegral.integral_of_le h1, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo heq, setIntegral_const, Real.volume_real_Ioo_of_le h1]

lemma integral_tau {d : ℕ} {γ : ℕ → ℝ} (h0 : ∀ n, 0 ≤ γ (n + 1))
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    IntervalIntegrable (noisePath γ u) volume 0 (tau γ k) ∧
      ∫ s in (0 : ℝ)..(tau γ k), noisePath γ u s = psum γ u k := by
  induction k with
  | zero => simp [tau_zero, psum]
  | succ k ih =>
    have h1 : tau γ k ≤ tau γ (k + 1) := tau_mono h0 (Nat.le_succ k)
    obtain ⟨hI, hval⟩ := noisePath_piece h0 u k h1 le_rfl
    refine ⟨ih.1.trans hI, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ih.1 hI, ih.2, hval, tau_succ]
    simp [psum, Finset.sum_range_succ]

/-- the integral of the noise path from `0` to `t ≥ 0`. -/
lemma integral_formula {d : ℕ} {γ : ℕ → ℝ} (hγ : IsStepSequence γ)
    (u : ℕ → EuclideanSpace ℝ (Fin d)) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (noisePath γ u) volume 0 t ∧
      ∫ s in (0 : ℝ)..t, noisePath γ u s =
        psum γ u (stepIndex γ t) + (t - tau γ (stepIndex γ t)) • u (stepIndex γ t + 1) := by
  obtain ⟨hs1, hs2⟩ := stepIndex_spec hγ ht
  obtain ⟨hA, hAv⟩ := integral_tau hγ.1 u (stepIndex γ t)
  obtain ⟨hB, hBv⟩ := noisePath_piece hγ.1 u (stepIndex γ t) hs1 hs2.le
  refine ⟨hA.trans hB, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB, hAv, hBv]

/-- block maximum of the partial-sum increments over the index block `[b, e]`. -/
noncomputable def blk {d : ℕ} (γ : ℕ → ℝ) (u : ℕ → EuclideanSpace ℝ (Fin d)) (b e : ℕ) : ℝ≥0∞ :=
  (Finset.Icc b e).sup fun k => ‖psum γ u k - psum γ u b‖ₑ

lemma blk_le {d : ℕ} (γ : ℕ → ℝ) (u : ℕ → EuclideanSpace ℝ (Fin d)) {b e k : ℕ}
    (hk1 : b ≤ k) (hk2 : k ≤ e) : ‖psum γ u k - psum γ u b‖ₑ ≤ blk γ u b e :=
  Finset.le_sup (f := fun k => ‖psum γ u k - psum γ u b‖ₑ) (Finset.mem_Icc.2 ⟨hk1, hk2⟩)

lemma diff_le_blk {d : ℕ} (γ : ℕ → ℝ) (u : ℕ → EuclideanSpace ℝ (Fin d)) {b e k l : ℕ}
    (hk1 : b ≤ k) (hk2 : k ≤ e) (hl1 : b ≤ l) (hl2 : l ≤ e) :
    ‖psum γ u k - psum γ u l‖ₑ ≤ 2 * blk γ u b e := by
  have : psum γ u k - psum γ u l = (psum γ u k - psum γ u b) - (psum γ u l - psum γ u b) := by
    abel
  rw [this, two_mul]
  exact enorm_sub_le.trans (add_le_add (blk_le γ u hk1 hk2) (blk_le γ u hl1 hl2))

lemma psum_succ_sub {d : ℕ} (γ : ℕ → ℝ) (u : ℕ → EuclideanSpace ℝ (Fin d)) (m : ℕ) :
    psum γ u (m + 1) - psum γ u m = γ (m + 1) • u (m + 1) := by
  simp [psum, Finset.sum_range_succ]

lemma interp_le {d : ℕ} {γ : ℕ → ℝ} (hγ : IsStepSequence γ) (u : ℕ → EuclideanSpace ℝ (Fin d))
    {t : ℝ} (ht : 0 ≤ t) {b e : ℕ} (hb : b ≤ stepIndex γ t) (he : stepIndex γ t + 1 ≤ e) :
    ‖(psum γ u (stepIndex γ t) + (t - tau γ (stepIndex γ t)) • u (stepIndex γ t + 1))
      - psum γ u b‖ₑ ≤ 3 * blk γ u b e := by
  set m := stepIndex γ t with hm
  obtain ⟨hs1, hs2⟩ := stepIndex_spec hγ ht
  rw [← hm] at hs1 hs2
  rw [tau_succ] at hs2
  have h1 : ‖(t - tau γ m) • u (m + 1)‖ₑ ≤ ‖psum γ u (m + 1) - psum γ u m‖ₑ := by
    rw [psum_succ_sub, enorm_le_iff_norm_le, norm_smul, norm_smul]
    gcongr
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg (hγ.1 m)]
    linarith
  have h2 := diff_le_blk γ u (k := m + 1) (l := m) (b := b) (e := e) (by omega) he hb (by omega)
  have h3 := blk_le γ u (k := m) (e := e) hb (by omega)
  have : (psum γ u m + (t - tau γ m) • u (m + 1)) - psum γ u b
      = (psum γ u m - psum γ u b) + (t - tau γ m) • u (m + 1) := by abel
  rw [this]
  calc _ ≤ ‖psum γ u m - psum γ u b‖ₑ + ‖(t - tau γ m) • u (m + 1)‖ₑ := enorm_add_le _ _
    _ ≤ blk γ u b e + 2 * blk γ u b e := add_le_add h3 (h1.trans h2)
    _ = 3 * blk γ u b e := by ring

lemma tau_nonneg {γ : ℕ → ℝ} (h0 : ∀ n, 0 ≤ γ (n + 1)) (n : ℕ) : 0 ≤ tau γ n := by
  have := tau_mono h0 (Nat.zero_le n); rwa [tau_zero] at this

lemma noiseDev_le_blk {d : ℕ} {γ : ℕ → ℝ} (hγ : IsStepSequence γ)
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (j L : ℕ) {t T : ℝ} (hjt : (j : ℝ) ≤ t)
    (htT : t + T ≤ (j : ℝ) + L) :
    noiseDev γ u t T ≤ 6 * blk γ u (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have ht0 : 0 ≤ t := hj0.trans hjt
  refine iSup₂_le fun h hh => ?_
  have hth : 0 ≤ t + h := by linarith [hh.1]
  obtain ⟨hA, hAv⟩ := integral_formula hγ u ht0
  obtain ⟨hB, hBv⟩ := integral_formula hγ u hth
  rw [← intervalIntegral.integral_interval_sub_left hB hA, hAv, hBv]
  have k1 : stepIndex γ j ≤ stepIndex γ t := stepIndex_mono hγ hj0 hjt
  have k2 : stepIndex γ t ≤ stepIndex γ (t + h) := stepIndex_mono hγ ht0 (by linarith [hh.1])
  have k3 : stepIndex γ (t + h) ≤ stepIndex γ ((j : ℝ) + L) :=
    stepIndex_mono hγ hth (by linarith [hh.2])
  have e1 := interp_le hγ u ht0 (b := stepIndex γ j) (e := stepIndex γ ((j : ℝ) + L) + 1)
    k1 (by omega)
  have e2 := interp_le hγ u hth (b := stepIndex γ j) (e := stepIndex γ ((j : ℝ) + L) + 1)
    (by omega) (by omega)
  set B := blk γ u (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1)
  calc _ = ‖((psum γ u (stepIndex γ (t + h)) + (t + h - tau γ (stepIndex γ (t + h))) •
          u (stepIndex γ (t + h) + 1)) - psum γ u (stepIndex γ j)) -
        ((psum γ u (stepIndex γ t) + (t - tau γ (stepIndex γ t)) • u (stepIndex γ t + 1)) -
          psum γ u (stepIndex γ j))‖ₑ := by congr 1; abel
    _ ≤ 3 * B + 3 * B := enorm_sub_le.trans (add_le_add e2 e1)
    _ = 6 * B := by ring

lemma a1Sup_le_blk {d : ℕ} {γ : ℕ → ℝ} (hγ : IsStepSequence γ)
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (n j L : ℕ) {T : ℝ} (hjn : (j : ℝ) < tau γ n)
    (hT : 0 ≤ T) (hjL : tau γ n + T ≤ (j : ℝ) + L) :
    a1Sup γ u n T ≤ 2 * blk γ u (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1) := by
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hn0 : 0 ≤ tau γ n := tau_nonneg hγ.1 n
  have hb : stepIndex γ j ≤ n := by
    by_contra hc
    push Not at hc
    have h1 := tau_mono hγ.1 hc.le
    have h2 := (stepIndex_spec hγ hj0).1
    linarith
  have hnL : n ≤ stepIndex γ ((j : ℝ) + L) :=
    le_stepIndex hγ (by linarith)
  have hTL : stepIndex γ (tau γ n + T) ≤ stepIndex γ ((j : ℝ) + L) :=
    stepIndex_mono hγ (by linarith) hjL
  refine Finset.sup_le fun k hk => ?_
  rw [Finset.mem_Ioc] at hk
  rw [Finset.sum_Ico_eq_sub _ hk.1.le]
  exact diff_le_blk γ u (by omega) (by omega) hb (by omega)

/-! ## Probabilistic part -/

/-- exponential of the projected partial sums. -/
noncomputable def Xp {d : ℕ} {Ω : Type*} (W : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (k : ℕ) (ω : Ω) : ℝ :=
  Real.exp ⟪θ, ∑ i ∈ Finset.range k, W i ω⟫_ℝ

lemma Xp_succ_fun {d : ℕ} {Ω : Type*} (W : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (k : ℕ) :
    Xp W θ (k + 1) = Xp W θ k * fun ω => Real.exp ⟪θ, W k ω⟫_ℝ := by
  funext ω
  simp [Xp, Finset.sum_range_succ, inner_add_right, Real.exp_add]

lemma Xp_sq {d : ℕ} {Ω : Type*} (W : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (θ : EuclideanSpace ℝ (Fin d)) (k : ℕ) (ω : Ω) :
    Xp W ((2 : ℝ) • θ) k ω = Xp W θ k ω ^ 2 := by
  unfold Xp
  rw [real_inner_smul_left, sq, ← Real.exp_add]
  ring_nf

lemma Xp_adapted {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (𝒢 : Filtration ℕ m0)
    (W : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hW : ∀ i, StronglyMeasurable[𝒢 (i + 1)] (W i))
    (θ : EuclideanSpace ℝ (Fin d)) (k : ℕ) : StronglyMeasurable[𝒢 k] (Xp W θ k) := by
  have hS : StronglyMeasurable[𝒢 k] (fun ω => ∑ i ∈ Finset.range k, W i ω) :=
    Finset.stronglyMeasurable_fun_sum (Finset.range k) fun i hi =>
      (hW i).mono (𝒢.mono (by simp at hi; omega))
  exact Real.continuous_exp.comp_stronglyMeasurable
    ((continuous_const.inner continuous_id).comp_stronglyMeasurable hS)

section Core
variable {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  (𝒢 : Filtration ℕ m0) (W : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (b : ℕ → ℝ) (Γ : ℝ)
  (hW : ∀ i, StronglyMeasurable[𝒢 (i + 1)] (W i))
  (hint : ∀ i θ, Integrable (fun ω => Real.exp ⟪θ, W i ω⟫_ℝ) P)
  (hup : ∀ i θ, P[fun ω => Real.exp ⟪θ, W i ω⟫_ℝ | 𝒢 i] ≤ᵐ[P]
    fun _ => Real.exp (Γ / 2 * b i ^ 2 * ‖θ‖ ^ 2))
  (hlow : ∀ i θ, (fun _ => (1 : ℝ)) ≤ᵐ[P] P[fun ω => Real.exp ⟪θ, W i ω⟫_ℝ | 𝒢 i])
include hW hint hup

lemma Xp_moment (k : ℕ) : ∀ θ : EuclideanSpace ℝ (Fin d), Integrable (Xp W θ k) P ∧
    ∫ ω, Xp W θ k ω ∂P ≤ Real.exp (Γ / 2 * ‖θ‖ ^ 2 * ∑ i ∈ Finset.range k, b i ^ 2) := by
  induction k with
  | zero =>
    intro θ
    have h0 : Xp W θ 0 = fun _ => 1 := by funext ω; simp [Xp]
    rw [h0]; simp
  | succ k ih =>
    intro θ
    have hY := hint k θ
    have hXk := (ih θ).1
    have hprod : Integrable (Xp W θ k * fun ω => Real.exp ⟪θ, W k ω⟫_ℝ) P := by
      refine Integrable.mono' (((ih ((2 : ℝ) • θ)).1.add (hint k ((2 : ℝ) • θ))).div_const 2)
        (hXk.aestronglyMeasurable.mul hY.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
      have hx := Xp_sq W θ k ω
      have hy : Real.exp ⟪(2 : ℝ) • θ, W k ω⟫_ℝ = Real.exp ⟪θ, W k ω⟫_ℝ ^ 2 := by
        rw [real_inner_smul_left, sq, ← Real.exp_add]; ring_nf
      have h1 : 0 ≤ Xp W θ k ω := (Real.exp_pos _).le
      have h2 : 0 ≤ Real.exp ⟪θ, W k ω⟫_ℝ := (Real.exp_pos _).le
      simp only [Pi.mul_apply, Pi.add_apply, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
      rw [hx, hy]
      nlinarith [sq_nonneg (Xp W θ k ω - Real.exp ⟪θ, W k ω⟫_ℝ)]
    rw [Xp_succ_fun]
    refine ⟨hprod, ?_⟩
    have hce := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (Xp_adapted 𝒢 W hW θ k)
      hprod hY
    calc ∫ ω, (Xp W θ k * fun ω => Real.exp ⟪θ, W k ω⟫_ℝ) ω ∂P
        = ∫ ω, (P[Xp W θ k * fun ω => Real.exp ⟪θ, W k ω⟫_ℝ | 𝒢 k]) ω ∂P :=
          (integral_condExp (𝒢.le k)).symm
      _ = ∫ ω, (Xp W θ k * P[fun ω => Real.exp ⟪θ, W k ω⟫_ℝ | 𝒢 k]) ω ∂P :=
          integral_congr_ae hce
      _ ≤ ∫ ω, Xp W θ k ω * Real.exp (Γ / 2 * b k ^ 2 * ‖θ‖ ^ 2) ∂P := by
          refine integral_mono_ae (integrable_condExp.congr hce) (hXk.mul_const _) ?_
          filter_upwards [hup k θ] with ω hω
          exact mul_le_mul_of_nonneg_left hω (Real.exp_pos _).le
      _ = (∫ ω, Xp W θ k ω ∂P) * Real.exp (Γ / 2 * b k ^ 2 * ‖θ‖ ^ 2) := integral_mul_const _ _
      _ ≤ Real.exp (Γ / 2 * ‖θ‖ ^ 2 * ∑ i ∈ Finset.range k, b i ^ 2) *
            Real.exp (Γ / 2 * b k ^ 2 * ‖θ‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (ih θ).2 (Real.exp_pos _).le
      _ = Real.exp (Γ / 2 * ‖θ‖ ^ 2 * ∑ i ∈ Finset.range (k + 1), b i ^ 2) := by
          rw [← Real.exp_add, Finset.sum_range_succ]; ring_nf

include hlow in
lemma Xp_submart (θ : EuclideanSpace ℝ (Fin d)) : Submartingale (Xp W θ) 𝒢 P := by
  refine submartingale_nat (fun k => Xp_adapted 𝒢 W hW θ k)
    (fun k => (Xp_moment 𝒢 W b Γ hW hint hup k θ).1) fun k => ?_
  have hprod := (Xp_moment 𝒢 W b Γ hW hint hup (k + 1) θ).1
  rw [Xp_succ_fun] at hprod ⊢
  have hce := condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (Xp_adapted 𝒢 W hW θ k)
    hprod (hint k θ)
  filter_upwards [hce, hlow k θ] with ω h1 h2
  rw [h1, Pi.mul_apply]
  exact le_mul_of_one_le_right (Real.exp_pos _).le h2

include hlow in
lemma dir_tail (hΓ : 0 < Γ) (w : EuclideanSpace ℝ (Fin d)) (hw : ‖w‖ = 1) (K : ℕ) (β : ℝ)
    (hβ : 0 < β) (hs : 0 < ∑ i ∈ Finset.range K, b i ^ 2) :
    P {ω | ∃ k ∈ Finset.range (K + 1), β ≤ ⟪w, ∑ i ∈ Finset.range k, W i ω⟫_ℝ} ≤
      ENNReal.ofReal (Real.exp (-(β ^ 2) / (2 * Γ * ∑ i ∈ Finset.range K, b i ^ 2))) := by
  set s := ∑ i ∈ Finset.range K, b i ^ 2 with hs_def
  set lam := β / (Γ * s) with hlam_def
  have hlam : 0 < lam := div_pos hβ (mul_pos hΓ hs)
  set θ := lam • w with hθ
  have hθn : ‖θ‖ = lam := by rw [hθ, norm_smul, hw, Real.norm_eq_abs, abs_of_pos hlam, mul_one]
  set ε : NNReal := (Real.exp (lam * β)).toNNReal with hε_def
  have hεr : (ε : ℝ) = Real.exp (lam * β) := Real.coe_toNNReal _ (Real.exp_pos _).le
  have hsub := Xp_submart 𝒢 W b Γ hW hint hup hlow θ
  have hmax := maximal_ineq hsub (fun k ω => (Real.exp_pos _).le) (ε := ε) K
  set A := {ω | (ε : ℝ) ≤ (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
      fun k => Xp W θ k ω} with hA
  have hsubset : {ω | ∃ k ∈ Finset.range (K + 1), β ≤ ⟪w, ∑ i ∈ Finset.range k, W i ω⟫_ℝ}
      ⊆ A := by
    rintro ω ⟨k, hk, hkβ⟩
    refine le_trans ?_ (Finset.le_sup' (fun k => Xp W θ k ω) hk)
    show (ε : ℝ) ≤ Xp W θ k ω
    rw [hεr]
    unfold Xp
    rw [hθ, real_inner_smul_left]
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hkβ hlam.le)
  have hmom := (Xp_moment 𝒢 W b Γ hW hint hup K θ)
  have hint_le : ∫ ω in A, Xp W θ K ω ∂P ≤ ∫ ω, Xp W θ K ω ∂P :=
    setIntegral_le_integral hmom.1 (ae_of_all _ fun ω => (Real.exp_pos _).le)
  have key : (ε : ℝ≥0∞) * P A ≤ ENNReal.ofReal (Real.exp (Γ / 2 * lam ^ 2 * s)) := by
    refine hmax.trans (ENNReal.ofReal_le_ofReal (hint_le.trans ?_))
    have := hmom.2
    rw [hθn] at this
    convert this using 2
  have e1 : Real.exp (Γ / 2 * lam ^ 2 * s) =
      Real.exp (lam * β) * Real.exp (-(β ^ 2) / (2 * Γ * s)) := by
    rw [← Real.exp_add]; congr 1; rw [hlam_def]; field_simp; ring
  have hε : (ε : ℝ≥0∞) = ENNReal.ofReal (Real.exp (lam * β)) := rfl
  rw [e1, ENNReal.ofReal_mul (Real.exp_pos _).le, hε] at key
  refine (measure_mono hsubset).trans ?_
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    ENNReal.ofReal_ne_top).1 key

include hlow in
lemma norm_tail (hΓ : 0 < Γ) (K : ℕ) (α : ℝ) (hα : 0 < α)
    (hs : 0 < ∑ i ∈ Finset.range K, b i ^ 2) :
    P {ω | ∃ k ∈ Finset.range (K + 1), α ≤ ‖∑ i ∈ Finset.range k, W i ω‖} ≤
      ENNReal.ofReal (2 * d * Real.exp (-((α / Real.sqrt d) ^ 2) /
        (2 * Γ * ∑ i ∈ Finset.range K, b i ^ 2))) := by
  set bs := EuclideanSpace.basisFun (Fin d) ℝ
  set β := α / Real.sqrt d with hβ_def
  set e := Real.exp (-(β ^ 2) / (2 * Γ * ∑ i ∈ Finset.range K, b i ^ 2)) with he
  have hpars : ∀ v : EuclideanSpace ℝ (Fin d), ‖v‖ ^ 2 = ∑ j, ⟪bs j, v⟫_ℝ ^ 2 := by
    intro v
    rw [← real_inner_self_eq_norm_sq, ← bs.sum_inner_mul_inner v v]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm v (bs j), sq]
  have hsubset : {ω | ∃ k ∈ Finset.range (K + 1), α ≤ ‖∑ i ∈ Finset.range k, W i ω‖} ⊆
      ⋃ j : Fin d, ({ω | ∃ k ∈ Finset.range (K + 1), β ≤ ⟪bs j, ∑ i ∈ Finset.range k, W i ω⟫_ℝ}
        ∪ {ω | ∃ k ∈ Finset.range (K + 1), β ≤ ⟪-bs j, ∑ i ∈ Finset.range k, W i ω⟫_ℝ}) := by
    rintro ω ⟨k, hk, hkα⟩
    set v := ∑ i ∈ Finset.range k, W i ω
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_union, not_exists, not_or] at hcon
    have hlt : ∀ j : Fin d, ⟪bs j, v⟫_ℝ ^ 2 < β ^ 2 := by
      intro j
      have h1 : ⟪bs j, v⟫_ℝ < β := by
        by_contra h; push Not at h; exact (hcon j).1 ⟨k, hk, h⟩
      have h2 : -⟪bs j, v⟫_ℝ < β := by
        by_contra h; push Not at h; exact (hcon j).2 ⟨k, hk, by rw [inner_neg_left]; exact h⟩
      nlinarith
    have hv2 : α ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hα.le hkα 2
    rw [hpars v] at hv2
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp at hv2
      nlinarith
    · have := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.2 ⟨⟨0, hd⟩⟩)
        (fun j (_ : j ∈ Finset.univ) => hlt j)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hβ_def, div_pow,
        Real.sq_sqrt (Nat.cast_nonneg d)] at this
      have hd' : (d : ℝ) ≠ 0 := by positivity
      field_simp at this
      linarith
  refine (measure_mono hsubset).trans ((measure_iUnion_fintype_le P _).trans ?_)
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  have hβpos : 0 < β := div_pos hα (Real.sqrt_pos.2 (by exact_mod_cast hd))
  have hj : ∀ j : Fin d, P ({ω | ∃ k ∈ Finset.range (K + 1),
      β ≤ ⟪bs j, ∑ i ∈ Finset.range k, W i ω⟫_ℝ} ∪ {ω | ∃ k ∈ Finset.range (K + 1),
      β ≤ ⟪-bs j, ∑ i ∈ Finset.range k, W i ω⟫_ℝ}) ≤ 2 * ENNReal.ofReal e := by
    intro j
    have hn : ‖bs j‖ = 1 := bs.orthonormal.1 j
    refine (measure_union_le _ _).trans ?_
    rw [two_mul]
    exact add_le_add (dir_tail 𝒢 W b Γ hW hint hup hlow hΓ (bs j) hn K β hβpos hs)
      (dir_tail 𝒢 W b Γ hW hint hup hlow hΓ (-bs j) (by rw [norm_neg, hn]) K β hβpos hs)
  refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_natCast]
  ring_nf
  exact le_rfl

end Core

/-! ## Concrete instantiation -/

/-- the filtration shifted by `b`. -/
def shiftF {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0) (b : ℕ) :
    Filtration ℕ m0 where
  seq k := ℱ (b + k)
  mono' i j h := ℱ.mono (by omega)
  le' k := ℱ.le _

lemma condExp_exp_ge_one {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ m0)
    (V : Ω → EuclideanSpace ℝ (Fin d)) (hV : Integrable V P) (h0 : P[V | m] =ᵐ[P] 0)
    (v : EuclideanSpace ℝ (Fin d)) (hexp : Integrable (fun ω => Real.exp ⟪v, V ω⟫_ℝ) P) :
    (fun _ => (1 : ℝ)) ≤ᵐ[P] P[fun ω => Real.exp ⟪v, V ω⟫_ℝ | m] := by
  set g : Ω → ℝ := fun ω => ⟪v, V ω⟫_ℝ with hg
  have hgi : Integrable g P := hV.const_inner v
  have h1 : P[(fun _ => (1 : ℝ)) + g | m] ≤ᵐ[P] P[fun ω => Real.exp ⟪v, V ω⟫_ℝ | m] :=
    condExp_mono ((integrable_const 1).add hgi) hexp (ae_of_all _ fun ω => by
      simp only [Pi.add_apply, hg]; linarith [Real.add_one_le_exp ⟪v, V ω⟫_ℝ])
  have h2 := condExp_add (integrable_const (1 : ℝ)) hgi m
  have hc : P[fun _ => (1 : ℝ) | m] = fun _ => 1 := condExp_const hm 1
  have hT := (innerSL ℝ v).comp_condExp_comm hV (m := m)
  have hTg : (⇑(innerSL ℝ v) ∘ V) = g := by funext ω; simp [hg]
  rw [hTg] at hT
  filter_upwards [h1, h2, hT, h0] with ω e1 e2 e3 e4
  rw [e2, hc] at e1
  simp only [Pi.add_apply] at e1
  rw [← e3] at e1
  simp only [Function.comp_apply, e4, Pi.zero_apply, map_zero] at e1
  linarith

lemma block_tail {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (γ : ℕ → ℝ)
    (U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (Γ : ℝ) (hΓ : 0 < Γ)
    (hsg : IsSubgaussianWith P ℱ U Γ)
    (hmeas : ∀ n : ℕ, StronglyMeasurable[ℱ (n + 1)] (U (n + 1)))
    (hint : ∀ n : ℕ, Integrable (U (n + 1)) P) (hmart : ∀ n : ℕ, P[U (n + 1) | ℱ n] =ᵐ[P] 0)
    (b K : ℕ) (α : ℝ) (hα : 0 < α) (hs : 0 < ∑ i ∈ Finset.range K, γ (b + i + 1) ^ 2) :
    P {ω | ∃ k ∈ Finset.range (K + 1),
        α ≤ ‖∑ i ∈ Finset.range k, γ (b + i + 1) • U (b + i + 1) ω‖} ≤
      ENNReal.ofReal (2 * d * Real.exp (-((α / Real.sqrt d) ^ 2) /
        (2 * Γ * ∑ i ∈ Finset.range K, γ (b + i + 1) ^ 2))) := by
  have hfe : ∀ (i : ℕ) (θ : EuclideanSpace ℝ (Fin d)),
      (fun ω => Real.exp ⟪θ, γ (b + i + 1) • U (b + i + 1) ω⟫_ℝ) =
        fun ω => Real.exp ⟪γ (b + i + 1) • θ, U (b + i + 1) ω⟫_ℝ := by
    intro i θ; funext ω; rw [real_inner_smul_right, real_inner_smul_left]
  refine norm_tail (shiftF ℱ b) (fun i ω => γ (b + i + 1) • U (b + i + 1) ω)
    (fun i => γ (b + i + 1)) Γ ?_ ?_ ?_ ?_ hΓ K α hα hs
  · intro i; exact (hmeas (b + i)).const_smul (γ (b + i + 1))
  · intro i θ; rw [hfe]; exact (hsg (b + i) _).1
  · intro i θ; rw [hfe]
    filter_upwards [(hsg (b + i) (γ (b + i + 1) • θ)).2] with ω hω
    refine hω.trans (le_of_eq ?_)
    congr 1; rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  · intro i θ; rw [hfe]
    exact condExp_exp_ge_one _ ((shiftF ℱ b).le i) _ (hint (b + i)) (hmart (b + i)) _
      (hsg (b + i) _).1

lemma psum_add_sub {d : ℕ} (γ : ℕ → ℝ) (u : ℕ → EuclideanSpace ℝ (Fin d)) (b k : ℕ) :
    psum γ u (b + k) - psum γ u b = ∑ i ∈ Finset.range k, γ (b + i + 1) • u (b + i + 1) := by
  simp [psum, Finset.sum_range_add]

lemma tau_add (γ : ℕ → ℝ) (b K : ℕ) :
    tau γ (b + K) = tau γ b + ∑ i ∈ Finset.range K, γ (b + i + 1) := by
  simp [tau, Finset.sum_range_add]

lemma event_sub {d : ℕ} {Ω : Type*} (γ : ℕ → ℝ) (U : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    {b e : ℕ} (hbe : b ≤ e) {α : ℝ} (hα : 0 < α) :
    {ω | ENNReal.ofReal α ≤ blk γ (fun n => U n ω) b e} ⊆
      {ω | ∃ k ∈ Finset.range (e - b + 1),
        α ≤ ‖∑ i ∈ Finset.range k, γ (b + i + 1) • U (b + i + 1) ω‖} := by
  intro ω hω
  obtain ⟨k, hk, hkα⟩ := (Finset.le_sup_iff (ENNReal.ofReal_pos.2 hα)).1 hω
  rw [Finset.mem_Icc] at hk
  refine ⟨k - b, Finset.mem_range.2 (by omega), ?_⟩
  have := psum_add_sub γ (fun n => U n ω) b (k - b)
  rw [Nat.add_sub_cancel' hk.1] at this
  beta_reduce at this
  rw [← this, ← ENNReal.ofReal_le_ofReal_iff (norm_nonneg _), ofReal_norm]
  exact hkα

lemma tsum_block_ne_top {γ : ℕ → ℝ} (hγ : IsStepSequence γ)
    (hsum : ∀ c : ℝ, 0 < c →
      Summable (fun n : ℕ => if 0 < γ (n + 1) then Real.exp (-c / γ (n + 1)) else 0))
    (L : ℕ) (c Γ D : ℝ) (hc : 0 < c) (hΓ : 0 < Γ) (hD : 0 ≤ D) :
    ∑' j : ℕ, ENNReal.ofReal
      (if 0 < ∑ i ∈ Finset.range (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j),
          γ (stepIndex γ j + i + 1) ^ 2 then
        D * Real.exp (-c / (2 * Γ * ∑ i ∈ Finset.range
          (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j), γ (stepIndex γ j + i + 1) ^ 2))
      else 0) ≠ ∞ := by
  obtain ⟨G, hG⟩ := hγ.2.2.bddAbove_range
  have hGi : ∀ i, γ (i + 1) ≤ G := fun i => hG ⟨i + 1, rfl⟩
  have hG0 : 0 ≤ G := (hγ.1 0).trans (hGi 0)
  set Wd : ℝ := L + 2 * G + 1 with hWd
  have hWpos : 0 < Wd := by positivity
  set c' := c / (2 * Γ * Wd) with hc'
  have hc'pos : 0 < c' := by positivity
  set h : ℕ → ℝ := fun n => if 0 < γ (n + 1) then Real.exp (-c' / γ (n + 1)) else 0 with hh
  have hh0 : ∀ n, 0 ≤ h n := fun n => by simp only [hh]; split_ifs <;> positivity
  have hhs : Summable h := hsum c' hc'pos
  set a : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (D * h n) with ha
  have hafin : ∑' n, a n ≠ ∞ := by
    rw [ha, ← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg hD (hh0 n)) (hhs.mul_left D)]
    exact ENNReal.ofReal_ne_top
  set M : ℕ := ⌈(L : ℝ) + G⌉₊ with hM
  have hj : ∀ j : ℕ, ENNReal.ofReal
      (if 0 < ∑ i ∈ Finset.range (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j),
          γ (stepIndex γ j + i + 1) ^ 2 then
        D * Real.exp (-c / (2 * Γ * ∑ i ∈ Finset.range
          (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j), γ (stepIndex γ j + i + 1) ^ 2))
      else 0) ≤ ∑ n ∈ Finset.Ico (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1), a n := by
    intro j
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjL0 : (0 : ℝ) ≤ (j : ℝ) + L := by positivity
    set b := stepIndex γ j with hb
    set e := stepIndex γ ((j : ℝ) + L) + 1 with he
    have hbe : b ≤ e := by
      have := stepIndex_mono hγ hj0 (show (j : ℝ) ≤ (j : ℝ) + L by linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)])
      omega
    set K := e - b with hK
    split_ifs with hs
    · have hKne : (Finset.range K).Nonempty := by
        rw [Finset.nonempty_range_iff]; rintro hK0; rw [hK0] at hs; simp at hs
      obtain ⟨i0, hi0, hmax⟩ := Finset.exists_max_image (Finset.range K) (fun i => γ (b + i + 1)) hKne
      set g := γ (b + i0 + 1) with hgdef
      have hsle : ∑ i ∈ Finset.range K, γ (b + i + 1) ^ 2 ≤ g * ∑ i ∈ Finset.range K, γ (b + i + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun i hi => by
          rw [sq]; exact mul_le_mul_of_nonneg_right (hmax i hi) (hγ.1 _)
      have hSig : ∑ i ∈ Finset.range K, γ (b + i + 1) ≤ Wd := by
        have h1 := tau_add γ b K
        rw [hK, Nat.add_sub_cancel' hbe] at h1
        obtain ⟨s1, s2⟩ := stepIndex_spec hγ hj0
        obtain ⟨s3, s4⟩ := stepIndex_spec hγ hjL0
        rw [← hb] at s1 s2
        rw [tau_succ] at s2
        have h2 : tau γ e = tau γ (stepIndex γ ((j : ℝ) + L)) + γ (stepIndex γ ((j : ℝ) + L) + 1) :=
          by rw [he, tau_succ]
        have := hGi b
        have := hGi (stepIndex γ ((j : ℝ) + L))
        linarith
      have hSig0 : 0 ≤ ∑ i ∈ Finset.range K, γ (b + i + 1) := Finset.sum_nonneg fun i _ => hγ.1 _
      have hg : 0 < g := by
        by_contra hg; push Not at hg; nlinarith
      have hsW : ∑ i ∈ Finset.range K, γ (b + i + 1) ^ 2 ≤ g * Wd :=
        hsle.trans (mul_le_mul_of_nonneg_left hSig hg.le)
      have hexp : D * Real.exp (-c / (2 * Γ * ∑ i ∈ Finset.range K, γ (b + i + 1) ^ 2)) ≤
          D * h (b + i0) := by
        apply mul_le_mul_of_nonneg_left _ hD
        simp only [hh]
        rw [if_pos hg]
        apply Real.exp_le_exp.2
        have e1 : -c' / g = -(c / (2 * Γ * Wd * g)) := by rw [hc']; ring
        rw [e1, neg_div]
        apply neg_le_neg
        apply div_le_div_of_nonneg_left hc.le (by positivity)
        nlinarith
      calc _ ≤ a (b + i0) := ENNReal.ofReal_le_ofReal hexp
        _ ≤ _ := Finset.single_le_sum (f := a) (fun n _ => zero_le)
            (Finset.mem_Ico.2 ⟨by omega, by rw [Finset.mem_range] at hi0; omega⟩)
    · rw [ENNReal.ofReal_zero]; exact zero_le
  have hmult : ∀ n j : ℕ, n ∈ Finset.Ico (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1) →
      j ∈ Finset.Ico ⌈tau γ n - L⌉₊ ⌈tau γ n + G⌉₊ := by
    intro n j hn
    rw [Finset.mem_Ico] at hn ⊢
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjL0 : (0 : ℝ) ≤ (j : ℝ) + L := by positivity
    obtain ⟨s1, s2⟩ := stepIndex_spec hγ hj0
    obtain ⟨s3, s4⟩ := stepIndex_spec hγ hjL0
    constructor
    · rw [Nat.ceil_le]
      have := tau_mono hγ.1 (show n ≤ stepIndex γ ((j : ℝ) + L) by omega)
      linarith
    · rw [Nat.lt_ceil]
      have h1 := tau_mono hγ.1 (show stepIndex γ j + 1 ≤ n + 1 by omega)
      rw [tau_succ γ n] at h1
      linarith [hGi n]
  have hcard : ∀ n : ℕ, (Finset.Ico ⌈tau γ n - L⌉₊ ⌈tau γ n + G⌉₊).card ≤ M := by
    intro n
    have := Nat.ceil_add_le (tau γ n - L) (L + G)
    rw [show tau γ n - L + (L + G) = tau γ n + G by ring] at this
    rw [Nat.card_Ico]
    omega
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top M) hafin) ?_
  calc _ ≤ ∑' j : ℕ, ∑ n ∈ Finset.Ico (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1), a n :=
        ENNReal.tsum_le_tsum hj
    _ = ∑' j : ℕ, ∑' n : ℕ,
          (if n ∈ Finset.Ico (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1) then a n else 0) := by
        congr 1; funext j
        rw [tsum_eq_sum (s := Finset.Ico (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1))
          (fun n hn => if_neg hn)]
        exact Finset.sum_congr rfl fun n hn => (if_pos hn).symm
    _ = ∑' n : ℕ, ∑' j : ℕ,
          (if n ∈ Finset.Ico (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1) then a n else 0) :=
        ENNReal.tsum_comm
    _ ≤ ∑' n : ℕ, (M : ℝ≥0∞) * a n := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        calc _ ≤ ∑' j : ℕ, (if j ∈ Finset.Ico ⌈tau γ n - L⌉₊ ⌈tau γ n + G⌉₊ then a n else 0) := by
              refine ENNReal.tsum_le_tsum fun j => ?_
              by_cases h1 : n ∈ Finset.Ico (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1)
              · rw [if_pos h1, if_pos (hmult n j h1)]
              · rw [if_neg h1]; exact zero_le
          _ = ∑ j ∈ Finset.Ico ⌈tau γ n - L⌉₊ ⌈tau γ n + G⌉₊, a n := by
              rw [tsum_eq_sum (s := Finset.Ico ⌈tau γ n - L⌉₊ ⌈tau γ n + G⌉₊)
                (fun j hj => if_neg hj)]
              exact Finset.sum_congr rfl fun j hj => if_pos hj
          _ ≤ (M : ℝ≥0∞) * a n := by
              rw [Finset.sum_const, nsmul_eq_mul]
              gcongr; exact_mod_cast hcard n
    _ = (M : ℝ≥0∞) * ∑' n, a n := ENNReal.tsum_mul_left

/-- Borel–Cantelli assembly: a.s. all grid block maxima tend to `0`. -/
lemma ae_blk_tendsto {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : IsRobbinsMonro P ℱ F γ x U)
    (hsg : IsSubgaussian P ℱ U)
    (hsum : ∀ c : ℝ, 0 < c →
      Summable (fun n : ℕ => if 0 < γ (n + 1) then Real.exp (-c / γ (n + 1)) else 0)) :
    ∀ᵐ ω ∂P, ∀ L : ℕ, Tendsto (fun j : ℕ =>
      blk γ (fun n => U n ω) (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1)) atTop (𝓝 0) := by
  obtain ⟨Γ, hΓ, hsgw⟩ := hsg
  obtain ⟨-, hγ, -, hmeas, hint, hmart⟩ := hRM
  have key : ∀ L r : ℕ, ∀ᵐ ω ∂P, ∀ᶠ j : ℕ in atTop, ω ∉ {ω | ENNReal.ofReal (1 / ((r : ℝ) + 1)) ≤
      blk γ (fun n => U n ω) (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1)} := by
    intro L r
    apply ae_eventually_notMem
    set α : ℝ := 1 / ((r : ℝ) + 1) with hαdef
    have hα : 0 < α := by positivity
    have hPj : ∀ j : ℕ, P {ω | ENNReal.ofReal α ≤
        blk γ (fun n => U n ω) (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1)} ≤
        ENNReal.ofReal
          (if 0 < ∑ i ∈ Finset.range (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j),
              γ (stepIndex γ j + i + 1) ^ 2 then
            2 * d * Real.exp (-((α / Real.sqrt d) ^ 2) / (2 * Γ * ∑ i ∈ Finset.range
              (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j), γ (stepIndex γ j + i + 1) ^ 2))
          else 0) := by
      intro j
      have hbe : stepIndex γ j ≤ stepIndex γ ((j : ℝ) + L) + 1 := by
        have := stepIndex_mono hγ (Nat.cast_nonneg j)
          (show (j : ℝ) ≤ (j : ℝ) + L by linarith [(Nat.cast_nonneg L : (0:ℝ) ≤ L)])
        omega
      refine (measure_mono (event_sub γ U hbe hα)).trans ?_
      split_ifs with hs
      · exact block_tail P ℱ γ U Γ hΓ hsgw hmeas hint hmart _ _ α hα hs
      · have hs0 : ∀ i ∈ Finset.range (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j),
            γ (stepIndex γ j + i + 1) = 0 := by
          have hnn : ∀ i ∈ Finset.range (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j),
              0 ≤ γ (stepIndex γ j + i + 1) ^ 2 := fun i _ => sq_nonneg _
          have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
            (le_antisymm (not_lt.1 hs) (Finset.sum_nonneg hnn))
          intro i hi
          exact pow_eq_zero_iff (two_ne_zero) |>.1 (hz i hi)
        have hempty : {ω | ∃ k ∈ Finset.range
            (stepIndex γ ((j : ℝ) + L) + 1 - stepIndex γ j + 1),
            α ≤ ‖∑ i ∈ Finset.range k, γ (stepIndex γ j + i + 1) •
              U (stepIndex γ j + i + 1) ω‖} = ∅ := by
          ext ω
          simp only [Set.mem_empty_iff_false, iff_false]
          rintro ⟨k, hk, hkα⟩
          rw [Finset.sum_eq_zero (fun i hi => by
            rw [hs0 i (by rw [Finset.mem_range] at hk hi ⊢; omega), zero_smul]), norm_zero] at hkα
          linarith
        rw [hempty, measure_empty]
        exact zero_le
    rcases Nat.eq_zero_or_pos d with hd | hd
    · refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hPj)
      simp [hd]
    · have hc : 0 < (α / Real.sqrt d) ^ 2 :=
        pow_pos (div_pos hα (Real.sqrt_pos.2 (Nat.cast_pos.2 hd))) 2
      exact ne_top_of_le_ne_top (tsum_block_ne_top hγ hsum L _ Γ (2 * d) hc hΓ (by positivity))
        (ENNReal.tsum_le_tsum hPj)
  have key2 : ∀ᵐ ω ∂P, ∀ L r : ℕ, ∀ᶠ j : ℕ in atTop, ω ∉ {ω | ENNReal.ofReal (1 / ((r : ℝ) + 1)) ≤
      blk γ (fun n => U n ω) (stepIndex γ j) (stepIndex γ ((j : ℝ) + L) + 1)} := by
    rw [ae_all_iff]; intro L; rw [ae_all_iff]; exact key L
  filter_upwards [key2] with ω hω L
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεt : ε = ∞
  · exact Eventually.of_forall fun j => hεt ▸ le_top
  obtain ⟨r, hr⟩ := exists_nat_one_div_lt (ENNReal.toReal_pos hε.ne' hεt)
  filter_upwards [hω L r] with j hj
  have hj' := not_le.1 hj
  calc _ ≤ ENNReal.ofReal (1 / ((r : ℝ) + 1)) := hj'.le
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hr.le
    _ = ε := ENNReal.ofReal_toReal hεt

end SAD_eee949e0

open MeasureTheory ProbabilityTheory Filter Topology StochApproxDyn.SubgaussianNoise in
theorem solution {d : ℕ} {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0)
    (F : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (γ : ℕ → ℝ)
    (x U : ℕ → Ω → EuclideanSpace ℝ (Fin d)) (hRM : StochApproxDyn.MartingaleNoise.IsRobbinsMonro P ℱ F γ x U)
    (hsg : IsSubgaussian P ℱ U)
    (hsum : ∀ c : ℝ, 0 < c →
      Summable (fun n : ℕ => if 0 < γ (n + 1) then Real.exp (-c / γ (n + 1)) else 0)) :
    ∀ᵐ ω ∂P, StochApproxDyn.MartingaleNoise.IsA1 γ (fun n => U n ω) ∧ StochApproxDyn.MartingaleNoise.IsA1Delta γ (fun n => U n ω) := by
  have hγ : StochApproxDyn.MartingaleNoise.IsStepSequence γ := hRM.2.1
  filter_upwards [SAD_eee949e0.ae_blk_tendsto P ℱ F γ x U hRM hsg hsum] with ω hω
  constructor
  · intro T hT
    set L : ℕ := ⌈T⌉₊ + 2 with hL
    have hτ : Tendsto (StochApproxDyn.Interpolation.tau γ) atTop atTop := hγ.2.1
    set J : ℕ → ℕ := fun n => ⌊StochApproxDyn.Interpolation.tau γ n⌋₊ - 1 with hJdef
    have hJ : Tendsto J atTop atTop :=
      (tendsto_sub_atTop_nat 1).comp (tendsto_nat_floor_atTop.comp hτ)
    have h2 := ENNReal.Tendsto.const_mul ((hω L).comp hJ) (Or.inr (by norm_num : (2 : ENNReal) ≠ ⊤))
    rw [mul_zero] at h2
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
      (Eventually.of_forall fun n => zero_le) ?_
    filter_upwards [hτ.eventually_ge_atTop 1] with n hn
    have hf1 : 1 ≤ ⌊StochApproxDyn.Interpolation.tau γ n⌋₊ := Nat.le_floor (by simpa using hn)
    have hJn : ((J n : ℕ) : ℝ) = (⌊StochApproxDyn.Interpolation.tau γ n⌋₊ : ℝ) - 1 := by
      rw [hJdef]; push_cast [Nat.cast_sub hf1]; ring
    have hfl := Nat.floor_le (le_trans zero_le_one hn)
    have hfl2 := Nat.lt_floor_add_one (StochApproxDyn.Interpolation.tau γ n)
    have hTc := Nat.le_ceil T
    exact SAD_eee949e0.a1Sup_le_blk hγ (fun n => U n ω) n (J n) L (by rw [hJn]; linarith) hT.le
      (by rw [hJn, hL]; push_cast; linarith)
  · intro T hT
    set L : ℕ := ⌈T⌉₊ + 2 with hL
    have h6 := ENNReal.Tendsto.const_mul ((hω L).comp (tendsto_nat_floor_atTop (α := ℝ)))
      (Or.inr (by norm_num : (6 : ENNReal) ≠ ⊤))
    rw [mul_zero] at h6
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h6
      (Eventually.of_forall fun t => zero_le) ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hfl := Nat.floor_le ht
    have hfl2 := Nat.lt_floor_add_one t
    have hTc := Nat.le_ceil T
    exact SAD_eee949e0.noiseDev_le_blk hγ (fun n => U n ω) ⌊t⌋₊ L hfl
      (by rw [hL]; push_cast; linarith)
