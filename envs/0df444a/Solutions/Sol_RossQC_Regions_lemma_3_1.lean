-- Prove2me | solution 1 for RossQC.Regions.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:52:27.937477+00:00
-- url     : https://prove2.me/submissions/e94d1818-00e4-43fd-a07e-bb09e2fbc713

import Mathlib
import Definitions.Def_RossQC_Regions_Model
import Definitions.Def_RossQC_Regions_TwoState
import Definitions.Def_RossQC_Sufficient_Model

open Filter

namespace RossQC.Regions
namespace Scl
structure Good (M : RossQC.Sufficient.Model) : Prop where
  hβ0 : 0 < M.β
  hβ1 : M.β < 1
  hπ0 : 0 ≤ M.π
  hπ1 : M.π ≤ 1
  hC0 : 0 < M.C
  hCI : M.C < M.I
  hIR : M.I < M.R

noncomputable def Fop (M : RossQC.Sufficient.Model) (V : ℝ → ℝ) (P : ℝ) : ℝ :=
  min (M.rhs3 V P .produce) (min (M.rhs3 V P .inspect) (M.rhs3 V P .revise))

lemma valueIter_succ (M : RossQC.Sufficient.Model) (n : ℕ) (P : ℝ) :
    M.valueIter (n+1) P = Fop M (M.valueIter n) P := rfl

lemma T_mem {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.T P ∈ Set.Icc (0:ℝ) 1 ∧ P ≤ M.T P := by
  obtain ⟨h0, h1⟩ := hP
  have := h.hπ0; have := h.hπ1
  unfold RossQC.Sufficient.Model.T
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith

lemma π_mem {M : RossQC.Sufficient.Model} (h : Good M) : M.π ∈ Set.Icc (0:ℝ) 1 := ⟨h.hπ0, h.hπ1⟩

lemma one_mem' : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩

lemma iter_bounds {M : RossQC.Sufficient.Model} (h : Good M) : ∀ n : ℕ, ∀ P ∈ Set.Icc (0:ℝ) 1,
    0 ≤ M.valueIter n P ∧ M.valueIter n P ≤ M.R / (1 - M.β) := by
  have hβ0 := h.hβ0; have hβ1 := h.hβ1
  have hR : 0 < M.R := by linarith [h.hC0, h.hCI, h.hIR]
  have hB0 : 0 ≤ M.R / (1 - M.β) := div_nonneg hR.le (by linarith)
  have hB : M.R / (1 - M.β) = M.R + M.β * (M.R / (1 - M.β)) := by
    have hne : (1 - M.β) ≠ 0 := by linarith
    field_simp; ring
  intro n
  induction n with
  | zero => intro P _; simp [RossQC.Sufficient.Model.valueIter, hB0]
  | succ n ih =>
    intro P hP
    rw [valueIter_succ]
    unfold Fop
    obtain ⟨hT, _⟩ := T_mem h hP
    have i1 := ih _ hT
    have i2 := ih 1 one_mem'
    have i3 := ih _ (π_mem h)
    have hC := h.hC0; have hCI := h.hCI; have hIR := h.hIR
    obtain ⟨hP0, hP1⟩ := hP
    constructor
    · refine le_min ?_ (le_min ?_ ?_)
      · simp only [RossQC.Sufficient.Model.rhs3]
        have := mul_nonneg hβ0.le i1.1
        have := mul_nonneg hC.le hP0
        linarith
      · simp only [RossQC.Sufficient.Model.rhs3]
        have := mul_nonneg (mul_nonneg hβ0.le hP0) i2.1
        have := mul_nonneg (mul_nonneg hβ0.le (sub_nonneg.2 hP1)) i3.1
        linarith
      · simp only [RossQC.Sufficient.Model.rhs3]
        have := mul_nonneg hβ0.le i3.1
        linarith
    · refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      simp only [RossQC.Sufficient.Model.rhs3]
      have := mul_le_mul_of_nonneg_left i3.2 hβ0.le
      linarith

lemma F_lip {M : RossQC.Sufficient.Model} (h : Good M) (U W : ℝ → ℝ) (δ : ℝ)
    (hU : ∀ x ∈ Set.Icc (0:ℝ) 1, |U x - W x| ≤ δ) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    |Fop M U P - Fop M W P| ≤ M.β * δ := by
  have hβ0 := h.hβ0
  obtain ⟨hT, _⟩ := T_mem h hP
  have u1 := hU _ hT
  have u2 := hU 1 one_mem'
  have u3 := hU _ (π_mem h)
  obtain ⟨hP0, hP1⟩ := hP
  have d1 : |M.rhs3 U P .produce - M.rhs3 W P .produce| ≤ M.β * δ := by
    simp only [RossQC.Sufficient.Model.rhs3]
    have : M.C * P + M.β * U (M.T P) - (M.C * P + M.β * W (M.T P)) = M.β * (U (M.T P) - W (M.T P)) := by ring
    rw [this, abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left u1 hβ0.le
  have d3 : |M.rhs3 U P .revise - M.rhs3 W P .revise| ≤ M.β * δ := by
    simp only [RossQC.Sufficient.Model.rhs3]
    have : M.R + M.β * U M.π - (M.R + M.β * W M.π) = M.β * (U M.π - W M.π) := by ring
    rw [this, abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left u3 hβ0.le
  have d2 : |M.rhs3 U P .inspect - M.rhs3 W P .inspect| ≤ M.β * δ := by
    simp only [RossQC.Sufficient.Model.rhs3]
    have : M.I + M.β * P * U 1 + M.β * (1 - P) * U M.π - (M.I + M.β * P * W 1 + M.β * (1 - P) * W M.π)
        = (M.β * P) * (U 1 - W 1) + (M.β * (1 - P)) * (U M.π - W M.π) := by ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (M.β * P), abs_mul (M.β * (1 - P)), abs_of_nonneg (mul_nonneg hβ0.le hP0), abs_of_nonneg (mul_nonneg hβ0.le (sub_nonneg.2 hP1))]
    have e1 := mul_le_mul_of_nonneg_left u2 (mul_nonneg hβ0.le hP0)
    have e2 := mul_le_mul_of_nonneg_left u3 (mul_nonneg hβ0.le (sub_nonneg.2 hP1))
    nlinarith
  unfold Fop
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le d1 ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le d2 d3)

lemma iter_diff {M : RossQC.Sufficient.Model} (h : Good M) : ∀ n : ℕ, ∀ P ∈ Set.Icc (0:ℝ) 1,
    |M.valueIter (n+1) P - M.valueIter n P| ≤ M.R * M.β ^ n := by
  have hR : 0 < M.R := by linarith [h.hC0, h.hCI, h.hIR]
  intro n
  induction n with
  | zero =>
    intro P hP
    obtain ⟨hP0, hP1⟩ := hP
    have hb := (iter_bounds h 1 P ⟨hP0, hP1⟩).1
    have hu : M.valueIter 1 P ≤ M.R := by
      rw [valueIter_succ]
      refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      simp [RossQC.Sufficient.Model.rhs3, RossQC.Sufficient.Model.valueIter]
    simp only [RossQC.Sufficient.Model.valueIter, pow_zero, mul_one, sub_zero]
    rw [abs_of_nonneg (by simpa [RossQC.Sufficient.Model.valueIter] using hb)]
    simpa [RossQC.Sufficient.Model.valueIter] using hu
  | succ n ih =>
    intro P hP
    rw [valueIter_succ, valueIter_succ]
    have := F_lip h (M.valueIter (n+1)) (M.valueIter n) (M.R * M.β ^ n) ih hP
    calc _ ≤ M.β * (M.R * M.β ^ n) := this
      _ = M.R * M.β ^ (n+1) := by ring

lemma iter_tendsto {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P)) := by
  have hc : CauchySeq (fun n : ℕ => M.valueIter n P) := by
    refine cauchySeq_of_le_geometric M.β M.R h.hβ1 (fun n => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    exact iter_diff h n P hP
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  have : M.value P = a := ha.limUnder_eq
  rw [this]; exact ha

lemma value_bounds {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ M.value P ∧ M.value P ≤ M.R / (1 - M.β) :=
  ⟨ge_of_tendsto' (iter_tendsto h hP) (fun n => (iter_bounds h n P hP).1),
   le_of_tendsto' (iter_tendsto h hP) (fun n => (iter_bounds h n P hP).2)⟩

lemma rhs3_tendsto {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) (a : Action) :
    Tendsto (fun n : ℕ => M.rhs3 (M.valueIter n) P a) atTop (nhds (M.rhs3 M.value P a)) := by
  obtain ⟨hT, _⟩ := T_mem h hP
  have t1 := iter_tendsto h hT
  have t2 := iter_tendsto h one_mem'
  have t3 := iter_tendsto h (π_mem h)
  cases a <;> simp only [RossQC.Sufficient.Model.rhs3]
  · exact tendsto_const_nhds.add (t1.const_mul _)
  · exact (tendsto_const_nhds.add (t2.const_mul _)).add (t3.const_mul _)
  · exact tendsto_const_nhds.add (t3.const_mul _)

lemma value_fixed {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise)) := by
  have t := (rhs3_tendsto h hP .produce).min ((rhs3_tendsto h hP .inspect).min (rhs3_tendsto h hP .revise))
  have t' : Tendsto (fun n : ℕ => M.valueIter (n+1) P) atTop (nhds (M.value P)) :=
    (tendsto_add_atTop_iff_nat 1).2 (iter_tendsto h hP)
  exact tendsto_nhds_unique t' t

lemma T_mono {M : RossQC.Sufficient.Model} (h : Good M) {x y : ℝ} (hxy : x ≤ y) : M.T x ≤ M.T y := by
  unfold RossQC.Sufficient.Model.T
  have := h.hπ1
  nlinarith

lemma iter_mono {M : RossQC.Sufficient.Model} (h : Good M) : ∀ n : ℕ, ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    x ≤ y → M.valueIter n x ≤ M.valueIter n y := by
  have hβ0 := h.hβ0
  intro n
  induction n with
  | zero => intro x _ y _ _; simp [RossQC.Sufficient.Model.valueIter]
  | succ n ih =>
    intro x hx y hy hxy
    rw [valueIter_succ, valueIter_succ]
    unfold Fop
    obtain ⟨hTx, _⟩ := T_mem h hx
    obtain ⟨hTy, _⟩ := T_mem h hy
    have e1 := ih _ hTx _ hTy (T_mono h hxy)
    have e2 : M.valueIter n M.π ≤ M.valueIter n 1 := ih _ (π_mem h) _ one_mem' h.hπ1
    have hC := h.hC0
    refine min_le_min ?_ (min_le_min ?_ ?_)
    · simp only [RossQC.Sufficient.Model.rhs3]
      have := mul_le_mul_of_nonneg_left e1 hβ0.le
      nlinarith
    · simp only [RossQC.Sufficient.Model.rhs3]
      have := mul_nonneg (mul_nonneg hβ0.le (sub_nonneg.2 hxy)) (sub_nonneg.2 e2)
      nlinarith
    · simp only [RossQC.Sufficient.Model.rhs3]; exact le_rfl

lemma value_mono {M : RossQC.Sufficient.Model} (h : Good M) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hxy : x ≤ y) : M.value x ≤ M.value y :=
  le_of_tendsto_of_tendsto' (iter_tendsto h hx) (iter_tendsto h hy)
    (fun n => iter_mono h n x hx y hy hxy)

/-- concavity on [0,1] -/
def Conc (f : ℝ → ℝ) : Prop := ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
  ∀ t ∈ Set.Icc (0:ℝ) 1, (1 - t) * f x + t * f y ≤ f ((1 - t) * x + t * y)

lemma conc_min {u v : ℝ → ℝ} (hu : Conc u) (hv : Conc v) : Conc (fun P => min (u P) (v P)) := by
  intro x hx y hy t ht
  obtain ⟨ht0, ht1⟩ := ht
  have h1 : 0 ≤ 1 - t := by linarith
  refine le_min ?_ ?_
  · have a1 := mul_le_mul_of_nonneg_left (min_le_left (u x) (v x)) h1
    have a2 := mul_le_mul_of_nonneg_left (min_le_left (u y) (v y)) ht0
    have a3 := hu x hx y hy t ⟨ht0, ht1⟩
    linarith
  · have a1 := mul_le_mul_of_nonneg_left (min_le_right (u x) (v x)) h1
    have a2 := mul_le_mul_of_nonneg_left (min_le_right (u y) (v y)) ht0
    have a3 := hv x hx y hy t ⟨ht0, ht1⟩
    linarith

lemma iter_conc {M : RossQC.Sufficient.Model} (h : Good M) : ∀ n : ℕ, Conc (M.valueIter n) := by
  have hβ0 := h.hβ0
  intro n
  induction n with
  | zero => intro x _ y _ t _; simp [RossQC.Sufficient.Model.valueIter]
  | succ n ih =>
    have hfun : M.valueIter (n+1) = fun P => min (M.rhs3 (M.valueIter n) P .produce)
        (min (M.rhs3 (M.valueIter n) P .inspect) (M.rhs3 (M.valueIter n) P .revise)) := rfl
    rw [hfun]
    refine conc_min ?_ (conc_min ?_ ?_)
    · intro x hx y hy t ht
      obtain ⟨hTx, _⟩ := T_mem h hx
      obtain ⟨hTy, _⟩ := T_mem h hy
      have key := ih _ hTx _ hTy t ht
      have hT : M.T ((1 - t) * x + t * y) = (1 - t) * M.T x + t * M.T y := by
        unfold RossQC.Sufficient.Model.T; ring
      simp only [RossQC.Sufficient.Model.rhs3]
      rw [hT]
      have := mul_le_mul_of_nonneg_left key hβ0.le
      nlinarith
    · intro x hx y hy t ht
      simp only [RossQC.Sufficient.Model.rhs3]
      apply le_of_eq; ring
    · intro x hx y hy t ht
      simp only [RossQC.Sufficient.Model.rhs3]
      apply le_of_eq; ring

lemma value_conc {M : RossQC.Sufficient.Model} (h : Good M) : Conc M.value := by
  intro x hx y hy t ht
  have hz : (1 - t) * x + t * y ∈ Set.Icc (0:ℝ) 1 := by
    obtain ⟨ht0, ht1⟩ := ht; obtain ⟨hx0, hx1⟩ := hx; obtain ⟨hy0, hy1⟩ := hy
    constructor <;> nlinarith
  have t1 := ((iter_tendsto h hx).const_mul (1 - t)).add ((iter_tendsto h hy).const_mul t)
  exact le_of_tendsto_of_tendsto' t1 (iter_tendsto h hz) (fun n => iter_conc h n x hx y hy t ht)

/-- the constant D -/
noncomputable def Dc (M : RossQC.Sufficient.Model) : ℝ := M.C / (1 - M.β * (1 - M.π))

lemma D_facts {M : RossQC.Sufficient.Model} (h : Good M) :
    0 < 1 - M.β * (1 - M.π) ∧ 0 < Dc M ∧ M.C + M.β * (1 - M.π) * Dc M = Dc M ∧
    Dc M ≤ M.C / (1 - M.β) ∧ M.π * Dc M ≤ M.C := by
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hπ0 := h.hπ0; have hπ1 := h.hπ1; have hC := h.hC0
  have hq : 0 < 1 - M.β * (1 - M.π) := by nlinarith
  have hD : 0 < Dc M := div_pos hC hq
  have hDe : M.C + M.β * (1 - M.π) * Dc M = Dc M := by
    unfold Dc; field_simp; ring
  refine ⟨hq, hD, hDe, ?_, ?_⟩
  · unfold Dc
    exact div_le_div_of_nonneg_left hC.le (by linarith) (by nlinarith)
  · unfold Dc
    rw [← mul_div_assoc, div_le_iff₀ hq]
    nlinarith [mul_nonneg hC.le (mul_nonneg (sub_nonneg.2 hπ1) (sub_nonneg.2 hβ1.le))]

/-- upward Lipschitz bound on [π,1] -/
def Slope (M : RossQC.Sufficient.Model) (f : ℝ → ℝ) : Prop := ∀ x y : ℝ, M.π ≤ x → x ≤ y → y ≤ 1 →
  f y - f x ≤ Dc M * (y - x)

lemma slope_min {M : RossQC.Sufficient.Model} {u v : ℝ → ℝ} (hu : Slope M u) (hv : Slope M v) :
    Slope M (fun P => min (u P) (v P)) := by
  intro x y hx hxy hy
  rcases le_total (u x) (v x) with h1 | h1
  · have := hu x y hx hxy hy
    have := min_le_left (u y) (v y)
    simp only [min_eq_left h1]
    linarith
  · have := hv x y hx hxy hy
    have := min_le_right (u y) (v y)
    simp only [min_eq_right h1]
    linarith

lemma iter_slope {M : RossQC.Sufficient.Model} (h : Good M) : ∀ n : ℕ, Slope M (M.valueIter n) := by
  obtain ⟨hq, hD, hDe, _, _⟩ := D_facts h
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hπ0 := h.hπ0; have hπ1 := h.hπ1
  intro n
  induction n with
  | zero => intro x y _ hxy _; simp [RossQC.Sufficient.Model.valueIter]; nlinarith
  | succ n ih =>
    have hfun : M.valueIter (n+1) = fun P => min (M.rhs3 (M.valueIter n) P .produce)
        (min (M.rhs3 (M.valueIter n) P .inspect) (M.rhs3 (M.valueIter n) P .revise)) := rfl
    rw [hfun]
    refine slope_min ?_ (slope_min ?_ ?_)
    · intro x y hx hxy hy
      have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
      have hy' : y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, hy⟩
      obtain ⟨hTx, hTx2⟩ := T_mem h hx'
      obtain ⟨hTy, _⟩ := T_mem h hy'
      have hπT : M.π ≤ M.T x := by unfold RossQC.Sufficient.Model.T; nlinarith
      have hTxy : M.T y - M.T x = (1 - M.π) * (y - x) := by unfold RossQC.Sufficient.Model.T; ring
      have := ih _ _ hπT (T_mono h hxy) hTy.2
      simp only [RossQC.Sufficient.Model.rhs3]
      rw [hTxy] at this
      have h2 := mul_le_mul_of_nonneg_left this hβ0.le
      nlinarith
    · intro x y hx hxy hy
      have e := ih M.π 1 le_rfl hπ1 le_rfl
      have e2 := mul_le_mul_of_nonneg_left e hβ0.le
      have e3 := mul_le_mul_of_nonneg_left e2 (sub_nonneg.2 hxy)
      have e4 : M.β * (Dc M * (1 - M.π)) ≤ Dc M := by nlinarith [h.hC0]
      have e5 := mul_le_mul_of_nonneg_left e4 (sub_nonneg.2 hxy)
      simp only [RossQC.Sufficient.Model.rhs3]
      nlinarith
    · intro x y _ _ _
      simp only [RossQC.Sufficient.Model.rhs3]
      have : 0 ≤ Dc M * (y - x) := mul_nonneg hD.le (by linarith)
      linarith

lemma value_slope {M : RossQC.Sufficient.Model} (h : Good M) {x y : ℝ} (hx : M.π ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    M.value y - M.value x ≤ Dc M * (y - x) := by
  have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [h.hπ0], by linarith⟩
  have hy' : y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [h.hπ0], hy⟩
  exact le_of_tendsto_of_tendsto' ((iter_tendsto h hy').sub (iter_tendsto h hx')) tendsto_const_nhds
    (fun n => iter_slope h n x y hx hxy hy)

/-- produce-forever value -/
noncomputable def Wf (M : RossQC.Sufficient.Model) (Q : ℝ) : ℝ := M.C / (1 - M.β) - Dc M * (1 - Q)

lemma iter_le_W {M : RossQC.Sufficient.Model} (h : Good M) : ∀ n : ℕ, ∀ Q ∈ Set.Icc (0:ℝ) 1, M.valueIter n Q ≤ Wf M Q := by
  obtain ⟨hq, hD, hDe, hDle, _⟩ := D_facts h
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hC := h.hC0
  have hBt : M.C / (1 - M.β) = M.C + M.β * (M.C / (1 - M.β)) := by
    have hne : (1 - M.β) ≠ 0 := by linarith
    field_simp; ring
  intro n
  induction n with
  | zero =>
    intro Q hQ
    simp only [RossQC.Sufficient.Model.valueIter, Wf]
    have : Dc M * (1 - Q) ≤ Dc M := by nlinarith [hQ.1]
    linarith
  | succ n ih =>
    intro Q hQ
    obtain ⟨hT, _⟩ := T_mem h hQ
    rw [valueIter_succ]
    refine (min_le_left _ _).trans ?_
    simp only [RossQC.Sufficient.Model.rhs3, Wf]
    have := mul_le_mul_of_nonneg_left (ih _ hT) hβ0.le
    simp only [Wf] at this
    have e : M.C * Q + M.β * (M.C / (1 - M.β) - Dc M * (1 - M.T Q)) = M.C / (1 - M.β) - Dc M * (1 - Q) := by
      unfold RossQC.Sufficient.Model.T
      linear_combination (-1) * hBt + (-(1 - Q)) * hDe
    linarith

lemma value_le_W {M : RossQC.Sufficient.Model} (h : Good M) {Q : ℝ} (hQ : Q ∈ Set.Icc (0:ℝ) 1) : M.value Q ≤ Wf M Q :=
  le_of_tendsto' (iter_tendsto h hQ) (fun n => iter_le_W h n Q hQ)

lemma contOn_min {u v : ℝ → ℝ} {s : Set ℝ} (hu : ContinuousOn u s) (hv : ContinuousOn v s) :
    ContinuousOn (fun P => min (u P) (v P)) s :=
  continuous_min.comp_continuousOn (hu.prodMk hv)

lemma iter_cont {M : RossQC.Sufficient.Model} (h : Good M) : ∀ n : ℕ, ContinuousOn (M.valueIter n) (Set.Icc (0:ℝ) 1) := by
  intro n
  induction n with
  | zero => simp only [RossQC.Sufficient.Model.valueIter]; exact continuousOn_const
  | succ n ih =>
    have hT : ContinuousOn M.T (Set.Icc (0:ℝ) 1) := by
      unfold RossQC.Sufficient.Model.T; fun_prop
    have hmap : Set.MapsTo M.T (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := fun P hP => (T_mem h hP).1
    have hfun : M.valueIter (n+1) = fun P => min (M.rhs3 (M.valueIter n) P .produce)
        (min (M.rhs3 (M.valueIter n) P .inspect) (M.rhs3 (M.valueIter n) P .revise)) := rfl
    rw [hfun]
    simp only [RossQC.Sufficient.Model.rhs3]
    refine contOn_min ?_ (contOn_min ?_ ?_)
    · exact (continuousOn_const.mul continuousOn_id).add (continuousOn_const.mul (ih.comp hT hmap))
    · fun_prop
    · exact continuousOn_const

lemma value_cont {M : RossQC.Sufficient.Model} (h : Good M) : ContinuousOn M.value (Set.Icc (0:ℝ) 1) := by
  have hR : 0 < M.R := by linarith [h.hC0, h.hCI, h.hIR]
  have hs : Summable (fun k : ℕ => M.R * M.β ^ k) :=
    (summable_geometric_of_lt_one h.hβ0.le h.hβ1).mul_left _
  have hc := continuousOn_tsum (f := fun (k : ℕ) (P : ℝ) => M.valueIter (k+1) P - M.valueIter k P)
    (s := Set.Icc (0:ℝ) 1) (fun k => (iter_cont h (k+1)).sub (iter_cont h k)) hs
    (fun k P hP => by rw [Real.norm_eq_abs]; exact iter_diff h k P hP)
  refine hc.congr (fun P hP => ?_)
  have hsum : Summable (fun k : ℕ => ‖M.valueIter (k+1) P - M.valueIter k P‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => by rw [Real.norm_eq_abs]; exact iter_diff h k P hP) hs
  have hHS : HasSum (fun k : ℕ => M.valueIter (k+1) P - M.valueIter k P) (M.value P) := by
    rw [hasSum_iff_tendsto_nat_of_summable_norm hsum]
    have : ∀ n : ℕ, ∑ i ∈ Finset.range n, (M.valueIter (i+1) P - M.valueIter i P) = M.valueIter n P := by
      intro n
      rw [Finset.sum_range_sub (fun i => M.valueIter i P)]
      simp [RossQC.Sufficient.Model.valueIter]
    simp only [this]
    exact iter_tendsto h hP
  exact hHS.tsum_eq.symm


lemma min3_choice (x y z : ℝ) :
    min x (min y z) = x ∨ min x (min y z) = y ∨ min x (min y z) = z := by
  rcases min_choice y z with h | h <;> rcases min_choice x (min y z) with h' | h' <;> simp_all

lemma T_one {M : RossQC.Sufficient.Model} : M.T 1 = 1 := by unfold RossQC.Sufficient.Model.T; ring

lemma opt_produce {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1)
    (h1 : M.rhs3 M.value P .produce ≤ M.rhs3 M.value P .inspect)
    (h2 : M.rhs3 M.value P .produce ≤ M.rhs3 M.value P .revise) :
    M.rhs3 M.value P .produce = M.value P := by
  rw [value_fixed h hP]; exact (min_eq_left (le_min h1 h2)).symm

lemma opt_inspect {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1)
    (h1 : M.rhs3 M.value P .inspect ≤ M.rhs3 M.value P .produce)
    (h2 : M.rhs3 M.value P .inspect ≤ M.rhs3 M.value P .revise) :
    M.rhs3 M.value P .inspect = M.value P := by
  rw [value_fixed h hP, min_eq_left h2, min_eq_right h1]

lemma opt_revise {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1)
    (h1 : M.rhs3 M.value P .revise ≤ M.rhs3 M.value P .produce)
    (h2 : M.rhs3 M.value P .revise ≤ M.rhs3 M.value P .inspect) :
    M.rhs3 M.value P .revise = M.value P := by
  rw [value_fixed h hP, min_eq_right h2, min_eq_right h1]

lemma b_bound {M : RossQC.Sufficient.Model} (h : Good M) : (1 - M.β) * M.value 1 ≤ M.C := by
  have hfix := value_fixed h one_mem'
  have : M.value 1 ≤ M.C + M.β * M.value 1 := by
    have h1 : M.value 1 ≤ M.rhs3 M.value 1 .produce := by
      rw [hfix]; exact min_le_left _ _
    simpa [RossQC.Sufficient.Model.rhs3, T_one] using h1
  nlinarith

lemma a_le_b {M : RossQC.Sufficient.Model} (h : Good M) : M.value M.π ≤ M.value 1 :=
  value_mono h (π_mem h) one_mem' h.hπ1

lemma a_lt_r {M : RossQC.Sufficient.Model} (h : Good M) : M.value M.π < M.R + M.β * M.value M.π := by
  have := b_bound h
  have := a_le_b h
  have := h.hCI; have := h.hIR; have := h.hβ1
  nlinarith [h.hβ0]

lemma Pr_bound {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.rhs3 M.value P .produce ≤ M.β * M.value M.π + Dc M * P := by
  obtain ⟨hq, hD, hDe, _, _⟩ := D_facts h
  obtain ⟨hT, hPT⟩ := T_mem h hP
  have hπT : M.π ≤ M.T P := by
    unfold RossQC.Sufficient.Model.T; nlinarith [hP.1, h.hπ1]
  have hs := value_slope h le_rfl hπT hT.2
  have hTP : M.T P - M.π = (1 - M.π) * P := by unfold RossQC.Sufficient.Model.T; ring
  rw [hTP] at hs
  simp only [RossQC.Sufficient.Model.rhs3]
  have h2 := mul_le_mul_of_nonneg_left hs h.hβ0.le
  have h3 : (M.C + M.β * (1 - M.π) * Dc M) * P = Dc M * P := by rw [hDe]
  nlinarith

lemma In_expr {M : RossQC.Sufficient.Model} (P : ℝ) :
    M.rhs3 M.value P .inspect = M.I + M.β * M.value M.π + M.β * P * (M.value 1 - M.value M.π) := by
  simp only [RossQC.Sufficient.Model.rhs3]; ring

lemma Pr_lt_In_le_pi {M : RossQC.Sufficient.Model} (h : Good M) {P : ℝ} (hP0 : 0 ≤ P) (hPπ : P ≤ M.π) :
    M.rhs3 M.value P .produce < M.rhs3 M.value P .inspect := by
  obtain ⟨hq, hD, hDe, _, hπD⟩ := D_facts h
  have hP : P ∈ Set.Icc (0:ℝ) 1 := ⟨hP0, hPπ.trans h.hπ1⟩
  have h1 := Pr_bound h hP
  rw [In_expr]
  have h2 := a_le_b h
  have h3 : Dc M * P ≤ Dc M * M.π := mul_le_mul_of_nonneg_left hPπ hD.le
  have h4 := mul_nonneg (mul_nonneg h.hβ0.le hP0) (sub_nonneg.2 h2)
  have := h.hCI
  nlinarith

end Scl

def sm (β π C I R : ℝ) : RossQC.Sufficient.Model := ⟨β, π, C, I, R⟩

lemma tsum2 (f : Fin 2 → ℝ) : ∑' i, f i = f 0 + f 1 := by
  rw [tsum_fintype, Fin.sum_univ_two]

lemma T_belief (β π C I R P : ℝ) :
    (twoState β π C I R).T (belief P) = belief (T2 π P) := by
  funext i
  fin_cases i
  · simp [Model.T, tsum2, twoState, belief, T2]; ring
  · simp [Model.T, tsum2, twoState, belief, T2]; ring

lemma e_zero (β π C I R : ℝ) : (twoState β π C I R).e 0 = belief π := by
  funext i; fin_cases i <;> simp [Model.e, twoState, belief]

lemma e_i0 (β π C I R : ℝ) : (twoState β π C I R).e (twoState β π C I R).i₀ = belief π := e_zero ..

lemma e_one (β π C I R : ℝ) : (twoState β π C I R).e 1 = belief 1 := by
  funext i; fin_cases i <;> simp [Model.e, twoState, belief]

lemma iter_bridge (β π C I R : ℝ) (n : ℕ) :
    ∀ P : ℝ, (twoState β π C I R).valueIter n (belief P) = (sm β π C I R).valueIter n P := by
  induction n with
  | zero => intro P; simp [Model.valueIter, RossQC.Sufficient.Model.valueIter]
  | succ n ih =>
    intro P
    show (twoState β π C I R).bellman ((twoState β π C I R).valueIter n) (belief P) = _
    simp only [Model.bellman, Model.rhs, RossQC.Sufficient.Model.valueIter,
      RossQC.Sufficient.Model.rhs3, tsum2, T_belief, e_i0, e_zero, e_one, ih]
    simp [twoState, belief, sm, RossQC.Sufficient.Model.T, T2]
    refine congrArg₂ min ?_ (congrArg₂ min ?_ ?_) <;> ring_nf

lemma V2_eq (β π C I R P : ℝ) : V2 β π C I R P = (sm β π C I R).value P := by
  unfold V2 Model.Vβ RossQC.Sufficient.Model.value
  simp only [iter_bridge]


lemma good_of (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) : Scl.Good (sm β π C I R) :=
  ⟨hβ0, hβ1, hπ0, hπ1, hC, hCI, hIR⟩

lemma V2_fun (β π C I R : ℝ) : V2 β π C I R = (sm β π C I R).value :=
  funext (V2_eq β π C I R)

theorem equation_3_core (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    ∀ P ∈ Set.Icc (0 : ℝ) 1,
      V2 β π C I R P =
        min (rhs3 β π C I R (V2 β π C I R) P .produce)
          (min (rhs3 β π C I R (V2 β π C I R) P .inspect)
            (rhs3 β π C I R (V2 β π C I R) P .revise)) := by
  intro P hP
  have h := good_of β π C I R hβ0 hβ1 hπ0 hπ1 hC hCI hIR
  rw [V2_fun]
  exact Scl.value_fixed h hP

theorem lemma_3_1_core (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    MonotoneOn (V2 β π C I R) (Set.Icc 0 1) := by
  have h := good_of β π C I R hβ0 hβ1 hπ0 hπ1 hC hCI hIR
  rw [V2_fun]
  intro x hx y hy hxy
  exact Scl.value_mono h hx hy hxy

theorem lemma_3_2_core (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    ∀ P ∈ Set.Icc (0 : ℝ) π,
      rhs3 β π C I R (V2 β π C I R) P .produce < rhs3 β π C I R (V2 β π C I R) P .inspect ∧
      rhs3 β π C I R (V2 β π C I R) P .produce < rhs3 β π C I R (V2 β π C I R) P .revise := by
  intro P hP
  have h := good_of β π C I R hβ0 hβ1 hπ0 hπ1 hC hCI hIR
  rw [V2_fun]
  refine ⟨Scl.Pr_lt_In_le_pi h hP.1 hP.2, ?_⟩
  have hP' : P ∈ Set.Icc (0:ℝ) 1 := ⟨hP.1, hP.2.trans hπ1⟩
  have h1 : (sm β π C I R).rhs3 (sm β π C I R).value P .produce ≤
      β * (sm β π C I R).value π + Scl.Dc (sm β π C I R) * P := Scl.Pr_bound h hP'
  obtain ⟨hq, hD, hDe, _, hπD⟩ := Scl.D_facts h
  have h3 : Scl.Dc (sm β π C I R) * P ≤ Scl.Dc (sm β π C I R) * π :=
    mul_le_mul_of_nonneg_left hP.2 hD.le
  have h4 : Scl.Dc (sm β π C I R) * π ≤ C := by
    have := hπD; change π * Scl.Dc (sm β π C I R) ≤ C at this; linarith
  show (sm β π C I R).rhs3 _ P .produce < (sm β π C I R).rhs3 _ P .revise
  have h5 : (sm β π C I R).rhs3 (sm β π C I R).value P .revise = R + β * (sm β π C I R).value π := rfl
  rw [h5]
  have : C < R := by linarith
  linarith

end RossQC.Regions

open RossQC.Regions


theorem solution (β π C I R : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hπ0 : 0 ≤ π) (hπ1 : π ≤ 1)
    (hC : 0 < C) (hCI : C < I) (hIR : I < R) :
    MonotoneOn (V2 β π C I R) (Set.Icc 0 1) := by
  exact lemma_3_1_core β π C I R hβ0 hβ1 hπ0 hπ1 hC hCI hIR
