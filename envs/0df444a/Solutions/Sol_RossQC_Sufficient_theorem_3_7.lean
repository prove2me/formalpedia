-- Prove2me | solution 1 for RossQC.Sufficient.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:39:43.856259+00:00
-- url     : https://prove2.me/submissions/5f24554b-ebd0-4c49-8327-bb0aa970bdf0

import Definitions.Def_RossQC_Sufficient_Model

open Filter

namespace RossQC.Sufficient

open RossQC.Regions

structure Good (M : Model) : Prop where
  hβ0 : 0 < M.β
  hβ1 : M.β < 1
  hπ0 : 0 ≤ M.π
  hπ1 : M.π ≤ 1
  hC0 : 0 < M.C
  hCI : M.C < M.I
  hIR : M.I < M.R

noncomputable def Fop (M : Model) (V : ℝ → ℝ) (P : ℝ) : ℝ :=
  min (M.rhs3 V P .produce) (min (M.rhs3 V P .inspect) (M.rhs3 V P .revise))

lemma valueIter_succ (M : Model) (n : ℕ) (P : ℝ) :
    M.valueIter (n+1) P = Fop M (M.valueIter n) P := rfl

lemma T_mem {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.T P ∈ Set.Icc (0:ℝ) 1 ∧ P ≤ M.T P := by
  obtain ⟨h0, h1⟩ := hP
  have := h.hπ0; have := h.hπ1
  unfold Model.T
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;> nlinarith

lemma π_mem {M : Model} (h : Good M) : M.π ∈ Set.Icc (0:ℝ) 1 := ⟨h.hπ0, h.hπ1⟩

lemma one_mem' : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩

lemma iter_bounds {M : Model} (h : Good M) : ∀ n : ℕ, ∀ P ∈ Set.Icc (0:ℝ) 1,
    0 ≤ M.valueIter n P ∧ M.valueIter n P ≤ M.R / (1 - M.β) := by
  have hβ0 := h.hβ0; have hβ1 := h.hβ1
  have hR : 0 < M.R := by linarith [h.hC0, h.hCI, h.hIR]
  have hB0 : 0 ≤ M.R / (1 - M.β) := div_nonneg hR.le (by linarith)
  have hB : M.R / (1 - M.β) = M.R + M.β * (M.R / (1 - M.β)) := by
    have hne : (1 - M.β) ≠ 0 := by linarith
    field_simp; ring
  intro n
  induction n with
  | zero => intro P _; simp [Model.valueIter, hB0]
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
      · simp only [Model.rhs3]
        have := mul_nonneg hβ0.le i1.1
        have := mul_nonneg hC.le hP0
        linarith
      · simp only [Model.rhs3]
        have := mul_nonneg (mul_nonneg hβ0.le hP0) i2.1
        have := mul_nonneg (mul_nonneg hβ0.le (sub_nonneg.2 hP1)) i3.1
        linarith
      · simp only [Model.rhs3]
        have := mul_nonneg hβ0.le i3.1
        linarith
    · refine (min_le_right _ _).trans ((min_le_right _ _).trans ?_)
      simp only [Model.rhs3]
      have := mul_le_mul_of_nonneg_left i3.2 hβ0.le
      linarith

lemma F_lip {M : Model} (h : Good M) (U W : ℝ → ℝ) (δ : ℝ)
    (hU : ∀ x ∈ Set.Icc (0:ℝ) 1, |U x - W x| ≤ δ) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    |Fop M U P - Fop M W P| ≤ M.β * δ := by
  have hβ0 := h.hβ0
  obtain ⟨hT, _⟩ := T_mem h hP
  have u1 := hU _ hT
  have u2 := hU 1 one_mem'
  have u3 := hU _ (π_mem h)
  obtain ⟨hP0, hP1⟩ := hP
  have d1 : |M.rhs3 U P .produce - M.rhs3 W P .produce| ≤ M.β * δ := by
    simp only [Model.rhs3]
    have : M.C * P + M.β * U (M.T P) - (M.C * P + M.β * W (M.T P)) = M.β * (U (M.T P) - W (M.T P)) := by ring
    rw [this, abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left u1 hβ0.le
  have d3 : |M.rhs3 U P .revise - M.rhs3 W P .revise| ≤ M.β * δ := by
    simp only [Model.rhs3]
    have : M.R + M.β * U M.π - (M.R + M.β * W M.π) = M.β * (U M.π - W M.π) := by ring
    rw [this, abs_mul, abs_of_pos hβ0]
    exact mul_le_mul_of_nonneg_left u3 hβ0.le
  have d2 : |M.rhs3 U P .inspect - M.rhs3 W P .inspect| ≤ M.β * δ := by
    simp only [Model.rhs3]
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

lemma iter_diff {M : Model} (h : Good M) : ∀ n : ℕ, ∀ P ∈ Set.Icc (0:ℝ) 1,
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
      simp [Model.rhs3, Model.valueIter]
    simp only [Model.valueIter, pow_zero, mul_one, sub_zero]
    rw [abs_of_nonneg (by simpa [Model.valueIter] using hb)]
    simpa [Model.valueIter] using hu
  | succ n ih =>
    intro P hP
    rw [valueIter_succ, valueIter_succ]
    have := F_lip h (M.valueIter (n+1)) (M.valueIter n) (M.R * M.β ^ n) ih hP
    calc _ ≤ M.β * (M.R * M.β ^ n) := this
      _ = M.R * M.β ^ (n+1) := by ring

lemma iter_tendsto {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun n : ℕ => M.valueIter n P) atTop (nhds (M.value P)) := by
  have hc : CauchySeq (fun n : ℕ => M.valueIter n P) := by
    refine cauchySeq_of_le_geometric M.β M.R h.hβ1 (fun n => ?_)
    rw [Real.dist_eq, abs_sub_comm]
    exact iter_diff h n P hP
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hc
  have : M.value P = a := ha.limUnder_eq
  rw [this]; exact ha

lemma value_bounds {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    0 ≤ M.value P ∧ M.value P ≤ M.R / (1 - M.β) :=
  ⟨ge_of_tendsto' (iter_tendsto h hP) (fun n => (iter_bounds h n P hP).1),
   le_of_tendsto' (iter_tendsto h hP) (fun n => (iter_bounds h n P hP).2)⟩

lemma rhs3_tendsto {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) (a : Action) :
    Tendsto (fun n : ℕ => M.rhs3 (M.valueIter n) P a) atTop (nhds (M.rhs3 M.value P a)) := by
  obtain ⟨hT, _⟩ := T_mem h hP
  have t1 := iter_tendsto h hT
  have t2 := iter_tendsto h one_mem'
  have t3 := iter_tendsto h (π_mem h)
  cases a <;> simp only [Model.rhs3]
  · exact tendsto_const_nhds.add (t1.const_mul _)
  · exact (tendsto_const_nhds.add (t2.const_mul _)).add (t3.const_mul _)
  · exact tendsto_const_nhds.add (t3.const_mul _)

lemma value_fixed {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.value P = min (M.rhs3 M.value P .produce)
        (min (M.rhs3 M.value P .inspect) (M.rhs3 M.value P .revise)) := by
  have t := (rhs3_tendsto h hP .produce).min ((rhs3_tendsto h hP .inspect).min (rhs3_tendsto h hP .revise))
  have t' : Tendsto (fun n : ℕ => M.valueIter (n+1) P) atTop (nhds (M.value P)) :=
    (tendsto_add_atTop_iff_nat 1).2 (iter_tendsto h hP)
  exact tendsto_nhds_unique t' t

lemma T_mono {M : Model} (h : Good M) {x y : ℝ} (hxy : x ≤ y) : M.T x ≤ M.T y := by
  unfold Model.T
  have := h.hπ1
  nlinarith

lemma iter_mono {M : Model} (h : Good M) : ∀ n : ℕ, ∀ x ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
    x ≤ y → M.valueIter n x ≤ M.valueIter n y := by
  have hβ0 := h.hβ0
  intro n
  induction n with
  | zero => intro x _ y _ _; simp [Model.valueIter]
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
    · simp only [Model.rhs3]
      have := mul_le_mul_of_nonneg_left e1 hβ0.le
      nlinarith
    · simp only [Model.rhs3]
      have := mul_nonneg (mul_nonneg hβ0.le (sub_nonneg.2 hxy)) (sub_nonneg.2 e2)
      nlinarith
    · simp only [Model.rhs3]; exact le_rfl

lemma value_mono {M : Model} (h : Good M) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
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

lemma iter_conc {M : Model} (h : Good M) : ∀ n : ℕ, Conc (M.valueIter n) := by
  have hβ0 := h.hβ0
  intro n
  induction n with
  | zero => intro x _ y _ t _; simp [Model.valueIter]
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
        unfold Model.T; ring
      simp only [Model.rhs3]
      rw [hT]
      have := mul_le_mul_of_nonneg_left key hβ0.le
      nlinarith
    · intro x hx y hy t ht
      simp only [Model.rhs3]
      apply le_of_eq; ring
    · intro x hx y hy t ht
      simp only [Model.rhs3]
      apply le_of_eq; ring

lemma value_conc {M : Model} (h : Good M) : Conc M.value := by
  intro x hx y hy t ht
  have hz : (1 - t) * x + t * y ∈ Set.Icc (0:ℝ) 1 := by
    obtain ⟨ht0, ht1⟩ := ht; obtain ⟨hx0, hx1⟩ := hx; obtain ⟨hy0, hy1⟩ := hy
    constructor <;> nlinarith
  have t1 := ((iter_tendsto h hx).const_mul (1 - t)).add ((iter_tendsto h hy).const_mul t)
  exact le_of_tendsto_of_tendsto' t1 (iter_tendsto h hz) (fun n => iter_conc h n x hx y hy t ht)

/-- the constant D -/
noncomputable def Dc (M : Model) : ℝ := M.C / (1 - M.β * (1 - M.π))

lemma D_facts {M : Model} (h : Good M) :
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
def Slope (M : Model) (f : ℝ → ℝ) : Prop := ∀ x y : ℝ, M.π ≤ x → x ≤ y → y ≤ 1 →
  f y - f x ≤ Dc M * (y - x)

lemma slope_min {M : Model} {u v : ℝ → ℝ} (hu : Slope M u) (hv : Slope M v) :
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

lemma iter_slope {M : Model} (h : Good M) : ∀ n : ℕ, Slope M (M.valueIter n) := by
  obtain ⟨hq, hD, hDe, _, _⟩ := D_facts h
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hπ0 := h.hπ0; have hπ1 := h.hπ1
  intro n
  induction n with
  | zero => intro x y _ hxy _; simp [Model.valueIter]; nlinarith
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
      have hπT : M.π ≤ M.T x := by unfold Model.T; nlinarith
      have hTxy : M.T y - M.T x = (1 - M.π) * (y - x) := by unfold Model.T; ring
      have := ih _ _ hπT (T_mono h hxy) hTy.2
      simp only [Model.rhs3]
      rw [hTxy] at this
      have h2 := mul_le_mul_of_nonneg_left this hβ0.le
      nlinarith
    · intro x y hx hxy hy
      have e := ih M.π 1 le_rfl hπ1 le_rfl
      have e2 := mul_le_mul_of_nonneg_left e hβ0.le
      have e3 := mul_le_mul_of_nonneg_left e2 (sub_nonneg.2 hxy)
      have e4 : M.β * (Dc M * (1 - M.π)) ≤ Dc M := by nlinarith [h.hC0]
      have e5 := mul_le_mul_of_nonneg_left e4 (sub_nonneg.2 hxy)
      simp only [Model.rhs3]
      nlinarith
    · intro x y _ _ _
      simp only [Model.rhs3]
      have : 0 ≤ Dc M * (y - x) := mul_nonneg hD.le (by linarith)
      linarith

lemma value_slope {M : Model} (h : Good M) {x y : ℝ} (hx : M.π ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    M.value y - M.value x ≤ Dc M * (y - x) := by
  have hx' : x ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [h.hπ0], by linarith⟩
  have hy' : y ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [h.hπ0], hy⟩
  exact le_of_tendsto_of_tendsto' ((iter_tendsto h hy').sub (iter_tendsto h hx')) tendsto_const_nhds
    (fun n => iter_slope h n x y hx hxy hy)

/-- produce-forever value -/
noncomputable def Wf (M : Model) (Q : ℝ) : ℝ := M.C / (1 - M.β) - Dc M * (1 - Q)

lemma iter_le_W {M : Model} (h : Good M) : ∀ n : ℕ, ∀ Q ∈ Set.Icc (0:ℝ) 1, M.valueIter n Q ≤ Wf M Q := by
  obtain ⟨hq, hD, hDe, hDle, _⟩ := D_facts h
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hC := h.hC0
  have hBt : M.C / (1 - M.β) = M.C + M.β * (M.C / (1 - M.β)) := by
    have hne : (1 - M.β) ≠ 0 := by linarith
    field_simp; ring
  intro n
  induction n with
  | zero =>
    intro Q hQ
    simp only [Model.valueIter, Wf]
    have : Dc M * (1 - Q) ≤ Dc M := by nlinarith [hQ.1]
    linarith
  | succ n ih =>
    intro Q hQ
    obtain ⟨hT, _⟩ := T_mem h hQ
    rw [valueIter_succ]
    refine (min_le_left _ _).trans ?_
    simp only [Model.rhs3, Wf]
    have := mul_le_mul_of_nonneg_left (ih _ hT) hβ0.le
    simp only [Wf] at this
    have e : M.C * Q + M.β * (M.C / (1 - M.β) - Dc M * (1 - M.T Q)) = M.C / (1 - M.β) - Dc M * (1 - Q) := by
      unfold Model.T
      linear_combination (-1) * hBt + (-(1 - Q)) * hDe
    linarith

lemma value_le_W {M : Model} (h : Good M) {Q : ℝ} (hQ : Q ∈ Set.Icc (0:ℝ) 1) : M.value Q ≤ Wf M Q :=
  le_of_tendsto' (iter_tendsto h hQ) (fun n => iter_le_W h n Q hQ)

lemma contOn_min {u v : ℝ → ℝ} {s : Set ℝ} (hu : ContinuousOn u s) (hv : ContinuousOn v s) :
    ContinuousOn (fun P => min (u P) (v P)) s :=
  continuous_min.comp_continuousOn (hu.prodMk hv)

lemma iter_cont {M : Model} (h : Good M) : ∀ n : ℕ, ContinuousOn (M.valueIter n) (Set.Icc (0:ℝ) 1) := by
  intro n
  induction n with
  | zero => simp only [Model.valueIter]; exact continuousOn_const
  | succ n ih =>
    have hT : ContinuousOn M.T (Set.Icc (0:ℝ) 1) := by
      unfold Model.T; fun_prop
    have hmap : Set.MapsTo M.T (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := fun P hP => (T_mem h hP).1
    have hfun : M.valueIter (n+1) = fun P => min (M.rhs3 (M.valueIter n) P .produce)
        (min (M.rhs3 (M.valueIter n) P .inspect) (M.rhs3 (M.valueIter n) P .revise)) := rfl
    rw [hfun]
    simp only [Model.rhs3]
    refine contOn_min ?_ (contOn_min ?_ ?_)
    · exact (continuousOn_const.mul continuousOn_id).add (continuousOn_const.mul (ih.comp hT hmap))
    · fun_prop
    · exact continuousOn_const

lemma value_cont {M : Model} (h : Good M) : ContinuousOn M.value (Set.Icc (0:ℝ) 1) := by
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
      simp [Model.valueIter]
    simp only [this]
    exact iter_tendsto h hP
  exact hHS.tsum_eq.symm


lemma min3_choice (x y z : ℝ) :
    min x (min y z) = x ∨ min x (min y z) = y ∨ min x (min y z) = z := by
  rcases min_choice y z with h | h <;> rcases min_choice x (min y z) with h' | h' <;> simp_all

lemma T_one {M : Model} : M.T 1 = 1 := by unfold Model.T; ring

lemma opt_produce {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1)
    (h1 : M.rhs3 M.value P .produce ≤ M.rhs3 M.value P .inspect)
    (h2 : M.rhs3 M.value P .produce ≤ M.rhs3 M.value P .revise) :
    M.rhs3 M.value P .produce = M.value P := by
  rw [value_fixed h hP]; exact (min_eq_left (le_min h1 h2)).symm

lemma opt_inspect {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1)
    (h1 : M.rhs3 M.value P .inspect ≤ M.rhs3 M.value P .produce)
    (h2 : M.rhs3 M.value P .inspect ≤ M.rhs3 M.value P .revise) :
    M.rhs3 M.value P .inspect = M.value P := by
  rw [value_fixed h hP, min_eq_left h2, min_eq_right h1]

lemma opt_revise {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1)
    (h1 : M.rhs3 M.value P .revise ≤ M.rhs3 M.value P .produce)
    (h2 : M.rhs3 M.value P .revise ≤ M.rhs3 M.value P .inspect) :
    M.rhs3 M.value P .revise = M.value P := by
  rw [value_fixed h hP, min_eq_right h2, min_eq_right h1]

lemma b_bound {M : Model} (h : Good M) : (1 - M.β) * M.value 1 ≤ M.C := by
  have hfix := value_fixed h one_mem'
  have : M.value 1 ≤ M.C + M.β * M.value 1 := by
    have h1 : M.value 1 ≤ M.rhs3 M.value 1 .produce := by
      rw [hfix]; exact min_le_left _ _
    simpa [Model.rhs3, T_one] using h1
  nlinarith

lemma a_le_b {M : Model} (h : Good M) : M.value M.π ≤ M.value 1 :=
  value_mono h (π_mem h) one_mem' h.hπ1

lemma a_lt_r {M : Model} (h : Good M) : M.value M.π < M.R + M.β * M.value M.π := by
  have := b_bound h
  have := a_le_b h
  have := h.hCI; have := h.hIR; have := h.hβ1
  nlinarith [h.hβ0]

lemma Pr_bound {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1) :
    M.rhs3 M.value P .produce ≤ M.β * M.value M.π + Dc M * P := by
  obtain ⟨hq, hD, hDe, _, _⟩ := D_facts h
  obtain ⟨hT, hPT⟩ := T_mem h hP
  have hπT : M.π ≤ M.T P := by
    unfold Model.T; nlinarith [hP.1, h.hπ1]
  have hs := value_slope h le_rfl hπT hT.2
  have hTP : M.T P - M.π = (1 - M.π) * P := by unfold Model.T; ring
  rw [hTP] at hs
  simp only [Model.rhs3]
  have h2 := mul_le_mul_of_nonneg_left hs h.hβ0.le
  have h3 : (M.C + M.β * (1 - M.π) * Dc M) * P = Dc M * P := by rw [hDe]
  nlinarith

lemma In_expr {M : Model} (P : ℝ) :
    M.rhs3 M.value P .inspect = M.I + M.β * M.value M.π + M.β * P * (M.value 1 - M.value M.π) := by
  simp only [Model.rhs3]; ring

lemma Pr_lt_In_le_pi {M : Model} (h : Good M) {P : ℝ} (hP0 : 0 ≤ P) (hPπ : P ≤ M.π) :
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

lemma a_lt_b {M : Model} (h : Good M) (hπ : M.π < 1) : M.value M.π < M.value 1 := by
  obtain ⟨hq, hD, hDe, _, _⟩ := D_facts h
  have hfix := value_fixed h one_mem'
  simp only [Model.rhs3, T_one] at hfix
  have hbb := b_bound h
  have hab := a_le_b h
  have hC := h.hC0; have hCI := h.hCI; have hIR := h.hIR; have hβ0 := h.hβ0; have hβ1 := h.hβ1
  have hWπ := value_le_W h (π_mem h)
  unfold Wf at hWπ
  rcases min3_choice (M.C * 1 + M.β * M.value 1) (M.I + M.β * 1 * M.value 1 + M.β * (1 - 1) * M.value M.π)
      (M.R + M.β * M.value M.π) with e | e | e
  · -- b = C + β b
    have hb : M.value 1 = M.C / (1 - M.β) := by
      have hne : (1 - M.β) ≠ 0 := by linarith
      field_simp; nlinarith [hfix, e]
    have : 0 < Dc M * (1 - M.π) := mul_pos hD (by linarith)
    linarith
  · nlinarith
  · nlinarith

lemma L0 {M : Model} (h : Good M) (hb : M.value 1 < M.R + M.β * M.value M.π) :
    ∀ P ∈ Set.Icc (0:ℝ) 1, M.rhs3 M.value P .produce < M.rhs3 M.value P .inspect := by
  obtain ⟨hq, hD, hDe, _, _⟩ := D_facts h
  have hfix := value_fixed h one_mem'
  simp only [Model.rhs3, T_one] at hfix
  have hbb := b_bound h
  have hC := h.hC0; have hCI := h.hCI; have hIR := h.hIR; have hβ0 := h.hβ0; have hβ1 := h.hβ1
  have hWπ := value_le_W h (π_mem h)
  unfold Wf at hWπ
  have hbe : M.value 1 = M.C / (1 - M.β) := by
    rcases min3_choice (M.C * 1 + M.β * M.value 1) (M.I + M.β * 1 * M.value 1 + M.β * (1 - 1) * M.value M.π)
      (M.R + M.β * M.value M.π) with e | e | e
    · have hne : (1 - M.β) ≠ 0 := by linarith
      field_simp; nlinarith [hfix, e]
    · exfalso; nlinarith
    · exfalso; linarith
  rw [← hbe] at hWπ
  intro P hP
  have h1 := Pr_bound h hP
  rw [In_expr]
  obtain ⟨hP0, hP1⟩ := hP
  have hd : Dc M * (1 - M.π) ≤ M.value 1 - M.value M.π := by linarith
  have h5 := mul_le_mul_of_nonneg_left hd (mul_nonneg hβ0.le hP0)
  nlinarith [mul_nonneg hP0 hC.le, mul_nonneg (sub_nonneg.2 hP1) hC.le]


lemma Pr_mono {M : Model} (h : Good M) {x y : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (hxy : x ≤ y) :
    M.rhs3 M.value x .produce ≤ M.rhs3 M.value y .produce := by
  obtain ⟨hTx, _⟩ := T_mem h hx
  obtain ⟨hTy, _⟩ := T_mem h hy
  have := value_mono h hTx hTy (T_mono h hxy)
  have := mul_le_mul_of_nonneg_left this h.hβ0.le
  simp only [Model.rhs3]
  nlinarith [h.hC0]

lemma Pr_cont {M : Model} (h : Good M) :
    ContinuousOn (fun P => M.rhs3 M.value P .produce) (Set.Icc (0:ℝ) 1) := by
  have hT : ContinuousOn M.T (Set.Icc (0:ℝ) 1) := by
    unfold Model.T; fun_prop
  have hmap : Set.MapsTo M.T (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := fun P hP => (T_mem h hP).1
  simp only [Model.rhs3]
  exact (continuousOn_const.mul continuousOn_id).add (continuousOn_const.mul ((value_cont h).comp hT hmap))

lemma two_region_of {M : Model} (h : Good M)
    (hins : ∀ P ∈ Set.Icc (0:ℝ) 1, M.rhs3 M.value P .produce ≤ M.rhs3 M.value P .inspect ∨
      M.rhs3 M.value P .revise ≤ M.rhs3 M.value P .inspect) :
    ∃ P₁ : ℝ, M.π ≤ P₁ ∧ ∀ P ∈ Set.Icc (0:ℝ) 1, M.rhs3 M.value P (M.twoRegion P₁ P) = M.value P := by
  have hlt := a_lt_r h
  have hrev : ∀ P, M.rhs3 M.value P .revise = M.R + M.β * M.value M.π := fun P => rfl
  -- produce optimal when Pr < r
  have hprod : ∀ P ∈ Set.Icc (0:ℝ) 1, M.rhs3 M.value P .produce < M.rhs3 M.value P .revise →
      M.rhs3 M.value P .produce = M.value P := by
    intro P hP hlt'
    refine opt_produce h hP ?_ hlt'.le
    rcases hins P hP with h1 | h1
    · exact h1
    · exact hlt'.le.trans h1
  by_cases hS : ({P : ℝ | P ∈ Set.Icc (0:ℝ) 1 ∧ M.R + M.β * M.value M.π ≤ M.rhs3 M.value P .produce}).Nonempty
  · set S := {P : ℝ | P ∈ Set.Icc (0:ℝ) 1 ∧ M.R + M.β * M.value M.π ≤ M.rhs3 M.value P .produce} with hSdef
    have hclosed : IsClosed S := by
      have := (Pr_cont h).preimage_isClosed_of_isClosed isClosed_Icc
        (isClosed_Ici (a := M.R + M.β * M.value M.π))
      have e : S = Set.Icc (0:ℝ) 1 ∩ (fun P => M.rhs3 M.value P .produce) ⁻¹' Set.Ici (M.R + M.β * M.value M.π) :=
        Set.ext (fun P => Iff.rfl)
      rw [e]; exact this
    have hbdd : BddBelow S := ⟨0, fun P hP => hP.1.1⟩
    have hP1S : sInf S ∈ S := hclosed.csInf_mem hS hbdd
    have hP1I := hP1S.1
    refine ⟨sInf S, ?_, ?_⟩
    · by_contra hcon
      push_neg at hcon
      have hP1 := hP1S.2
      have hr : M.R + M.β * M.value M.π ≤ M.rhs3 M.value (sInf S) .inspect := by
        rcases hins _ hP1I with h1 | h1
        · exact hP1.trans h1
        · exact h1
      have hopt := opt_revise h hP1I hP1 hr
      have hm := value_mono h hP1I (π_mem h) hcon.le
      rw [← hopt] at hm
      simp only [Model.rhs3] at hm
      linarith
    · intro P hP
      unfold Model.twoRegion
      split_ifs with hlt2
      · have hnot : P ∉ S := fun hPS => absurd (csInf_le hbdd hPS) (not_le.2 hlt2)
        have : M.rhs3 M.value P .produce < M.rhs3 M.value P .revise := by
          rw [hrev]; by_contra hc; exact hnot ⟨hP, not_lt.1 hc⟩
        exact hprod P hP this
      · push_neg at hlt2
        have hP1 := hP1S.2
        have hm := Pr_mono h hP1I hP hlt2
        have h1 : M.rhs3 M.value P .revise ≤ M.rhs3 M.value P .produce := hP1.trans hm
        refine opt_revise h hP h1 ?_
        rcases hins P hP with h2 | h2
        · exact h1.trans h2
        · exact h2
  · refine ⟨2, by linarith [h.hπ1], ?_⟩
    intro P hP
    unfold Model.twoRegion
    have hP2 : P < 2 := by linarith [hP.2]
    rw [if_pos hP2]
    apply hprod P hP
    rw [hrev]
    by_contra hc
    exact hS ⟨P, hP, not_lt.1 hc⟩

lemma part_b1 {M : Model} (h : Good M)
    (hb : M.I + M.β * (M.value 1 - M.value M.π) ≥ M.C / (1 - M.β * (1 - M.π))) :
    ∃ P₁ : ℝ, M.π ≤ P₁ ∧ ∀ P ∈ Set.Icc (0:ℝ) 1, M.rhs3 M.value P (M.twoRegion P₁ P) = M.value P := by
  apply two_region_of h
  intro P hP
  left
  have h1 := Pr_bound h hP
  rw [In_expr]
  have hD : Dc M = M.C / (1 - M.β * (1 - M.π)) := rfl
  rw [← hD] at hb
  obtain ⟨hP0, hP1⟩ := hP
  have hI := h.hIR; have hC := h.hC0; have hCI := h.hCI
  nlinarith [mul_nonneg hP0 (sub_nonneg.2 hb), mul_nonneg (sub_nonneg.2 hP1) (by linarith : (0:ℝ) ≤ M.I)]

lemma part_b2 {M : Model} (h : Good M)
    (hb : (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) ≤
        (M.R / M.C) * (1 - M.β * (1 - M.π))) :
    ∃ P₁ : ℝ, M.π ≤ P₁ ∧ ∀ P ∈ Set.Icc (0:ℝ) 1, M.rhs3 M.value P (M.twoRegion P₁ P) = M.value P := by
  obtain ⟨hq, hD, hDe, _, _⟩ := D_facts h
  apply two_region_of h
  intro P hP
  have h1 := Pr_bound h hP
  rw [In_expr]
  simp only [Model.rhs3] at h1 ⊢
  by_cases hπ : M.π < 1
  · have hab := a_lt_b h hπ
    set w := M.β * (M.value 1 - M.value M.π) with hw
    have hwpos : 0 < w := mul_pos h.hβ0 (sub_pos.2 hab)
    have hRI := h.hIR
    by_cases hPs : P ≤ (M.R - M.I) / w
    · left
      have hRD : (M.R - M.I) / w * Dc M ≤ M.R := by
        have : (M.R / M.C) * (1 - M.β * (1 - M.π)) = M.R / Dc M := by
          unfold Dc; field_simp
        rw [this, le_div_iff₀ hD] at hb
        exact hb
      have e1 : (M.R - M.I) / w * w = M.R - M.I := div_mul_cancel₀ _ hwpos.ne'
      have hPs' : P * w ≤ M.R - M.I := by
        have := mul_le_mul_of_nonneg_right hPs hwpos.le
        linarith
      have hP0 := hP.1
      have key : (Dc M - w) * P ≤ M.I := by
        by_cases hdw : Dc M ≤ w
        · nlinarith [mul_nonneg hP0 (sub_nonneg.2 hdw), h.hC0, h.hCI]
        · push_neg at hdw
          have := mul_le_mul_of_nonneg_left hPs (sub_pos.2 hdw).le
          nlinarith
      have : M.β * P * (M.value 1 - M.value M.π) = w * P := by rw [hw]; ring
      linarith
    · right
      push_neg at hPs
      have e1 : (M.R - M.I) / w * w = M.R - M.I := div_mul_cancel₀ _ hwpos.ne'
      have := mul_lt_mul_of_pos_right hPs hwpos
      have : M.β * P * (M.value 1 - M.value M.π) = w * P := by rw [hw]; ring
      nlinarith
  · left
    have hπ1 : M.π = 1 := le_antisymm h.hπ1 (not_lt.1 hπ)
    have hab : M.value M.π = M.value 1 := by rw [hπ1]
    have hD1 : Dc M = M.C := by unfold Dc; rw [hπ1]; field_simp; ring
    obtain ⟨hP0, hP1⟩ := hP
    have := h.hCI
    rw [hab] at h1 ⊢
    rw [hD1] at h1
    nlinarith [h.hC0]


lemma In_cont {M : Model} :
    Continuous (fun P => M.rhs3 M.value P .inspect) := by
  simp only [Model.rhs3]; fun_prop

lemma g_concave {M : Model} (h : Good M) {x y t : ℝ} (hx : x ∈ Set.Icc (0:ℝ) 1)
    (hy : y ∈ Set.Icc (0:ℝ) 1) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (1 - t) * (M.rhs3 M.value x .produce - M.rhs3 M.value x .inspect) +
      t * (M.rhs3 M.value y .produce - M.rhs3 M.value y .inspect) ≤
    M.rhs3 M.value ((1 - t) * x + t * y) .produce - M.rhs3 M.value ((1 - t) * x + t * y) .inspect := by
  obtain ⟨hTx, _⟩ := T_mem h hx
  obtain ⟨hTy, _⟩ := T_mem h hy
  have key := value_conc h _ hTx _ hTy t ht
  have hT : M.T ((1 - t) * x + t * y) = (1 - t) * M.T x + t * M.T y := by
    unfold Model.T; ring
  have := mul_le_mul_of_nonneg_left key h.hβ0.le
  simp only [Model.rhs3]
  rw [hT]
  nlinarith

lemma F1 {M : Model} (h : Good M) {P : ℝ} (hP : P ∈ Set.Icc (0:ℝ) 1)
    (hpr : M.rhs3 M.value P .produce = M.value P) (hlt : M.value P < M.R + M.β * M.value M.π) :
    M.C * P < (1 - M.β) * (M.R + M.β * M.value M.π) := by
  obtain ⟨hT, hPT⟩ := T_mem h hP
  have h1 := value_mono h hP hT hPT
  have h2 := mul_le_mul_of_nonneg_left h1 h.hβ0.le
  simp only [Model.rhs3] at hpr
  have := h.hβ1
  nlinarith

lemma part_a {M : Model} (h : Good M)
    (hHa : (1 - M.β) * (M.R + M.β * M.value M.π) / M.C ≤
        (M.R - M.I) / (M.β * (M.value 1 - M.value M.π))) :
    ∃ P₁ P₂ : ℝ, M.π ≤ P₁ ∧ P₁ ≤ P₂ ∧
        ((∃ P ∈ Set.Icc (0 : ℝ) 1,
            M.rhs3 M.value P .revise = M.value P) → P₂ ≤ 1) ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.threeRegion P₁ P₂ P) = M.value P := by
  have hβ0 := h.hβ0; have hβ1 := h.hβ1; have hC := h.hC0; have hCI := h.hCI; have hIR := h.hIR
  have hRpos : 0 < M.R := by linarith
  have ha0 : 0 ≤ M.value M.π := (value_bounds h (π_mem h)).1
  have hrpos : 0 < M.R + M.β * M.value M.π := by nlinarith
  have hLpos : 0 < (1 - M.β) * (M.R + M.β * M.value M.π) / M.C :=
    div_pos (mul_pos (by linarith) hrpos) hC
  have hab : M.value M.π < M.value 1 := by
    rcases (a_le_b h).lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have hz : (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) = 0 := by rw [h1]; simp
      linarith
  set w := M.β * (M.value 1 - M.value M.π) with hw
  have hwpos : 0 < w := mul_pos hβ0 (sub_pos.2 hab)
  set r := M.R + M.β * M.value M.π with hr
  set Ps := (M.R - M.I) / w with hPs
  have hws : w * Ps = M.R - M.I := mul_div_cancel₀ _ hwpos.ne'
  have hrev : ∀ P, M.rhs3 M.value P .revise = r := fun P => rfl
  have hIn_le : ∀ P, M.rhs3 M.value P .inspect ≤ r ↔ P ≤ Ps := by
    intro P
    rw [In_expr]
    have e : M.β * P * (M.value 1 - M.value M.π) = w * P := by rw [hw]; ring
    rw [e, hPs, le_div_iff₀ hwpos]
    constructor <;> intro hh <;> nlinarith [hh, hr]
  have hIn_ge : ∀ P, r ≤ M.rhs3 M.value P .inspect ↔ Ps ≤ P := by
    intro P
    rw [In_expr]
    have e : M.β * P * (M.value 1 - M.value M.π) = w * P := by rw [hw]; ring
    rw [e, hPs, div_le_iff₀ hwpos]
    constructor <;> intro hh <;> nlinarith [hh, hr]
  have hrevP : ∀ P ∈ Set.Icc (0:ℝ) 1, M.rhs3 M.value P .revise = M.value P → Ps ≤ P := by
    intro P hP hopt
    have h1 : M.value P ≤ M.rhs3 M.value P .inspect := by
      rw [value_fixed h hP]; exact (min_le_right _ _).trans (min_le_left _ _)
    rw [← hopt] at h1
    exact (hIn_ge P).1 h1
  have hIn_eq : M.rhs3 M.value Ps .inspect = r := le_antisymm ((hIn_le Ps).2 le_rfl) ((hIn_ge Ps).2 le_rfl)
  have hPsle : Ps ≤ 1 → ∀ P ∈ Set.Icc (0:ℝ) 1, Ps ≤ P → r ≤ M.rhs3 M.value P .produce := by
    intro _ P hP hPP
    by_contra hcon
    push_neg at hcon
    have hInr := (hIn_ge P).2 hPP
    have hopt := opt_produce h hP (hcon.le.trans hInr) hcon.le
    have hlt : M.value P < r := by rw [← hopt]; exact hcon
    have := F1 h hP hopt hlt
    have h2 : P < (1 - M.β) * r / M.C := by rw [lt_div_iff₀ hC]; linarith
    linarith
  refine ?_
  by_cases hPs1 : Ps ≤ 1
  · -- main case
    have hgPs : M.rhs3 M.value Ps .inspect ≤ M.rhs3 M.value Ps .produce := by
      have hPsI : Ps ∈ Set.Icc (0:ℝ) 1 := ⟨hPs ▸ (div_nonneg (by linarith) hwpos.le), hPs1⟩
      rw [hIn_eq]; exact hPsle hPs1 Ps hPsI le_rfl
    have hPs0 : 0 ≤ Ps := div_nonneg (by linarith) hwpos.le
    set K : Set ℝ := {P : ℝ | P ∈ Set.Icc (0:ℝ) Ps ∧ M.rhs3 M.value P .inspect ≤ M.rhs3 M.value P .produce}
      with hK
    have hKne : K.Nonempty := ⟨Ps, ⟨hPs0, le_rfl⟩, hgPs⟩
    have hKbdd : BddBelow K := ⟨0, fun P hP => hP.1.1⟩
    have hKclosed : IsClosed K := by
      have hc : ContinuousOn (fun P => M.rhs3 M.value P .produce - M.rhs3 M.value P .inspect)
          (Set.Icc (0:ℝ) Ps) :=
        ((Pr_cont h).mono (Set.Icc_subset_Icc le_rfl hPs1)).sub In_cont.continuousOn
      have := hc.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_Ici (a := (0:ℝ)))
      have e : K = Set.Icc (0:ℝ) Ps ∩ (fun P => M.rhs3 M.value P .produce - M.rhs3 M.value P .inspect) ⁻¹' Set.Ici 0 := by
        ext P
        simp only [hK, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
      rw [e]; exact this
    have hP1K : sInf K ∈ K := hKclosed.csInf_mem hKne hKbdd
    have hP1le : sInf K ≤ Ps := csInf_le hKbdd ⟨⟨hPs0, le_rfl⟩, hgPs⟩
    have hP1ge : M.π ≤ sInf K := by
      refine le_csInf hKne (fun k hk => ?_)
      by_contra hcon
      push_neg at hcon
      have := Pr_lt_In_le_pi h hk.1.1 hcon.le
      linarith [hk.2]
    refine ⟨sInf K, Ps, hP1ge, hP1le, ?_, ?_⟩
    · intro _; exact hPs1
    · intro P hP
      unfold Model.threeRegion
      split_ifs with h1 h2
      · -- produce
        have hnotK : P ∉ K := fun hPK => absurd (csInf_le hKbdd hPK) (not_le.2 h1)
        have hPIcc : P ∈ Set.Icc (0:ℝ) Ps := ⟨hP.1, (h1.le.trans hP1le)⟩
        have hlt : M.rhs3 M.value P .produce < M.rhs3 M.value P .inspect := by
          by_contra hc
          exact hnotK ⟨hPIcc, not_lt.1 hc⟩
        have hInr := (hIn_le P).2 hPIcc.2
        exact opt_produce h hP hlt.le (by rw [hrev]; linarith)
      · -- inspect
        push_neg at h1
        have hPIcc : P ∈ Set.Icc (0:ℝ) Ps := ⟨hP.1, h2.le⟩
        have hInr := (hIn_le P).2 hPIcc.2
        have hKP := hP1K
        have hP1I : sInf K ∈ Set.Icc (0:ℝ) 1 := ⟨hKP.1.1, hKP.1.2.trans hPs1⟩
        have hPsI : Ps ∈ Set.Icc (0:ℝ) 1 := ⟨hPs0, hPs1⟩
        have hpos : 0 < Ps - sInf K := by linarith
        set t := (P - sInf K) / (Ps - sInf K) with ht
        have ht0 : 0 ≤ t := div_nonneg (by linarith) hpos.le
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith
        have hz : (1 - t) * sInf K + t * Ps = P := by
          rw [ht]; field_simp; ring
        have hgc := g_concave h hP1I hPsI ⟨ht0, ht1⟩
        rw [hz] at hgc
        have g1 : 0 ≤ M.rhs3 M.value (sInf K) .produce - M.rhs3 M.value (sInf K) .inspect := by
          linarith [hKP.2]
        have g2 : 0 ≤ M.rhs3 M.value Ps .produce - M.rhs3 M.value Ps .inspect := by
          linarith
        have := mul_nonneg (sub_nonneg.2 ht1) g1
        have := mul_nonneg ht0 g2
        exact opt_inspect h hP (by nlinarith) (by rw [hrev]; exact hInr)
      · -- revise
        push_neg at h2
        exact opt_revise h hP (hPsle hPs1 P hP h2) ((hIn_ge P).2 h2)
  · -- Ps > 1
    push_neg at hPs1
    have hPs0 : 0 ≤ Ps := by linarith
    have hIn1 := (hIn_le 1).2 hPs1.le
    have hbr : M.value 1 < r := by
      have := b_bound h
      rw [In_expr] at hIn1
      nlinarith
    have hL0 := L0 h hbr
    refine ⟨Ps, Ps, by linarith [h.hπ1], le_rfl, ?_, ?_⟩
    · rintro ⟨P, hP, hopt⟩
      exact (hrevP P hP hopt).trans hP.2
    · intro P hP
      unfold Model.threeRegion
      have hlt : P < Ps := by linarith [hP.2]
      rw [if_pos hlt]
      have hInr := (hIn_le P).2 hlt.le
      exact opt_produce h hP (hL0 P hP).le (by rw [hrev]; linarith [hL0 P hP])


theorem theorem_3_7_core (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ((1 - M.β) * (M.R + M.β * M.value M.π) / M.C ≤
        (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) →
      ∃ P₁ P₂ : ℝ, M.π ≤ P₁ ∧ P₁ ≤ P₂ ∧
        ((∃ P ∈ Set.Icc (0 : ℝ) 1,
            M.rhs3 M.value P .revise = M.value P) → P₂ ≤ 1) ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.threeRegion P₁ P₂ P) = M.value P) ∧
    ((M.I + M.β * (M.value 1 - M.value M.π) ≥
        M.C / (1 - M.β * (1 - M.π)) ∨
      (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) ≤
        (M.R / M.C) * (1 - M.β * (1 - M.π))) →
      ∃ P₁ : ℝ, M.π ≤ P₁ ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.twoRegion P₁ P) = M.value P) := by
  have h : Good M := ⟨hβ0, hβ1, hπ0, hπ1, hC0, hCI, hIR⟩
  refine ⟨fun hHa => part_a h hHa, fun hb => ?_⟩
  rcases hb with hb | hb
  · exact part_b1 h hb
  · exact part_b2 h hb

end RossQC.Sufficient

open RossQC.Sufficient


theorem solution (M : Model)
    (hβ0 : 0 < M.β) (hβ1 : M.β < 1)
    (hπ0 : 0 ≤ M.π) (hπ1 : M.π ≤ 1)
    (hC0 : 0 < M.C) (hCI : M.C < M.I) (hIR : M.I < M.R) :
    ((1 - M.β) * (M.R + M.β * M.value M.π) / M.C ≤
        (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) →
      ∃ P₁ P₂ : ℝ, M.π ≤ P₁ ∧ P₁ ≤ P₂ ∧
        ((∃ P ∈ Set.Icc (0 : ℝ) 1,
            M.rhs3 M.value P .revise = M.value P) → P₂ ≤ 1) ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.threeRegion P₁ P₂ P) = M.value P) ∧
    ((M.I + M.β * (M.value 1 - M.value M.π) ≥
        M.C / (1 - M.β * (1 - M.π)) ∨
      (M.R - M.I) / (M.β * (M.value 1 - M.value M.π)) ≤
        (M.R / M.C) * (1 - M.β * (1 - M.π))) →
      ∃ P₁ : ℝ, M.π ≤ P₁ ∧
        ∀ P ∈ Set.Icc (0 : ℝ) 1,
          M.rhs3 M.value P (M.twoRegion P₁ P) = M.value P) := by
  exact theorem_3_7_core M hβ0 hβ1 hπ0 hπ1 hC0 hCI hIR
