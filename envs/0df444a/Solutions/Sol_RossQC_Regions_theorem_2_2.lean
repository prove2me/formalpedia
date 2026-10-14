-- Prove2me | solution 1 for RossQC.Regions.theorem_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T00:58:04.056914+00:00
-- url     : https://prove2.me/submissions/67de71e5-8846-4c20-b7f2-84c947cb1d51

import Mathlib
import Definitions.Def_RossQC_Regions_Model



namespace RossQC.Regions

open Filter Topology

section General

variable {ι : Type*} [Countable ι] (M : Model ι)

lemma sum_mul_summable {P : ι → ℝ} (hP : P ∈ M.simplex) {f : ι → ℝ} {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) : Summable (fun i => P i * f i) := by
  refine Summable.of_norm_bounded (hP.2.summable.mul_right B) ?_
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hP.1 i)]
  exact mul_le_mul_of_nonneg_left (hf i) (hP.1 i)

lemma abs_sum_mul_le {P : ι → ℝ} (hP : P ∈ M.simplex) {f : ι → ℝ} {B : ℝ}
    (hf : ∀ i, |f i| ≤ B) : |∑' i, P i * f i| ≤ B := by
  have hs := sum_mul_summable M hP hf
  have hf' : ∀ i, |(-f) i| ≤ B := fun i => by simpa using hf i
  have hs' := sum_mul_summable M hP hf'
  rw [abs_le]
  constructor
  · have h1 : ∑' i, P i * (-B) ≤ ∑' i, P i * f i :=
      Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (neg_le_of_abs_le (hf i)) (hP.1 i))
        (hP.2.summable.mul_right (-B)) hs
    rw [tsum_mul_right, hP.2.tsum_eq] at h1
    linarith
  · have h1 : ∑' i, P i * f i ≤ ∑' i, P i * B :=
      Summable.tsum_le_tsum (fun i => mul_le_mul_of_nonneg_left (le_of_abs_le (hf i)) (hP.1 i))
        hs (hP.2.summable.mul_right B)
    rw [tsum_mul_right, hP.2.tsum_eq] at h1
    linarith

variable {M}

lemma Pm_le_one (hM : M.Valid) (i j : ι) : M.Pm i j ≤ 1 :=
  le_hasSum (hM.Pm_row i) j (fun k _ => hM.Pm_nonneg i k)

lemma e_mem (hM : M.Valid) (i : ι) : M.e i ∈ M.simplex :=
  ⟨hM.Pm_nonneg i, hM.Pm_row i⟩

lemma T_summable (hM : M.Valid) {P : ι → ℝ} (hP : P ∈ M.simplex) (i : ι) :
    Summable (fun j => P j * M.Pm j i) := by
  refine sum_mul_summable M hP (B := 1) (fun j => ?_)
  rw [abs_of_nonneg (hM.Pm_nonneg j i)]
  exact Pm_le_one hM j i

lemma T_mem (hM : M.Valid) {P : ι → ℝ} (hP : P ∈ M.simplex) : M.T P ∈ M.simplex := by
  refine ⟨fun i => tsum_nonneg (fun j => mul_nonneg (hP.1 j) (hM.Pm_nonneg j i)), ?_⟩
  have hsum : Summable (fun p : ι × ι => P p.1 * M.Pm p.1 p.2) := by
    rw [summable_prod_of_nonneg (fun p => mul_nonneg (hP.1 p.1) (hM.Pm_nonneg p.1 p.2))]
    refine ⟨fun j => (hM.Pm_row j).summable.mul_left (P j), ?_⟩
    have : ∀ j, ∑' i, P j * M.Pm j i = P j := fun j => by
      rw [tsum_mul_left, (hM.Pm_row j).tsum_eq, mul_one]
    simpa [this] using hP.2.summable
  have hsum' : Summable (fun p : ι × ι => P p.2 * M.Pm p.2 p.1) :=
    (Equiv.prodComm ι ι).summable_iff.2 hsum
  have h1 : Summable (fun i => ∑' j, P j * M.Pm j i) := by
    have := (summable_prod_of_nonneg (f := fun p : ι × ι => P p.2 * M.Pm p.2 p.1)
      (fun p => mul_nonneg (hP.1 p.2) (hM.Pm_nonneg p.2 p.1))).1 hsum'
    exact this.2
  refine (h1.hasSum_iff).2 ?_
  have h2 : ∑' i, ∑' j, P j * M.Pm j i = ∑' j, ∑' i, P j * M.Pm j i :=
    Summable.tsum_comm' (f := fun j i => P j * M.Pm j i) hsum (fun j => (hM.Pm_row j).summable.mul_left (P j)) (fun i => T_summable hM hP i)
  show ∑' i, ∑' j, P j * M.Pm j i = 1
  rw [h2]
  have : ∀ j, ∑' i, P j * M.Pm j i = P j := fun j => by
    rw [tsum_mul_left, (hM.Pm_row j).tsum_eq, mul_one]
  simp only [this]
  exact hP.2.tsum_eq

lemma mix_mem {x y : ι → ℝ} (hx : x ∈ M.simplex) (hy : y ∈ M.simplex) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : a • x + b • y ∈ M.simplex := by
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · have := (hx.2.mul_left a).add (hy.2.mul_left b)
    rw [mul_one, mul_one, hab] at this
    exact this

lemma simplex_convex : Convex ℝ M.simplex := by
  intro x hx y hy a b ha hb hab
  exact mix_mem hx hy ha hb hab

/-- bounded on the simplex -/
lemma sum_mix {x y : ι → ℝ} (hx : x ∈ M.simplex) (hy : y ∈ M.simplex) {a b : ℝ}
    {f : ι → ℝ} {B : ℝ} (hf : ∀ i, |f i| ≤ B) :
    ∑' i, (a • x + b • y) i * f i = a * ∑' i, x i * f i + b * ∑' i, y i * f i := by
  have h1 := sum_mul_summable M hx hf
  have h2 := sum_mul_summable M hy hf
  have : ∀ i, (a • x + b • y) i * f i = a * (x i * f i) + b * (y i * f i) := fun i => by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [this]
  rw [Summable.tsum_add (h1.mul_left a) (h2.mul_left b), tsum_mul_left, tsum_mul_left]

lemma T_mix (hM : M.Valid) {x y : ι → ℝ} (hx : x ∈ M.simplex) (hy : y ∈ M.simplex) {a b : ℝ} :
    M.T (a • x + b • y) = a • M.T x + b • M.T y := by
  funext i
  simp only [Model.T, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine sum_mix hx hy (f := fun j => M.Pm j i) (B := 1) (fun j => ?_)
  rw [abs_of_nonneg (hM.Pm_nonneg j i)]
  exact Pm_le_one hM j i


lemma rhs_diff (hM : M.Valid) {V W : (ι → ℝ) → ℝ} {BV BW d : ℝ}
    (hV : ∀ P ∈ M.simplex, |V P| ≤ BV) (hW : ∀ P ∈ M.simplex, |W P| ≤ BW)
    (hd : ∀ P ∈ M.simplex, |V P - W P| ≤ d) {P : ι → ℝ} (hP : P ∈ M.simplex) (a : Action) :
    |M.rhs V P a - M.rhs W P a| ≤ M.β * d := by
  have hβ := hM.β_pos
  cases a with
  | produce =>
    have : M.rhs V P .produce - M.rhs W P .produce = M.β * (V (M.T P) - W (M.T P)) := by
      simp only [Model.rhs]; ring
    rw [this, abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hd _ (T_mem hM hP)) hβ.le
  | inspect =>
    have h1 := sum_mul_summable M hP (f := fun i => V (M.e i)) (B := BV) (fun i => hV _ (e_mem hM i))
    have h2 := sum_mul_summable M hP (f := fun i => W (M.e i)) (B := BW) (fun i => hW _ (e_mem hM i))
    have : M.rhs V P .inspect - M.rhs W P .inspect =
        M.β * ∑' i, P i * (V (M.e i) - W (M.e i)) := by
      simp only [Model.rhs]
      have : ∀ i, P i * (V (M.e i) - W (M.e i)) = P i * V (M.e i) - P i * W (M.e i) :=
        fun i => by ring
      simp only [this]
      rw [Summable.tsum_sub h1 h2]; ring
    rw [this, abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (abs_sum_mul_le M hP (fun i => hd _ (e_mem hM i))) hβ.le
  | revise =>
    have : M.rhs V P .revise - M.rhs W P .revise = M.β * (V (M.e M.i₀) - W (M.e M.i₀)) := by
      simp only [Model.rhs]; ring
    rw [this, abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hd _ (e_mem hM _)) hβ.le

lemma bellman_diff (hM : M.Valid) {V W : (ι → ℝ) → ℝ} {BV BW d : ℝ}
    (hV : ∀ P ∈ M.simplex, |V P| ≤ BV) (hW : ∀ P ∈ M.simplex, |W P| ≤ BW)
    (hd : ∀ P ∈ M.simplex, |V P - W P| ≤ d) {P : ι → ℝ} (hP : P ∈ M.simplex) :
    |M.bellman V P - M.bellman W P| ≤ M.β * d := by
  have k := fun a => rhs_diff hM hV hW hd hP a
  unfold Model.bellman
  refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le (k _) ?_)
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le (k _) (k _))

lemma rhs_abs_le (hM : M.Valid) {Bc : ℝ} (hBc : ∀ i, |M.C i| ≤ Bc ∧ |M.I i| ≤ Bc ∧ |M.R i| ≤ Bc)
    {V : (ι → ℝ) → ℝ} {B : ℝ} (hV : ∀ P ∈ M.simplex, |V P| ≤ B)
    {P : ι → ℝ} (hP : P ∈ M.simplex) (a : Action) : |M.rhs V P a| ≤ Bc + M.β * B := by
  have hβ := hM.β_pos
  cases a with
  | produce =>
    simp only [Model.rhs]
    refine (abs_add_le _ _).trans (add_le_add (abs_sum_mul_le M hP (fun i => (hBc i).1)) ?_)
    rw [abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hV _ (T_mem hM hP)) hβ.le
  | inspect =>
    simp only [Model.rhs]
    refine (abs_add_le _ _).trans (add_le_add (abs_sum_mul_le M hP (fun i => (hBc i).2.1)) ?_)
    rw [abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (abs_sum_mul_le M hP (fun i => hV _ (e_mem hM i))) hβ.le
  | revise =>
    simp only [Model.rhs]
    refine (abs_add_le _ _).trans (add_le_add (abs_sum_mul_le M hP (fun i => (hBc i).2.2)) ?_)
    rw [abs_mul, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hV _ (e_mem hM _)) hβ.le

lemma bellman_abs_le (hM : M.Valid) {Bc : ℝ} (hBc : ∀ i, |M.C i| ≤ Bc ∧ |M.I i| ≤ Bc ∧ |M.R i| ≤ Bc)
    {V : (ι → ℝ) → ℝ} {B : ℝ} (hV : ∀ P ∈ M.simplex, |V P| ≤ B)
    {P : ι → ℝ} (hP : P ∈ M.simplex) : |M.bellman V P| ≤ Bc + M.β * B := by
  have k := fun a => rhs_abs_le hM hBc hV hP a
  unfold Model.bellman
  refine (abs_min_le_max_abs_abs).trans (max_le (k _) ?_)
  exact (abs_min_le_max_abs_abs).trans (max_le (k _) (k _))


lemma iter_bdd (hM : M.Valid) {Bc : ℝ} (hBc : ∀ i, |M.C i| ≤ Bc ∧ |M.I i| ≤ Bc ∧ |M.R i| ≤ Bc)
    (hB0 : 0 ≤ Bc) (n : ℕ) : ∀ P ∈ M.simplex, |M.valueIter n P| ≤ Bc / (1 - M.β) := by
  have hβ0 := hM.β_pos; have hβ1 := hM.β_lt_one
  have h1 : 0 < 1 - M.β := by linarith
  induction n with
  | zero => intro P _; simp [Model.valueIter]; positivity
  | succ n ih =>
    intro P hP
    have := bellman_abs_le hM hBc ih hP
    show |M.bellman (M.valueIter n) P| ≤ _
    refine this.trans (le_of_eq ?_)
    field_simp; ring

lemma iter_step (hM : M.Valid) {Bc : ℝ} (hBc : ∀ i, |M.C i| ≤ Bc ∧ |M.I i| ≤ Bc ∧ |M.R i| ≤ Bc)
    (hB0 : 0 ≤ Bc) (n : ℕ) :
    ∀ P ∈ M.simplex, |M.valueIter (n+1) P - M.valueIter n P| ≤ M.β ^ n * Bc := by
  induction n with
  | zero =>
    intro P hP
    have := bellman_abs_le hM hBc (V := fun _ => (0:ℝ)) (B := 0) (fun _ _ => by simp) hP
    simpa [Model.valueIter] using this
  | succ n ih =>
    intro P hP
    have := bellman_diff hM (iter_bdd hM hBc hB0 (n+1)) (iter_bdd hM hBc hB0 n) ih hP
    show |M.bellman (M.valueIter (n+1)) P - M.bellman (M.valueIter n) P| ≤ _
    refine this.trans (le_of_eq ?_)
    ring

lemma iter_tendsto_ex (hM : M.Valid) {Bc : ℝ} (hBc : ∀ i, |M.C i| ≤ Bc ∧ |M.I i| ≤ Bc ∧ |M.R i| ≤ Bc)
    (hB0 : 0 ≤ Bc) {P : ι → ℝ} (hP : P ∈ M.simplex) :
    ∃ L : ℝ, Tendsto (fun n => M.valueIter n P) atTop (𝓝 L) := by
  have hu : ∀ n, dist (M.valueIter n P) (M.valueIter (n+1) P) ≤ Bc * M.β ^ n := by
    intro n
    rw [Real.dist_eq, abs_sub_comm, mul_comm]
    exact iter_step hM hBc hB0 n P hP
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric M.β Bc hM.β_lt_one hu)

lemma iter_rate (hM : M.Valid) {Bc : ℝ} (hBc : ∀ i, |M.C i| ≤ Bc ∧ |M.I i| ≤ Bc ∧ |M.R i| ≤ Bc)
    (hB0 : 0 ≤ Bc) {P : ι → ℝ} (hP : P ∈ M.simplex) (n : ℕ) :
    |M.valueIter n P - M.Vβ P| ≤ Bc / (1 - M.β) * M.β ^ n := by
  obtain ⟨L, hL⟩ := iter_tendsto_ex hM hBc hB0 hP
  have hV : M.Vβ P = L := hL.limUnder_eq
  have hu : ∀ n, dist (M.valueIter n P) (M.valueIter (n+1) P) ≤ Bc * M.β ^ n := by
    intro n
    rw [Real.dist_eq, abs_sub_comm, mul_comm]
    exact iter_step hM hBc hB0 n P hP
  have := dist_le_of_le_geometric_of_tendsto M.β Bc hM.β_lt_one hu hL n
  rw [hV, ← Real.dist_eq]
  refine this.trans (le_of_eq ?_)
  ring

lemma zero_of_geom {x c r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (h : ∀ n : ℕ, |x| ≤ c * r ^ n) : x = 0 := by
  have t : Tendsto (fun n : ℕ => c * r ^ n) atTop (𝓝 (c * 0)) :=
    tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1)
  have := ge_of_tendsto' t h
  rw [mul_zero] at this
  exact abs_nonpos_iff.1 this


lemma bdd_data (hM : M.Valid) : ∃ Bc : ℝ, 0 ≤ Bc ∧ ∀ i, |M.C i| ≤ Bc ∧ |M.I i| ≤ Bc ∧ |M.R i| ≤ Bc := by
  obtain ⟨B, hB⟩ := hM.costs_bdd
  exact ⟨B, (abs_nonneg _).trans (hB M.i₀).1, hB⟩

lemma Vβ_tendsto (hM : M.Valid) {P : ι → ℝ} (hP : P ∈ M.simplex) :
    Tendsto (fun n => M.valueIter n P) atTop (𝓝 (M.Vβ P)) := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  obtain ⟨L, hL⟩ := iter_tendsto_ex hM hBc hB0 hP
  have : M.Vβ P = L := hL.limUnder_eq
  rw [this]; exact hL

lemma Vβ_abs_le (hM : M.Valid) {Bc : ℝ} (hBc : ∀ i, |M.C i| ≤ Bc ∧ |M.I i| ≤ Bc ∧ |M.R i| ≤ Bc)
    (hB0 : 0 ≤ Bc) {P : ι → ℝ} (hP : P ∈ M.simplex) : |M.Vβ P| ≤ Bc / (1 - M.β) :=
  le_of_tendsto' (Vβ_tendsto hM hP).abs (fun n => iter_bdd hM hBc hB0 n P hP)

lemma Vβ_fixed (hM : M.Valid) {P : ι → ℝ} (hP : P ∈ M.simplex) : M.Vβ P = M.bellman M.Vβ P := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  have hβ0 := hM.β_pos
  have hbV : ∀ P ∈ M.simplex, |M.Vβ P| ≤ Bc / (1 - M.β) := fun P hP => Vβ_abs_le hM hBc hB0 hP
  have key : ∀ n : ℕ, |M.bellman M.Vβ P - M.Vβ P| ≤ (2 * M.β * (Bc / (1 - M.β))) * M.β ^ n := by
    intro n
    have h1 := bellman_diff hM hbV (iter_bdd hM hBc hB0 n)
      (d := Bc / (1 - M.β) * M.β ^ n)
      (fun Q hQ => by rw [abs_sub_comm]; exact iter_rate hM hBc hB0 hQ n) hP
    have h2 := iter_rate hM hBc hB0 hP (n+1)
    have h3 : M.bellman M.Vβ P - M.Vβ P =
        (M.bellman M.Vβ P - M.bellman (M.valueIter n) P) + (M.valueIter (n+1) P - M.Vβ P) := by
      show _ = _ + (M.bellman (M.valueIter n) P - M.Vβ P)
      ring
    rw [h3]
    refine (abs_add_le _ _).trans ?_
    have : 2 * M.β * (Bc / (1 - M.β)) * M.β ^ n =
        M.β * (Bc / (1 - M.β) * M.β ^ n) + Bc / (1 - M.β) * M.β ^ (n+1) := by ring
    rw [this]
    exact add_le_add h1 h2
  have := zero_of_geom hM.β_pos.le hM.β_lt_one key
  linarith

lemma Vβ_unique (hM : M.Valid) {W : (ι → ℝ) → ℝ} {BW : ℝ} (hW : ∀ P ∈ M.simplex, |W P| ≤ BW)
    (hfix : ∀ P ∈ M.simplex, W P = M.bellman W P) {P : ι → ℝ} (hP : P ∈ M.simplex) :
    W P = M.Vβ P := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  have hbV : ∀ P ∈ M.simplex, |M.Vβ P| ≤ Bc / (1 - M.β) := fun P hP => Vβ_abs_le hM hBc hB0 hP
  have key : ∀ n : ℕ, ∀ Q ∈ M.simplex, |W Q - M.Vβ Q| ≤ M.β ^ n * (BW + Bc / (1 - M.β)) := by
    intro n
    induction n with
    | zero =>
      intro Q hQ
      calc |W Q - M.Vβ Q| ≤ |W Q| + |M.Vβ Q| := abs_sub _ _
        _ ≤ _ := by simp; exact add_le_add (hW Q hQ) (hbV Q hQ)
    | succ n ih =>
      intro Q hQ
      have := bellman_diff hM hW hbV ih hQ
      rw [← hfix Q hQ, ← Vβ_fixed hM hQ] at this
      refine this.trans (le_of_eq ?_)
      ring
  have := zero_of_geom hM.β_pos.le hM.β_lt_one (x := W P - M.Vβ P) (c := BW + Bc / (1 - M.β))
    (fun n => by rw [mul_comm]; exact key n P hP)
  linarith

theorem optimality_equation_core (hM : M.Valid) :
    (∀ P ∈ M.simplex, ∃ L : ℝ, Tendsto (fun n => M.valueIter n P) atTop (𝓝 L)) ∧
    (∃ B : ℝ, ∀ P ∈ M.simplex, |M.Vβ P| ≤ B) ∧
    (∀ P ∈ M.simplex, M.Vβ P = M.bellman M.Vβ P) ∧
    (∀ W : (ι → ℝ) → ℝ, (∃ B : ℝ, ∀ P ∈ M.simplex, |W P| ≤ B) →
      (∀ P ∈ M.simplex, W P = M.bellman W P) → ∀ P ∈ M.simplex, W P = M.Vβ P) := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  refine ⟨fun P hP => iter_tendsto_ex hM hBc hB0 hP, ⟨_, fun P hP => Vβ_abs_le hM hBc hB0 hP⟩,
    fun P hP => Vβ_fixed hM hP, ?_⟩
  rintro W ⟨BW, hW⟩ hfix P hP
  exact Vβ_unique hM hW hfix hP


/-- concavity along convex combinations on the simplex -/
def ConcS (M : Model ι) (V : (ι → ℝ) → ℝ) : Prop :=
  ∀ x ∈ M.simplex, ∀ y ∈ M.simplex, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a * V x + b * V y ≤ V (a • x + b • y)

lemma rhs_inspect_mix (hM : M.Valid) {V : (ι → ℝ) → ℝ} {B : ℝ} (hV : ∀ P ∈ M.simplex, |V P| ≤ B)
    {x y : ι → ℝ} (hx : x ∈ M.simplex) (hy : y ∈ M.simplex) {a b : ℝ} :
    M.rhs V (a • x + b • y) .inspect = a * M.rhs V x .inspect + b * M.rhs V y .inspect := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  simp only [Model.rhs]
  rw [sum_mix hx hy (f := M.I) (B := Bc) (fun i => (hBc i).2.1),
    sum_mix hx hy (f := fun i => V (M.e i)) (B := B) (fun i => hV _ (e_mem hM i))]
  ring

lemma rhs_revise_mix (hM : M.Valid) (V : (ι → ℝ) → ℝ)
    {x y : ι → ℝ} (hx : x ∈ M.simplex) (hy : y ∈ M.simplex) {a b : ℝ} (hab : a + b = 1) :
    M.rhs V (a • x + b • y) .revise = a * M.rhs V x .revise + b * M.rhs V y .revise := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  simp only [Model.rhs]
  rw [sum_mix hx hy (f := M.R) (B := Bc) (fun i => (hBc i).2.2)]
  have : b = 1 - a := by linarith
  subst this
  ring

lemma rhs_produce_conc (hM : M.Valid) {V : (ι → ℝ) → ℝ} {B : ℝ} (hV : ConcS M V)
    {x y : ι → ℝ} (hx : x ∈ M.simplex) (hy : y ∈ M.simplex) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * M.rhs V x .produce + b * M.rhs V y .produce ≤ M.rhs V (a • x + b • y) .produce := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  simp only [Model.rhs]
  rw [sum_mix hx hy (f := M.C) (B := Bc) (fun i => (hBc i).1), T_mix hM hx hy]
  have := hV _ (T_mem hM hx) _ (T_mem hM hy) a b ha hb hab
  have h2 := mul_le_mul_of_nonneg_left this hM.β_pos.le
  nlinarith

lemma ConcS_bellman (hM : M.Valid) {V : (ι → ℝ) → ℝ} {B : ℝ} (hB : ∀ P ∈ M.simplex, |V P| ≤ B)
    (hV : ConcS M V) : ConcS M (M.bellman V) := by
  intro x hx y hy a b ha hb hab
  have hz := mix_mem hx hy ha hb hab
  have p := rhs_produce_conc hM (B := B) hV hx hy ha hb hab
  have i := (rhs_inspect_mix hM hB hx hy (a := a) (b := b)).ge
  have r := (rhs_revise_mix hM V hx hy hab).ge
  unfold Model.bellman
  have mn : ∀ u1 v1 u2 v2 w1 w2 : ℝ, a * u1 + b * u2 ≤ w1 → a * v1 + b * v2 ≤ w2 →
      a * min u1 v1 + b * min u2 v2 ≤ min w1 w2 := by
    intro u1 v1 u2 v2 w1 w2 h1 h2
    refine le_min ?_ ?_
    · nlinarith [min_le_left u1 v1, min_le_left u2 v2]
    · nlinarith [min_le_right u1 v1, min_le_right u2 v2]
  refine mn _ _ _ _ _ _ p (mn _ _ _ _ _ _ i r)

lemma ConcS_iter (hM : M.Valid) (n : ℕ) : ConcS M (M.valueIter n) := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  induction n with
  | zero => intro x _ y _ a b _ _ hab; simp [Model.valueIter]
  | succ n ih => exact ConcS_bellman hM (iter_bdd hM hBc hB0 n) ih

lemma ConcS_Vβ (hM : M.Valid) : ConcS M M.Vβ := by
  intro x hx y hy a b ha hb hab
  have hz := mix_mem hx hy ha hb hab
  have t := ((Vβ_tendsto hM hx).const_mul a).add ((Vβ_tendsto hM hy).const_mul b)
  exact le_of_tendsto_of_tendsto' t (Vβ_tendsto hM hz) (fun n => ConcS_iter hM n x hx y hy a b ha hb hab)

theorem lemma_2_1_core (hM : M.Valid) : ConcaveOn ℝ M.simplex M.Vβ := by
  refine ⟨simplex_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa [smul_eq_mul] using ConcS_Vβ hM x hx y hy a b ha hb hab

lemma region_convex (hM : M.Valid) (act : Action)
    (hmix : ∀ {x y : ι → ℝ}, x ∈ M.simplex → y ∈ M.simplex → ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a + b = 1 →
      M.rhs M.Vβ (a • x + b • y) act = a * M.rhs M.Vβ x act + b * M.rhs M.Vβ y act) :
    Convex ℝ (M.region act) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hxS, hxe⟩ := hx
  obtain ⟨hyS, hye⟩ := hy
  have hz := mix_mem hxS hyS ha hb hab
  refine ⟨hz, ?_⟩
  have hc := ConcS_Vβ hM x hxS y hyS a b ha hb hab
  have hle : M.Vβ (a • x + b • y) ≤ M.rhs M.Vβ (a • x + b • y) act := by
    rw [Vβ_fixed hM hz]
    unfold Model.bellman
    cases act
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hge : M.rhs M.Vβ (a • x + b • y) act ≤ M.Vβ (a • x + b • y) := by
    rw [hmix hxS hyS ha hb hab, ← hxe, ← hye]; exact hc
  exact le_antisymm hle hge

theorem theorem_2_2_core (hM : M.Valid) : Convex ℝ M.inspectRegion ∧ Convex ℝ M.reviseRegion := by
  obtain ⟨Bc, hB0, hBc⟩ := bdd_data hM
  refine ⟨region_convex hM .inspect ?_, region_convex hM .revise ?_⟩
  · intro x y hx hy a b _ _ _
    exact rhs_inspect_mix hM (B := Bc / (1 - M.β)) (fun P hP => Vβ_abs_le hM hBc hB0 hP) hx hy
  · intro x y hx hy a b _ _ hab
    exact rhs_revise_mix hM _ hx hy hab

end General

end RossQC.Regions

open RossQC.Regions
open Filter Topology

theorem solution {ι : Type*} [Countable ι] (M : Model ι) (hM : M.Valid) :
    Convex ℝ M.inspectRegion ∧ Convex ℝ M.reviseRegion := by
  exact theorem_2_2_core hM
