-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P37.theoremC19
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T21:47:37.355141+00:00
-- url     : https://prove2.me/submissions/080ad9be-a232-4d7f-ba6a-38f76328ecac

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

open scoped BigOperators Matrix
open Filter Topology

namespace X7Q10

variable {d : ℕ}

def X7_l1 (y : Fin d → ℝ) : ℝ := ∑ i, |y i|

def X7_Stoch (R : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i j, 0 ≤ R i j) ∧ ∀ j, ∑ i, R i j = 1

lemma X7_stoch_mul {R S : Matrix (Fin d) (Fin d) ℝ} (hR : X7_Stoch R) (hS : X7_Stoch S) :
    X7_Stoch (R * S) := by
  refine ⟨fun i j => ?_, fun j => ?_⟩
  · simp only [Matrix.mul_apply]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hR.1 _ _) (hS.1 _ _)
  · simp only [Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hR.2, one_mul, hS.2]

lemma X7_stoch_pow {R : Matrix (Fin d) (Fin d) ℝ} (hR : X7_Stoch R) (n : ℕ) :
    X7_Stoch (R ^ n) := by
  induction n with
  | zero =>
    refine ⟨fun i j => ?_, fun j => ?_⟩
    · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
    · simp [Matrix.one_apply]
  | succ n ih => rw [pow_succ]; exact X7_stoch_mul ih hR

lemma X7_sum_mulVec {R : Matrix (Fin d) (Fin d) ℝ} (hR : X7_Stoch R) (y : Fin d → ℝ) :
    ∑ i, (R *ᵥ y) i = ∑ j, y j := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hR.2, one_mul]

lemma X7_l1_mulVec {R : Matrix (Fin d) (Fin d) ℝ} (hR : X7_Stoch R) (y : Fin d → ℝ) :
    X7_l1 (R *ᵥ y) ≤ X7_l1 y := by
  unfold X7_l1
  calc ∑ i, |(R *ᵥ y) i| ≤ ∑ i, ∑ j, R i j * |y j| := by
        gcongr with i
        simp only [Matrix.mulVec, dotProduct]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hR.1 i j)]
    _ = ∑ j, |y j| := by
        rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul, hR.2, one_mul]

lemma X7_dobrushin {B : Matrix (Fin d) (Fin d) ℝ} (hB : X7_Stoch B) (δ : ℝ)
    (hδ : ∀ j l, δ ≤ ∑ i, min (B i j) (B i l)) (y : Fin d → ℝ) (hy : ∑ j, y j = 0) :
    X7_l1 (B *ᵥ y) ≤ (1 - δ) * X7_l1 y := by
  set yp : Fin d → ℝ := fun j => max (y j) 0 with hyp_def
  set ym : Fin d → ℝ := fun j => max (-y j) 0 with hym_def
  have hyp : ∀ j, 0 ≤ yp j := fun j => le_max_right _ _
  have hym : ∀ j, 0 ≤ ym j := fun j => le_max_right _ _
  have key : ∀ j, y j = yp j - ym j ∧ |y j| = yp j + ym j := by
    intro j
    rcases le_total 0 (y j) with h | h
    · have h1 : yp j = y j := max_eq_left h
      have h2 : ym j = 0 := max_eq_right (by linarith)
      rw [h1, h2, abs_of_nonneg h]; simp
    · have h1 : yp j = 0 := max_eq_right h
      have h2 : ym j = -y j := max_eq_left (by linarith)
      rw [h1, h2, abs_of_nonpos h]; simp
  set s := ∑ j, yp j with hs_def
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => hyp j
  have hs : ∑ j, ym j = s := by
    have : ∑ j, y j = ∑ j, yp j - ∑ j, ym j := by
      rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun j _ => (key j).1
    linarith
  have hl1 : X7_l1 y = 2 * s := by
    unfold X7_l1
    rw [Finset.sum_congr rfl fun j _ => (key j).2, Finset.sum_add_distrib, hs]; ring
  have hid : ∀ i, s * (B *ᵥ y) i = ∑ j, ∑ l, yp j * ym l * (B i j - B i l) := by
    intro i
    have e1 : (B *ᵥ y) i = ∑ j, B i j * yp j - ∑ l, B i l * ym l := by
      simp only [Matrix.mulVec, dotProduct]; rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [(key j).1]; ring
    have a1 : ∑ j, ∑ l, yp j * ym l * B i j = s * ∑ j, B i j * yp j := by
      rw [← hs, Finset.sum_mul_sum, Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    have a2 : ∑ j, ∑ l, yp j * ym l * B i l = s * ∑ l, B i l * ym l := by
      rw [hs_def, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    have : ∑ j, ∑ l, yp j * ym l * (B i j - B i l) =
        ∑ j, ∑ l, yp j * ym l * B i j - ∑ j, ∑ l, yp j * ym l * B i l := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [this, a1, a2, e1]; ring
  have hcol : ∀ j l, ∑ i, |B i j - B i l| ≤ 2 - 2 * δ := by
    intro j l
    have : ∀ i, |B i j - B i l| = B i j + B i l - 2 * min (B i j) (B i l) := by
      intro i; rcases le_total (B i j) (B i l) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hB.2, hB.2, ← Finset.mul_sum]
    linarith [hδ j l]
  have hmain : s * X7_l1 (B *ᵥ y) ≤ s * ((1 - δ) * X7_l1 y) := by
    calc s * X7_l1 (B *ᵥ y) = ∑ i, |s * (B *ᵥ y) i| := by
            unfold X7_l1; rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [abs_mul, abs_of_nonneg hs0]
      _ = ∑ i, |∑ j, ∑ l, yp j * ym l * (B i j - B i l)| := by simp_rw [hid]
      _ ≤ ∑ i, ∑ j, ∑ l, yp j * ym l * |B i j - B i l| := by
          gcongr with i
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          gcongr with j
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [abs_mul, abs_of_nonneg (mul_nonneg (hyp j) (hym l))]
      _ = ∑ j, ∑ l, yp j * ym l * ∑ i, |B i j - B i l| := by
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun l _ => ?_
          rw [Finset.mul_sum]
      _ ≤ ∑ j, ∑ l, yp j * ym l * (2 - 2 * δ) := by
          gcongr with j _ l _
          exact hcol j l
      _ = s * ((1 - δ) * X7_l1 y) := by
          have : ∀ j, ∑ l, yp j * ym l * (2 - 2 * δ) = yp j * ((2 - 2 * δ) * s) := fun j => by
            rw [← hs, Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun l _ => by ring
          rw [Finset.sum_congr rfl fun j _ => this j, ← Finset.sum_mul, ← hs_def, hl1]; ring
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · have h1 : X7_l1 y = 0 := by rw [hl1, ← h0]; ring
    have := X7_l1_mulVec hB y
    rw [h1] at this ⊢; simpa using this
  · exact le_of_mul_le_mul_left hmain hpos

lemma X7_iter {R : Matrix (Fin d) (Fin d) ℝ} (hR : X7_Stoch R) {k : ℕ} (hk : 0 < k) (c : ℝ)
    (hc0 : 0 ≤ c) (hcon : ∀ y : Fin d → ℝ, ∑ j, y j = 0 → X7_l1 ((R ^ k) *ᵥ y) ≤ c * X7_l1 y) :
    ∀ n (y : Fin d → ℝ), ∑ j, y j = 0 → X7_l1 ((R ^ n) *ᵥ y) ≤ c ^ (n / k) * X7_l1 y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hy
    rcases lt_or_ge n k with h | h
    · rw [Nat.div_eq_of_lt h, pow_zero, one_mul]
      exact X7_l1_mulVec (X7_stoch_pow hR n) y
    · have hn : R ^ n = R ^ k * R ^ (n - k) := by rw [← pow_add]; congr 1; omega
      rw [hn, ← Matrix.mulVec_mulVec, Nat.div_eq_sub_div hk h, pow_succ]
      have hsum : ∑ j, (R ^ (n - k) *ᵥ y) j = 0 := by
        rw [X7_sum_mulVec (X7_stoch_pow hR _), hy]
      calc X7_l1 (R ^ k *ᵥ (R ^ (n - k) *ᵥ y)) ≤ c * X7_l1 (R ^ (n - k) *ᵥ y) := hcon _ hsum
        _ ≤ c * (c ^ ((n - k) / k) * X7_l1 y) := by
            gcongr; exact ih (n - k) (by omega) y hy
        _ = c ^ ((n - k) / k) * c * X7_l1 y := by ring

lemma X7_norm_le_l1 (y : Fin d → ℝ) : ‖y‖ ≤ X7_l1 y := by
  have h0 : 0 ≤ X7_l1 y := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [pi_norm_le_iff_of_nonneg h0]
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun i => |y i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)

/-- Core: a stochastic matrix with a pairwise-overlapping (scrambling) power is mixing. -/
theorem X7_real_mixing (hd : 0 < d) {R : Matrix (Fin d) (Fin d) ℝ} (hR : X7_Stoch R)
    {k : ℕ} (hk : 0 < k) (hscr : ∀ j l, ∃ i, 0 < (R ^ k) i j * (R ^ k) i l) :
    ∃ v : Fin d → ℝ, (∀ i, 0 ≤ v i) ∧ ∑ i, v i = 1 ∧
      ∀ y : Fin d → ℝ, Tendsto (fun n => (R ^ n) *ᵥ y) atTop (𝓝 ((∑ j, y j) • v)) := by
  set B := R ^ k with hB_def
  have hB : X7_Stoch B := X7_stoch_pow hR k
  let f : Fin d × Fin d → ℝ := fun p => ∑ i, min (B i p.1) (B i p.2)
  have hfpos : ∀ p, 0 < f p := by
    intro p
    obtain ⟨i, hi⟩ := hscr p.1 p.2
    have h1 : 0 < B i p.1 := by
      rcases (hB.1 i p.1).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hi; exact absurd hi (lt_irrefl 0)
    have h2 : 0 < B i p.2 := by
      rcases (hB.1 i p.2).lt_or_eq with h | h
      · exact h
      · rw [← h, mul_zero] at hi; exact absurd hi (lt_irrefl 0)
    calc 0 < min (B i p.1) (B i p.2) := lt_min h1 h2
      _ ≤ f p := Finset.single_le_sum (f := fun i => min (B i p.1) (B i p.2))
          (fun i _ => le_min (hB.1 _ _) (hB.1 _ _)) (Finset.mem_univ i)
  have hne : (Finset.univ : Finset (Fin d × Fin d)).Nonempty := ⟨(⟨0, hd⟩, ⟨0, hd⟩), Finset.mem_univ _⟩
  set δ := Finset.univ.inf' hne f with hδ_def
  have hδpos : 0 < δ := (Finset.lt_inf'_iff hne).2 fun p _ => hfpos p
  have hδle : ∀ j l, δ ≤ ∑ i, min (B i j) (B i l) := fun j l =>
    Finset.inf'_le f (Finset.mem_univ (j, l))
  have hδ1 : δ ≤ 1 := by
    have := hδle ⟨0, hd⟩ ⟨0, hd⟩
    simp only [min_self] at this
    rw [hB.2] at this; exact this
  set c := 1 - δ
  have hc0 : 0 ≤ c := by simp only [c]; linarith
  have hc1 : c < 1 := by simp only [c]; linarith
  have hcon : ∀ y : Fin d → ℝ, ∑ j, y j = 0 → X7_l1 ((R ^ k) *ᵥ y) ≤ c * X7_l1 y :=
    fun y hy => X7_dobrushin hB δ hδle y hy
  have hit := X7_iter hR hk c hc0 hcon
  have hgeo : Tendsto (fun n : ℕ => c ^ (n / k)) atTop (𝓝 0) := by
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp ?_
    exact tendsto_atTop_atTop.2 fun b => ⟨b * k, fun a ha => (Nat.le_div_iff_mul_le hk).2 ha⟩
  -- sum-zero vectors are driven to zero
  have hzero : ∀ z : Fin d → ℝ, ∑ j, z j = 0 → Tendsto (fun n => (R ^ n) *ᵥ z) atTop (𝓝 0) := by
    intro z hz
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (X7_norm_le_l1 _).trans (hit n z hz)) ?_
    simpa using hgeo.mul_const (X7_l1 z)
  let u : Fin d → ℝ := fun i => if i = ⟨0, hd⟩ then 1 else 0
  have hu0 : ∀ i, 0 ≤ u i := fun i => by simp only [u]; split_ifs <;> norm_num
  have hu1 : ∑ i, u i = 1 := by simp [u]
  have hul1 : X7_l1 u = 1 := by
    unfold X7_l1; rw [Finset.sum_congr rfl fun i _ => abs_of_nonneg (hu0 i), hu1]
  let w : ℕ → Fin d → ℝ := fun n => (R ^ n) *ᵥ u
  have hwnn : ∀ n i, 0 ≤ w n i := fun n i => by
    simp only [w, Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_nonneg ((X7_stoch_pow hR n).1 _ _) (hu0 j)
  have hwsum : ∀ n, ∑ i, w n i = 1 := fun n => by
    simp only [w]; rw [X7_sum_mulVec (X7_stoch_pow hR n), hu1]
  have hdist : ∀ n m, n ≤ m → dist (w m) (w n) ≤ 2 * c ^ (n / k) := by
    intro n m hnm
    set z : Fin d → ℝ := (R ^ (m - n)) *ᵥ u - u
    have hz : ∑ j, z j = 0 := by
      simp only [z, Pi.sub_apply, Finset.sum_sub_distrib]
      rw [X7_sum_mulVec (X7_stoch_pow hR _), hu1, sub_self]
    have hzl : X7_l1 z ≤ 2 := by
      unfold X7_l1
      calc ∑ i, |z i| ≤ ∑ i, (|((R ^ (m - n)) *ᵥ u) i| + |u i|) :=
            Finset.sum_le_sum fun i _ => abs_sub _ _
        _ = X7_l1 ((R ^ (m - n)) *ᵥ u) + X7_l1 u := Finset.sum_add_distrib
        _ ≤ X7_l1 u + X7_l1 u := by gcongr; exact X7_l1_mulVec (X7_stoch_pow hR _) u
        _ = 2 := by rw [hul1]; norm_num
    have hwz : w m - w n = (R ^ n) *ᵥ z := by
      have hpm : R ^ m = R ^ n * R ^ (m - n) := by rw [← pow_add]; congr 1; omega
      simp only [w, z, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hpm]
    rw [dist_eq_norm, hwz]
    calc ‖(R ^ n) *ᵥ z‖ ≤ X7_l1 ((R ^ n) *ᵥ z) := X7_norm_le_l1 _
      _ ≤ c ^ (n / k) * X7_l1 z := hit n z hz
      _ ≤ c ^ (n / k) * 2 := by gcongr
      _ = 2 * c ^ (n / k) := by ring
  have hcauchy : CauchySeq w := by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * c ^ (N / k)) ?_ (by simpa using hgeo.const_mul 2)
    intro n m N hn hm
    have hmono : ∀ a, N ≤ a → 2 * c ^ (a / k) ≤ 2 * c ^ (N / k) := fun a ha => by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hc0 hc1.le (Nat.div_le_div_right ha)) (by norm_num)
    rcases le_total n m with h | h
    · rw [dist_comm]; exact (hdist n m h).trans (hmono n hn)
    · exact (hdist m n h).trans (hmono m hm)
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hvi : ∀ i, Tendsto (fun n => w n i) atTop (𝓝 (v i)) := fun i => tendsto_pi_nhds.1 hv i
  refine ⟨v, fun i => ge_of_tendsto' (hvi i) fun n => hwnn n i, ?_, ?_⟩
  · have h1 : Tendsto (fun n => ∑ i, w n i) atTop (𝓝 (∑ i, v i)) :=
      tendsto_finsetSum _ fun i _ => hvi i
    simp only [hwsum] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  · intro y
    set sy := ∑ j, y j
    have hz : ∑ j, (y - sy • u) j = 0 := by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
        ← Finset.mul_sum, hu1]; simp [sy]
    have heq : (fun n => (R ^ n) *ᵥ y) = fun n => sy • w n + (R ^ n) *ᵥ (y - sy • u) := by
      funext n; simp only [w, Matrix.mulVec_sub, Matrix.mulVec_smul]; abel
    rw [heq]
    simpa using (hv.const_smul sy).add (hzero _ hz)


open QAlgorithms.Papers.Independent.Dependency50.P37
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

lemma X7_realize {A : Operator d} (hA : ColumnStochastic A) :
    X7_Stoch (A.map Complex.re) ∧ A = (A.map Complex.re).map (fun x : ℝ => (x : ℂ)) := by
  refine ⟨⟨fun i j => (hA.1 i j).2, fun j => ?_⟩, ?_⟩
  · have := congrArg Complex.re (hA.2 j)
    simpa [Complex.re_sum] using this
  · ext i j; apply Complex.ext <;> simp [(hA.1 i j).1]

lemma X7_pow_map (R : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    (R.map (fun x : ℝ => (x : ℂ))) ^ n = (R ^ n).map (fun x : ℝ => (x : ℂ)) := by
  exact (map_pow (Complex.ofRealHom.mapMatrix (m := Fin d)) R n).symm

lemma X7_pow_entry {A : Operator d} (hA : ColumnStochastic A) (n : ℕ) :
    A ^ n = ((A.map Complex.re) ^ n).map (fun x : ℝ => (x : ℂ)) := by
  conv_lhs => rw [(X7_realize hA).2]
  rw [X7_pow_map]

lemma X7_mulVec_ofReal (M : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℂ) :
    (M.map (fun x : ℝ => (x : ℂ))) *ᵥ x = fun i =>
      (((M *ᵥ fun j => (x j).re) i : ℝ) : ℂ) + Complex.I * (((M *ᵥ fun j => (x j).im) i : ℝ) : ℂ) := by
  funext i
  apply Complex.ext <;> simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum]

lemma X7_mixing_of_real (hd : 0 < d) {A : Operator d} (hA : ColumnStochastic A) {k : ℕ}
    (hk : 0 < k) (hscr : ∀ j l, ∃ i, 0 < ((A.map Complex.re) ^ k) i j * ((A.map Complex.re) ^ k) i l) :
    MatrixMixing A := by
  obtain ⟨hR, -⟩ := X7_realize hA
  obtain ⟨v, hv0, hv1, hlim⟩ := X7_real_mixing hd hR hk hscr
  refine ⟨fun i => (v i : ℂ), fun i => ⟨by simp, by simpa using hv0 i⟩, ?_, fun x => ?_⟩
  · rw [← Complex.ofReal_sum, hv1]; simp
  · have hpow : ∀ n, A ^ n = ((A.map Complex.re) ^ n).map (fun x : ℝ => (x : ℂ)) :=
      X7_pow_entry hA
    simp_rw [hpow, X7_mulVec_ofReal]
    have h1 := hlim (fun j => (x j).re)
    have h2 := hlim (fun j => (x j).im)
    have hc : Continuous (fun f : Fin d → ℝ => fun i => ((f i : ℝ) : ℂ)) :=
      continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i)
    have := ((hc.tendsto _).comp h1).add (((hc.tendsto _).comp h2).const_smul Complex.I)
    convert this using 1
    · funext n; funext i; simp [Function.comp]
    · congr 1
      funext i
      apply Complex.ext <;> simp [Complex.re_sum, Complex.im_sum]

lemma X7_exists_pos {v : Fin d → ℂ} (hv : ∀ i, (v i).im = 0 ∧ 0 ≤ (v i).re)
    (hv1 : ∑ i, v i = 1) : ∃ i0, 0 < (v i0).re := by
  by_contra h
  push Not at h
  have : (∑ i, v i).re ≤ 0 := by
    rw [Complex.re_sum]; exact Finset.sum_nonpos fun i _ => h i
  rw [hv1] at this; norm_num at this

lemma X7_entry_tendsto {A : Operator d} {v : Fin d → ℂ}
    (hlim : ∀ x : Fin d → ℂ, Tendsto (fun n : ℕ => Matrix.mulVec (A ^ n) x)
      atTop (𝓝 ((∑ i, x i) • v))) (i j : Fin d) :
    Tendsto (fun n : ℕ => ((A ^ n) i j).re) atTop (𝓝 (v i).re) := by
  have h := hlim (Pi.single j 1)
  have h2 := (Complex.continuous_re.tendsto _).comp (((continuous_apply i).tendsto _).comp h)
  have e : (((∑ i, (Pi.single j (1 : ℂ) : Fin d → ℂ) i) • v) i).re = (v i).re := by simp
  rw [e] at h2
  refine h2.congr fun n => ?_
  simp [Function.comp, Matrix.mulVec_single]

end X7Q10

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Information100.P23 (Operator)
open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)
open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)
open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)
open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

open QAlgorithms.Papers.Independent.Dependency50.P37 X7Q10 in
theorem solution {d : ℕ} (hd : 0 < d) (A : Operator d) (hA : ColumnStochastic A) :
    MatrixPrimitive A ↔ ∃ k : ℕ, 0 < k ∧ MatrixStrictlyPositive (A ^ k) := by
  have him : ∀ n i j, ((A ^ n) i j).im = 0 := fun n i j => by
    rw [X7_pow_entry hA n]; simp
  have hcolsum : ∀ x : Fin d → ℂ, ∑ i, (A *ᵥ x) i = ∑ j, x j := fun x => by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hA.2, one_mul]
  constructor
  · rintro ⟨⟨v, hv, hv1, hlim⟩, w, hw, hw1, hAw⟩
    have hpw : ∀ n, (A ^ n) *ᵥ w = w := by
      intro n; induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hAw, ih]
    have hvw : w = v := by
      have := hlim w
      simp only [hpw, hw1, one_smul] at this
      exact tendsto_nhds_unique tendsto_const_nhds this
    subst hvw
    have hev : ∀ᶠ n in atTop, 1 ≤ n ∧ ∀ i j, 0 < ((A ^ n) i j).re := by
      refine (eventually_ge_atTop 1).and (eventually_all.2 fun i => eventually_all.2 fun j => ?_)
      exact (X7_entry_tendsto hlim i j).eventually (lt_mem_nhds (hw i).2)
    obtain ⟨n, hn1, hn⟩ := hev.exists
    exact ⟨n, hn1, fun i j => ⟨him n i j, hn i j⟩⟩
  · rintro ⟨k, hk, hpos⟩
    have hmix : MatrixMixing A := by
      refine X7_mixing_of_real hd hA hk fun j l => ⟨⟨0, hd⟩, ?_⟩
      have h := X7_pow_entry hA k
      have h1 := (hpos ⟨0, hd⟩ j).2
      have h2 := (hpos ⟨0, hd⟩ l).2
      rw [h] at h1 h2
      simp only [Matrix.map_apply, Complex.ofReal_re] at h1 h2
      exact mul_pos h1 h2
    refine ⟨hmix, ?_⟩
    obtain ⟨v, hv, hv1, hlim⟩ := hmix
    let u : Fin d → ℂ := Pi.single ⟨0, hd⟩ 1
    have hu : ∑ j, u j = 1 := by simp [u]
    have hAv : A *ᵥ v = v := by
      have h1 := hlim (A *ᵥ u)
      rw [hcolsum, hu, one_smul] at h1
      have h2 : Tendsto (fun n : ℕ => A *ᵥ ((A ^ n) *ᵥ u)) atTop (𝓝 (A *ᵥ v)) := by
        have hc : Continuous (fun x : Fin d → ℂ => A *ᵥ x) :=
          (Matrix.mulVecLin A).continuous_of_finiteDimensional
        have := (hc.tendsto _).comp (hlim u)
        rw [hu, one_smul] at this
        exact this
      have heq : (fun n : ℕ => A *ᵥ ((A ^ n) *ᵥ u)) = fun n => (A ^ n) *ᵥ (A *ᵥ u) := by
        funext n; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← pow_succ', ← pow_succ]
      rw [heq] at h2
      exact tendsto_nhds_unique h2 h1
    have hpv' : ∀ n : ℕ, (A ^ n) *ᵥ v = v := by
      intro n; induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, ih]
    have hpv := hpv' k
    refine ⟨v, fun i => ⟨(hv i).1, ?_⟩, hv1, hAv⟩
    obtain ⟨j0, hj0⟩ := X7_exists_pos hv hv1
    have hre : (v i).re = ∑ j, ((A ^ k) i j).re * (v j).re := by
      conv_lhs => rw [← hpv]
      simp only [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re, him k i, zero_mul,
        sub_zero]
    rw [hre]
    calc 0 < ((A ^ k) i j0).re * (v j0).re := mul_pos (hpos i j0).2 hj0
      _ ≤ ∑ j, ((A ^ k) i j).re * (v j).re :=
        Finset.single_le_sum (f := fun j => ((A ^ k) i j).re * (v j).re)
          (fun j _ => mul_nonneg (hpos i j).2.le (hv j).2) (Finset.mem_univ j0)
