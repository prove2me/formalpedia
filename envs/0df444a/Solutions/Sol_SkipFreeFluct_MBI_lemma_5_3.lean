-- Prove2me | solution 1 for SkipFreeFluct.MBI.lemma_5_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T10:49:00.857494+00:00
-- url     : https://prove2.me/submissions/94dd2bfa-0bbf-4a7c-b4d0-99aab5457f06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SkipFreeFluct_MBI_Chain
import Definitions.Def_SkipFreeFluct_MBI_Model
import Theorems.Thm_SkipFreeFluct_MBI_lemma_5_1
import Theorems.Thm_SkipFreeFluct_MBI_lemma_5_2
import Theorems.Thm_SkipFreeFluct_MBI_transition_tsum_le_one
import Theorems.Thm_SkipFreeFluct_MBI_mbiQ_skipFree_QMatrix
open scoped ENNReal Topology
open Filter MeasureTheory

namespace MBI53R
open SkipFreeFluct.MBI Finset

/-- One-sided identity theorem for power series. -/
lemma coeff_zero_of_tsum_zero (c : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hsum : Summable (fun n => |c n| * r ^ n))
    (h0 : ∀ s ∈ Set.Ioo 0 r, ∑' n, c n * s ^ n = 0) : ∀ n, c n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ k ih =>
    have hMs : Summable (fun n => |c (n + k + 1)| * r ^ n) := by
      have h1 := (summable_nat_add_iff (k + 1)).mpr hsum
      refine (h1.mul_left (1 / r ^ (k + 1))).congr fun n => ?_
      rw [show n + (k + 1) = n + k + 1 by omega, pow_add]
      field_simp
      ring
    set M := ∑' n, |c (n + k + 1)| * r ^ n with hM
    have hM0 : 0 ≤ M := tsum_nonneg fun n => by positivity
    have key : ∀ s ∈ Set.Ioo 0 r, |c k| ≤ s * M := by
      intro s hs
      have hsr : Summable (fun n => c n * s ^ n) := by
        refine Summable.of_norm_bounded hsum fun n => ?_
        rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_of_nonneg hs.1.le]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1.le hs.2.le _) (abs_nonneg _)
      have e1 := hsr.sum_add_tsum_nat_add k
      have hz : ∑ i ∈ Finset.range k, c i * s ^ i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [ih i (Finset.mem_range.1 hi), zero_mul]
      rw [hz, zero_add, h0 s hs] at e1
      have hsr' : Summable (fun n => c (n + k) * s ^ (n + k)) := (summable_nat_add_iff k).mpr hsr
      rw [hsr'.tsum_eq_zero_add] at e1
      simp only [zero_add] at e1
      have hb : ∀ n, |c (n + 1 + k) * s ^ (n + 1 + k)| ≤ s ^ (k + 1) * (|c (n + k + 1)| * r ^ n) := by
        intro n
        rw [abs_mul, abs_of_nonneg (pow_nonneg hs.1.le _), show n + 1 + k = n + k + 1 by omega]
        rw [show s ^ (n + k + 1) = s ^ (k + 1) * s ^ n by rw [← pow_add]; congr 1; omega]
        have := pow_le_pow_left₀ hs.1.le hs.2.le n
        have h3 : 0 ≤ s ^ (k + 1) := pow_nonneg hs.1.le _
        nlinarith [abs_nonneg (c (n + k + 1)), mul_le_mul_of_nonneg_left this
          (mul_nonneg (abs_nonneg (c (n + k + 1))) h3)]
      have hsumb : Summable (fun n => c (n + 1 + k) * s ^ (n + 1 + k)) :=
        Summable.of_norm_bounded (hMs.mul_left (s ^ (k + 1))) (fun n => by
          rw [Real.norm_eq_abs]; exact hb n)
      have hle : |∑' n, c (n + 1 + k) * s ^ (n + 1 + k)| ≤ s ^ (k + 1) * M := by
        rw [hM, ← tsum_mul_left]
        refine (norm_tsum_le_tsum_norm hsumb.norm).trans ?_
        exact Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hb n) hsumb.norm
          (hMs.mul_left _)
      have hck : |c k| * s ^ k ≤ s ^ k * (s * M) := by
        have : c k * s ^ k = -∑' n, c (n + 1 + k) * s ^ (n + 1 + k) := by linarith
        rw [← abs_of_nonneg (pow_nonneg hs.1.le k), ← abs_mul, this, abs_neg,
          abs_of_nonneg (pow_nonneg hs.1.le k)]
        calc _ ≤ s ^ (k + 1) * M := hle
          _ = s ^ k * (s * M) := by ring
      have hsk : 0 < s ^ k := pow_pos hs.1 k
      nlinarith
    by_contra hne
    have hpos : 0 < |c k| := abs_pos.mpr hne
    set s := min (r / 2) (|c k| / (2 * (M + 1))) with hs
    have hs1 : 0 < s := lt_min (by linarith) (by positivity)
    have hs2 : s < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h := key s ⟨hs1, hs2⟩
    have h3 : s ≤ |c k| / (2 * (M + 1)) := min_le_right _ _
    have h4 : s * M ≤ |c k| / (2 * (M + 1)) * M := mul_le_mul_of_nonneg_right h3 hM0
    have h5 : |c k| / (2 * (M + 1)) * M < |c k| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

lemma psi_continuousOn (P : MBIParams) (hP : P.Valid) : ContinuousOn (psi P) (Set.Icc 0 1) := by
  obtain ⟨_, hmu, hmu1, _⟩ := hP
  have hser : ContinuousOn (fun s : ℝ => ∑' j : ℕ, P.mu j * s ^ j) (Set.Icc 0 1) := by
    refine continuousOn_tsum (u := P.mu) (fun j => by fun_prop) hmu1.summable (fun j s hs => ?_)
    rw [norm_mul, Real.norm_of_nonneg (hmu j), norm_pow, Real.norm_of_nonneg hs.1]
    exact mul_le_of_le_one_right (hmu j) (pow_le_one₀ hs.1 hs.2)
  unfold psi
  exact (continuousOn_const.mul (hser.sub continuousOn_id)).sub
    (continuousOn_const.mul continuousOn_id)

lemma s0_pos (P : MBIParams) (hP : P.Valid) : 0 < s0 P := by
  have hc := psi_continuousOn P hP
  obtain ⟨hα, hmu, hmu1, hmu0, _, hp, _⟩ := hP
  have h0 : psi P 0 = P.alpha * P.mu 0 := by
    unfold psi
    rw [tsum_eq_single 0 (fun j hj => by simp [zero_pow hj])]
    simp
  have h1 : psi P 1 = -P.p := by
    unfold psi
    simp only [one_pow, mul_one]
    rw [hmu1.tsum_eq]; ring
  have hpos0 : 0 < psi P 0 := by rw [h0]; positivity
  -- a zero in (0, 1]
  obtain ⟨c, hcI, hc0⟩ : ∃ c ∈ Set.Icc (0 : ℝ) 1, psi P c = 0 :=
    intermediate_value_Icc' zero_le_one hc ⟨by rw [h1]; linarith, hpos0.le⟩
  have hcne : c ≠ 0 := by rintro rfl; linarith
  have hne : ({s : ℝ | s ∈ Set.Ioc (0 : ℝ) 1 ∧ psi P s = 0}).Nonempty :=
    ⟨c, ⟨lt_of_le_of_ne hcI.1 (Ne.symm hcne), hcI.2⟩, hc0⟩
  -- positivity of psi near 0
  have hev : ∀ᶠ s in 𝓝[Set.Icc 0 1] (0 : ℝ), 0 < psi P s :=
    (hc 0 ⟨le_rfl, zero_le_one⟩).eventually (lt_mem_nhds hpos0)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hev
  refine lt_of_lt_of_le hε (le_csInf hne fun s hs => ?_)
  by_contra hlt
  push Not at hlt
  have : 0 < psi P s := hball ⟨by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hs.1.1]; exact hlt,
    ⟨hs.1.1.le, hs.1.2⟩⟩
  linarith [hs.2]

end MBI53R

open SkipFreeFluct.MBI Finset MBI53R in
theorem solution (P : MBIParams) (hP : P.Valid) :
    IsStationaryMeasure (Set.Ici 0) (mbiQ P)
      (fun x : ℤ => if 0 ≤ x then piSeq P x.toNat else 0) := by
  obtain ⟨hnn, hgf⟩ := lemma_5_1 P hP
  obtain ⟨hbij, hgen⟩ := lemma_5_2 P hP
  have hs0 := s0_pos P hP
  have hpi : ∀ k, 0 ≤ piSeq P k := fun k => (hnn k).2.2.2
  refine ⟨fun x _ => by dsimp only; split_ifs <;> simp [hpi], ?_⟩
  intro t ht y hy
  have hy0 : (0 : ℤ) ≤ y := hy
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hy0
  set T : ℕ → ℕ → ℝ≥0∞ := fun k m => transition (Set.Ici 0) (mbiQ P) t k m with hT
  have hTfin : ∀ k m, T k m ≠ ⊤ := by
    intro k m
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    exact (ENNReal.le_tsum (m : ℤ)).trans
      (transition_tsum_le_one _ _ (mbiQ_skipFree_QMatrix P hP).2.1 t k)
  -- reindex the sum over the state space by ℕ
  let e : ℕ ≃ Set.Ici (0 : ℤ) :=
    { toFun := fun k => ⟨k, by simp⟩
      invFun := fun x => x.1.toNat
      left_inv := fun k => by simp
      right_inv := fun x => by ext; simp [Int.toNat_of_nonneg (show (0:ℤ) ≤ x.1 from x.2)] }
  have hreidx : ∀ m : ℕ, (∑' x : Set.Ici (0 : ℤ),
      ENNReal.ofReal (if 0 ≤ (x : ℤ) then piSeq P (x : ℤ).toNat else 0) *
        transition (Set.Ici 0) (mbiQ P) t x m) =
      ∑' k : ℕ, ENNReal.ofReal (piSeq P k) * T k m := by
    intro m
    rw [← e.tsum_eq]
    simp [e, hT]
  simp only [hreidx]
  set A : ℕ → ℝ≥0∞ := fun m => ∑' k : ℕ, ENNReal.ofReal (piSeq P k) * T k m with hA
  set pis : ℝ → ℝ := fun s => ∑' k : ℕ, piSeq P k * s ^ k with hpis
  -- generating function of A
  have hK : ∀ s ∈ Set.Ico 0 (s0 P), ∑' m, A m * ENNReal.ofReal (s ^ m) = ENNReal.ofReal (pis s) := by
    intro s hs
    have hts : t + Lam P s ∈ Set.Ici (0 : ℝ) := by
      have := hbij.mapsTo hs; simp only [Set.mem_Ici] at this ⊢; linarith
    obtain ⟨u, hu, hLu⟩ := hbij.surjOn hts
    set C : ℝ := (∑' k : ℕ, piSeq P k * s ^ k) * ∑' k : ℕ, varpi P k * u ^ k with hC
    have hCn : 0 ≤ C := by
      rw [hC, (hgf s hs).2.2.2.1.tsum_eq, (hgf u hu).2.2.2.2.tsum_eq]; positivity
    have hinner : ∀ k : ℕ, ∑' m, T k m * ENNReal.ofReal (s ^ m) = ENNReal.ofReal (u ^ k * C) := by
      intro k
      have h := hgen k t ht s hs u hu hLu
      have he : ∀ m, T k m * ENNReal.ofReal (s ^ m) =
          ENNReal.ofReal ((transition (Set.Ici 0) (mbiQ P) t k m).toReal * s ^ m) := by
        intro m
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hTfin k m)]
      simp only [he]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg ENNReal.toReal_nonneg
        (pow_nonneg hs.1 _)) h.summable, h.tsum_eq]
    calc ∑' m, A m * ENNReal.ofReal (s ^ m)
        = ∑' m, ∑' k, ENNReal.ofReal (piSeq P k) * T k m * ENNReal.ofReal (s ^ m) := by
          simp only [hA, ENNReal.tsum_mul_right]
      _ = ∑' k, ∑' m, ENNReal.ofReal (piSeq P k) * T k m * ENNReal.ofReal (s ^ m) :=
          ENNReal.tsum_comm
      _ = ∑' k, ENNReal.ofReal (piSeq P k) * ENNReal.ofReal (u ^ k * C) := by
          simp only [mul_assoc, ENNReal.tsum_mul_left, hinner]
      _ = ∑' k, ENNReal.ofReal (piSeq P k * u ^ k * C) := by
          congr 1; funext k; rw [← ENNReal.ofReal_mul (hpi k)]; ring_nf
      _ = ENNReal.ofReal (pis s) := by
          have hsum := ((hgf u hu).2.2.2.1.mul_right C)
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (mul_nonneg (hpi k)
            (pow_nonneg hu.1 _)) hCn) hsum.summable, hsum.tsum_eq]
          congr 1
          rw [hC, hpis, (hgf s hs).2.2.2.1.tsum_eq, (hgf u hu).2.2.2.2.tsum_eq,
            mul_comm, mul_assoc, ← Real.exp_add]
          simp only [neg_add_cancel, Real.exp_zero, mul_one]
          exact ((hgf s hs).2.2.2.1.tsum_eq).symm
  have hr : (0 : ℝ) < s0 P / 2 := by linarith
  have hrmem : s0 P / 2 ∈ Set.Ico 0 (s0 P) := ⟨hr.le, by linarith⟩
  have hAfin : ∀ m, A m ≠ ⊤ := by
    intro m h
    have h1 : A m * ENNReal.ofReal ((s0 P / 2) ^ m) ≤ ∑' m, A m * ENNReal.ofReal ((s0 P / 2) ^ m) :=
      ENNReal.le_tsum m
    rw [hK _ hrmem, h, ENNReal.top_mul (by simp [ENNReal.ofReal_eq_zero, not_le, pow_pos hr])]
      at h1
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h1)
  have hreal : ∀ s ∈ Set.Ico 0 (s0 P), HasSum (fun m => (A m).toReal * s ^ m) (pis s) := by
    intro s hs
    have h := hK s hs
    have hne : ∑' m, A m * ENNReal.ofReal (s ^ m) ≠ ⊤ := by rw [h]; exact ENNReal.ofReal_ne_top
    have hpisnn : 0 ≤ pis s := tsum_nonneg fun k => mul_nonneg (hpi k) (pow_nonneg hs.1 _)
    have h2 := (ENNReal.summable_toReal hne).hasSum
    rw [← ENNReal.tsum_toReal_eq (fun m => ENNReal.mul_ne_top (hAfin m) ENNReal.ofReal_ne_top),
      h, ENNReal.toReal_ofReal hpisnn] at h2
    have hterm : ∀ m, (A m * ENNReal.ofReal (s ^ m)).toReal = (A m).toReal * s ^ m := by
      intro m; rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hs.1 _)]
    simpa only [hterm] using h2
  have hc := coeff_zero_of_tsum_zero (fun m => (A m).toReal - piSeq P m) (s0 P / 2) hr ?_ ?_
  · have := hc n
    simp only [sub_eq_zero] at this
    have h0 : (0 : ℤ) ≤ (n : ℤ) := by omega
    simp only [h0, if_true, Int.toNat_natCast]
    rw [← this, ENNReal.ofReal_toReal (hAfin n)]
  · have h1 := (hreal _ hrmem).summable
    have h2 := (hgf _ hrmem).2.2.2.1.summable
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun m => ?_) (h1.add h2)
    have hpow : 0 ≤ (s0 P / 2) ^ m := pow_nonneg hr.le _
    rw [← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hpow
    rw [abs_le]; constructor <;> nlinarith [hpi m, (ENNReal.toReal_nonneg : 0 ≤ (A m).toReal)]
  · intro s hs
    have hsm : s ∈ Set.Ico 0 (s0 P) := ⟨hs.1.le, by linarith [hs.2]⟩
    have := (hreal s hsm).sub (hgf s hsm).2.2.2.1
    simp only [hpis] at this
    rw [(hgf s hsm).2.2.2.1.tsum_eq, sub_self] at this
    simpa only [sub_mul] using this.tsum_eq
