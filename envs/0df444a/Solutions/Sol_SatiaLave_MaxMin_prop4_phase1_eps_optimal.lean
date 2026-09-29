-- Prove2me | solution 1 for SatiaLave.MaxMin.prop4_phase1_eps_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T05:05:52.545145+00:00
-- url     : https://prove2.me/submissions/7047297c-ca38-4f51-a515-f56adc118b2d

import Mathlib
import Definitions.Def_SatiaLave_MaxMin_Model
import Definitions.Def_SatiaLave_MaxMin_Algorithm

namespace SatiaLave.MaxMin

/-- averaging bound: a probability row averages values bounded by `c` to at most `c`. -/
theorem aux_p4e_avg {S : Type*} [Fintype S] (q : S → ℝ) (hq : q ∈ stdSimplex ℝ S)
    (e : S → ℝ) (c : ℝ) (he : ∀ j, e j ≤ c) : ∑ j, q j * e j ≤ c := by
  have h1 : ∑ j, q j * e j ≤ ∑ j, q j * c :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (he j) (hq.1 j)
  rw [← Finset.sum_mul, hq.2, one_mul] at h1
  exact h1

/-- maximum principle: `d ≤ β Q d` with `Q` stochastic and `0 ≤ β < 1` forces `d ≤ 0`. -/
theorem aux_p4e_max {S : Type*} [Fintype S] (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (q : S → S → ℝ) (hq : ∀ i, q i ∈ stdSimplex ℝ S) (d : S → ℝ)
    (hd : ∀ i, d i ≤ β * ∑ j, q i j * d j) : ∀ i, d i ≤ 0 := by
  intro i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ d ⟨i, Finset.mem_univ i⟩
  have h1 : ∑ j, q i0 j * d j ≤ d i0 :=
    aux_p4e_avg (q i0) (hq i0) d (d i0) (fun j => hi0 j (Finset.mem_univ j))
  have h3 : d i0 ≤ β * d i0 := (hd i0).trans (mul_le_mul_of_nonneg_left h1 hβ0)
  have h4 : d i0 ≤ 0 := by nlinarith
  exact (hi0 i (Finset.mem_univ i)).trans h4

theorem aux_p4e_diff {S : Type*} [Fintype S] (q r x y : S → ℝ) (β : ℝ) :
    ∑ j, q j * (r j + β * x j) - ∑ j, q j * (r j + β * y j) =
      β * ∑ j, q j * (x j - y j) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem aux_p4e_eq5 {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : Sel M) :
    ∀ i, presentValue M A P i =
      ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) := by
  have hrow : ∀ i, P.1 i (A i) ∈ stdSimplex ℝ S := fun i => M.U_subset i (A i) (P.2 i (A i))
  set N : Matrix S S ℝ := 1 - M.β • transMat M A P with hN
  have hmul : ∀ x : S → ℝ, ∀ i, (Matrix.mulVec N x) i = x i - M.β * ∑ j, P.1 i (A i) j * x j := by
    intro x i
    simp [hN, Matrix.mulVec, dotProduct, transMat, Finset.mul_sum, sub_mul,
      Finset.sum_sub_distrib, Matrix.one_apply, mul_assoc]
  have hdet : N.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have hfix : ∀ i, x i = M.β * ∑ j, P.1 i (A i) j * x j := by
      intro i
      have := congrFun hx i
      rw [hmul] at this
      simp only [Pi.zero_apply] at this
      linarith
    have hle := aux_p4e_max M.β M.β_nonneg M.β_lt_one (fun i => P.1 i (A i)) hrow x
      (fun i => (hfix i).le)
    have hge := aux_p4e_max M.β M.β_nonneg M.β_lt_one (fun i => P.1 i (A i)) hrow (-x)
      (fun i => by
        simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
        linarith [hfix i])
    apply hx0
    funext i
    have a := hle i
    have b := hge i
    simp only [Pi.neg_apply] at b
    simp only [Pi.zero_apply]
    linarith
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hdet
  have hv : Matrix.mulVec N (presentValue M A P) = rewardVec M A P := by
    unfold presentValue
    rw [← hN, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hu, Matrix.one_mulVec]
  intro i
  have := congrFun hv i
  rw [hmul] at this
  have e : ∑ j, P.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A P j) =
      rewardVec M A P i + M.β * ∑ j, P.1 i (A i) j * presentValue M A P j := by
    simp only [rewardVec, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  linarith

/-- uniform lower bound on present values. -/
theorem aux_p4e_lower {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (Q : Sel M) (i : S) :
    -(∑ i, ∑ j, |M.r i (A i) j|) / (1 - M.β) ≤ presentValue M A Q i := by
  have hRle : ∀ i j, -(∑ i, ∑ j, |M.r i (A i) j|) ≤ M.r i (A i) j := by
    intro i j
    have h1 : |M.r i (A i) j| ≤ ∑ j, |M.r i (A i) j| :=
      Finset.single_le_sum (f := fun j => |M.r i (A i) j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h2 : ∑ j, |M.r i (A i) j| ≤ ∑ i, ∑ j, |M.r i (A i) j| :=
      Finset.single_le_sum (f := fun i => ∑ j, |M.r i (A i) j|)
        (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have := neg_abs_le (M.r i (A i) j)
    linarith
  generalize (∑ i, ∑ j, |M.r i (A i) j|) = R at hRle
  have hβ1 : 0 < 1 - M.β := by linarith [M.β_lt_one]
  have hc : -R / (1 - M.β) * (1 - M.β) = -R := div_mul_cancel₀ _ hβ1.ne'
  generalize -R / (1 - M.β) = c at hc
  have hrow : ∀ i, Q.1 i (A i) ∈ stdSimplex ℝ S := fun i => M.U_subset i (A i) (Q.2 i (A i))
  have key := aux_p4e_max M.β M.β_nonneg M.β_lt_one (fun i => Q.1 i (A i)) hrow
    (fun i => c - presentValue M A Q i) (by
      intro i
      have e1 := aux_p4e_eq5 M A Q i
      have e2 : ∑ j, Q.1 i (A i) j * (M.r i (A i) j + M.β * presentValue M A Q j) =
          ∑ j, Q.1 i (A i) j * M.r i (A i) j +
            M.β * ∑ j, Q.1 i (A i) j * presentValue M A Q j := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        exact Finset.sum_congr rfl fun j _ => by ring
      have e3 : ∑ j, Q.1 i (A i) j * (c - presentValue M A Q j) =
          c - ∑ j, Q.1 i (A i) j * presentValue M A Q j := by
        simp only [mul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul, (hrow i).2, one_mul]
      have e4 : ∑ j, Q.1 i (A i) j * (-M.r i (A i) j) ≤ R :=
        aux_p4e_avg _ (hrow i) _ R (fun j => by linarith [hRle i j])
      simp only [mul_neg, Finset.sum_neg_distrib] at e4
      show c - presentValue M A Q i ≤ M.β * ∑ j, Q.1 i (A i) j * (c - presentValue M A Q j)
      rw [e3, mul_sub, e1, e2]
      have : c = -R + M.β * c := by rw [← hc]; ring
      linarith)
  linarith [key i]

end SatiaLave.MaxMin

open SatiaLave.MaxMin

theorem solution {S : Type*} [Fintype S] [DecidableEq S] {D : S → Type*}
    (M : UncertainMDP S D) (A : Policy S D) (P : ℕ → Sel M)
    (hrun : ∀ n, IsPhase1Step M A (P n) (P (n + 1))) :
    (∀ ε > 0, ∃ n, ∀ m ≥ n, ∀ i, presentValue M A (P m) i ≤ robustValue M A i + ε) ∧
      ∀ n, Phase1Stops M A (P n) (P (n + 1)) → ∀ i, presentValue M A (P n) i = robustValue M A i := by
  have hβ0 := M.β_nonneg
  have hβ1 := M.β_lt_one
  have hβ1' : 0 < 1 - M.β := by linarith
  have : Nonempty (Sel M) := ⟨P 0⟩
  have hlow := aux_p4e_lower M A
  have hbdd : ∀ i, BddBelow (Set.range fun Q : Sel M => presentValue M A Q i) :=
    fun i => ⟨_, by rintro _ ⟨Q, rfl⟩; exact hlow Q i⟩
  have hrow : ∀ (Q : Sel M) i, Q.1 i (A i) ∈ stdSimplex ℝ S :=
    fun Q i => M.U_subset i (A i) (Q.2 i (A i))
  -- monotonicity of the run
  have hmono : ∀ n i, presentValue M A (P (n + 1)) i ≤ presentValue M A (P n) i := by
    intro n
    have := aux_p4e_max M.β hβ0 hβ1 (fun i => (P (n + 1)).1 i (A i)) (hrow (P (n + 1)))
      (fun i => presentValue M A (P (n + 1)) i - presentValue M A (P n) i) (by
        intro i
        have h1 := hrun n i ((P n).1 i (A i)) ((P n).2 i (A i))
        rw [← aux_p4e_eq5 M A (P n) i] at h1
        have e' := aux_p4e_eq5 M A (P (n + 1)) i
        have hd := aux_p4e_diff ((P (n + 1)).1 i (A i)) (M.r i (A i))
          (presentValue M A (P (n + 1))) (presentValue M A (P n)) M.β
        show presentValue M A (P (n + 1)) i - presentValue M A (P n) i ≤ M.β *
          ∑ j, (P (n + 1)).1 i (A i) j *
            (presentValue M A (P (n + 1)) j - presentValue M A (P n) j)
        linarith)
    intro i
    linarith [this i]
  -- one-step comparison with an arbitrary choice of nature
  have hcomp : ∀ (Q : Sel M) n i, presentValue M A (P (n + 1)) i - presentValue M A Q i ≤
      M.β * ∑ j, Q.1 i (A i) j * (presentValue M A (P n) j - presentValue M A Q j) := by
    intro Q n i
    have h1 := hrun n i (Q.1 i (A i)) (Q.2 i (A i))
    have e' := aux_p4e_eq5 M A (P (n + 1)) i
    have eQ := aux_p4e_eq5 M A Q i
    have hd1 := aux_p4e_diff ((P (n + 1)).1 i (A i)) (M.r i (A i))
      (presentValue M A (P n)) (presentValue M A (P (n + 1))) M.β
    have hd2 := aux_p4e_diff (Q.1 i (A i)) (M.r i (A i))
      (presentValue M A (P n)) (presentValue M A Q) M.β
    have hnn : 0 ≤ M.β * ∑ j, (P (n + 1)).1 i (A i) j *
        (presentValue M A (P n) j - presentValue M A (P (n + 1)) j) :=
      mul_nonneg hβ0 (Finset.sum_nonneg fun j _ =>
        mul_nonneg ((hrow (P (n + 1)) i).1 j) (sub_nonneg.mpr (hmono n j)))
    linarith
  -- geometric bound
  set C : ℝ := (∑ i, |presentValue M A (P 0) i|) + (∑ i, ∑ j, |M.r i (A i) j|) / (1 - M.β)
    with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ (∑ i, ∑ j, |M.r i (A i) j|) / (1 - M.β) :=
      div_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
        hβ1'.le
    have : 0 ≤ ∑ i, |presentValue M A (P 0) i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hind : ∀ n (Q : Sel M) i, presentValue M A (P n) i - presentValue M A Q i ≤ M.β ^ n * C := by
    intro n
    induction n with
    | zero =>
      intro Q i
      have h1 : presentValue M A (P 0) i ≤ ∑ i, |presentValue M A (P 0) i| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun i => |presentValue M A (P 0) i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ i))
      have h2 := hlow Q i
      rw [neg_div] at h2
      simp only [pow_zero, one_mul]
      linarith
    | succ n ih =>
      intro Q i
      have h1 := hcomp Q n i
      have h2 : ∑ j, Q.1 i (A i) j * (presentValue M A (P n) j - presentValue M A Q j) ≤
          M.β ^ n * C := aux_p4e_avg _ (hrow Q i) _ _ (fun j => ih Q j)
      have h3 := mul_le_mul_of_nonneg_left h2 hβ0
      rw [pow_succ]
      linarith
  refine ⟨?_, ?_⟩
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (C + 1) by positivity) hβ1
    refine ⟨n, fun m hm i => ?_⟩
    have hpow : M.β ^ m ≤ M.β ^ n := pow_le_pow_of_le_one hβ0 hβ1.le hm
    have hbn : M.β ^ n * C ≤ ε := by
      have h1 : M.β ^ n * (C + 1) < ε := by
        rwa [lt_div_iff₀ (by positivity)] at hn
      have h2 : 0 ≤ M.β ^ n := pow_nonneg hβ0 n
      nlinarith
    have hbm : M.β ^ m * C ≤ ε := (mul_le_mul_of_nonneg_right hpow hC0).trans hbn
    have : presentValue M A (P m) i - ε ≤ robustValue M A i :=
      le_ciInf fun Q => by linarith [hind m Q i]
    linarith
  · intro n hstop i
    have hle : ∀ Q : Sel M, ∀ i, presentValue M A (P n) i ≤ presentValue M A Q i := by
      intro Q
      have := aux_p4e_max M.β hβ0 hβ1 (fun i => Q.1 i (A i)) (hrow Q)
        (fun i => presentValue M A (P n) i - presentValue M A Q i) (by
          intro i
          have h1 := hrun n i (Q.1 i (A i)) (Q.2 i (A i))
          have hs := hstop i
          have eQ := aux_p4e_eq5 M A Q i
          have hd := aux_p4e_diff (Q.1 i (A i)) (M.r i (A i))
            (presentValue M A (P n)) (presentValue M A Q) M.β
          show presentValue M A (P n) i - presentValue M A Q i ≤ M.β *
            ∑ j, Q.1 i (A i) j * (presentValue M A (P n) j - presentValue M A Q j)
          linarith)
      intro i
      linarith [this i]
    exact le_antisymm (le_ciInf fun Q => hle Q i) (ciInf_le (hbdd i) (P n))
