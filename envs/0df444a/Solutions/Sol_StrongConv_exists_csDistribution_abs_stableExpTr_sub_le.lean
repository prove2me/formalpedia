-- Prove2me | solution 1 for StrongConv.exists_csDistribution_abs_stableExpTr_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T22:42:45.4092+00:00
-- url     : https://prove2.me/submissions/1015cfe8-b462-4a52-adb6-5b32406d92a1

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_exists_uniformExp_trN_wordEval_eq_div
import Theorems.Thm_StrongConv_cNorm_iteratedDeriv_div_le
import Theorems.Thm_StrongConv_cNorm_le_two_mul_sSup_of_subset_add
import Theorems.Thm_StrongConv_abs_coeff_zero_le_and_sum_le_lpNormCircle
import Theorems.Thm_StrongConv_tfae_extends_csDistribution

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L1
open StrongConv
/-!
# q202: Blueprint for the stable Lemma 10.3 analogue (`exists_csDistribution_abs_stableExpTr_sub_le`)

CGTvH p. 31: "We can now repeat the proofs in sections 6–7 nearly verbatim with the replacements …".

* `abstract_master` (S1): Theorems 6.1 + 7.1 for an abstract family `E N` of linear functionals that are
  bounded by `s · sup_{[-K,K]} |h|`, rational in `1/N` on polynomials (denominator `g_L`, `L ≤ q Q₀`), and
  exact on the constant function.
* `stable_rational` (S2–S4): Lemma 10.1 for `E[Tr h(P(Πᴺ))]/N^α`.
* `stable_bound`, `stable_linear`, `stable_const`, `stable_degenerate`: the remaining inputs.
-/
/-- `E[Tr h(P(Πᴺ, Πᴺ*))] / N^α`, the left side of the stable Lemma 10.3. -/
def stE (π : StableRep) {D d : ℕ} (P : NCPoly D d) (N : ℕ) (h : ℝ → ℝ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
      ((fnCalc h (P.eval (π.model σ)) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
        PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
      (N : ℝ) ^ π.alpha)

end StrongConv.Q202L1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
noncomputable section
namespace StrongConv.Q202L1.PartS1
open StrongConv StrongConv.Q202L1
/-!
# q202, Part S1: the abstract master inequality (`abstract_master`)

Theorems 6.1 + 7.1 of CGTvH with `expTr P N` replaced by an abstract family `E N`.
The analytic core is `core_estimate` (s67/PartC.lean) generalised to a real parameter `a`;
the assembly follows `exp_data`/`master_dev` (s67/Blueprint.lean) and `poly_master`,
`exists_csDistribution_abs_expTr_sub_le_dev` (Theorem 7.1 solution).
-/
/-- `F` has the asymptotic expansion with coefficients `c`. -/
def HasExp (F : ℕ → ℝ) (c : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    |F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i| ≤ C / (N : ℝ) ^ m

lemma HasExp.tendsto {F c : ℕ → ℝ} (hF : HasExp F c) (m : ℕ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ m * (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i))
      atTop (𝓝 (c m)) := by
  obtain ⟨C, hC⟩ := hF (m + 1)
  have h0 : Tendsto (fun N : ℕ => C / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ h0
  filter_upwards [hC, eventually_gt_atTop 0] with N hN hpos
  have hNp : (0 : ℝ) < N := by exact_mod_cast hpos
  have e : (N : ℝ) ^ m * (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i) - c m =
      (N : ℝ) ^ m * (F N - ∑ i ∈ Finset.range (m + 1), c i / (N : ℝ) ^ i) := by
    rw [Finset.sum_range_succ]; field_simp; ring
  rw [Real.norm_eq_abs, e, abs_mul, abs_of_pos (pow_pos hNp m)]
  calc (N : ℝ) ^ m * |F N - ∑ i ∈ Finset.range (m + 1), c i / (N : ℝ) ^ i|
      ≤ (N : ℝ) ^ m * (C / (N : ℝ) ^ (m + 1)) := mul_le_mul_of_nonneg_left hN (pow_pos hNp m).le
    _ = C / N := by field_simp; ring

lemma HasExp.asympCoeff_eq {F c : ℕ → ℝ} (hF : HasExp F c) (m : ℕ) : asympCoeff F m = c m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [asympCoeff]
    have h : ∀ N : ℕ, ∑ i : Fin m, asympCoeff F i / (N : ℝ) ^ (i : ℕ) =
        ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i := by
      intro N
      rw [Finset.sum_range (fun i => c i / (N : ℝ) ^ i)]
      exact Finset.sum_congr rfl fun i _ => by rw [ih i i.isLt]
    simp only [h]
    exact (hF.tendsto m).limUnder_eq

lemma small_N_arith (a : ℝ) (ha : 1 ≤ a) (m : ℕ) (hm : 1 ≤ m) (N : ℕ) (hN1 : 1 ≤ N)
    (hN : (N : ℝ) < 2 * a ^ 2) :
    1 + ∑ i ∈ Finset.range m, (4 * a) ^ (4 * i) / (N : ℝ) ^ i ≤ (4 * a) ^ (4 * m) / (N : ℝ) ^ m := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  set t : ℝ := (4 * a) ^ 4 / N with ht
  have ht2 : 2 ≤ t := by
    rw [ht, le_div_iff₀ hNp]
    have : (4 * a) ^ 4 = 256 * a ^ 2 * a ^ 2 := by ring
    nlinarith [sq_nonneg a, one_le_pow₀ (n := 2) ha]
  have key : ∀ k : ℕ, 1 + ∑ i ∈ Finset.range k, t ^ i ≤ t ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ← add_assoc, pow_succ]
      have : 1 ≤ t ^ k := one_le_pow₀ (by linarith)
      nlinarith
  have e : ∀ k : ℕ, (4 * a) ^ (4 * k) / (N : ℝ) ^ k = t ^ k := by
    intro k; rw [ht, div_pow, ← pow_mul]
  simp only [e]
  exact key m

lemma prod_one_sub_ge {ι : Type*} (s : Finset ι) (u : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ u i)
    (h1 : ∀ i ∈ s, u i ≤ 1) :
    1 - ∑ i ∈ s, (1 - u i) ≤ ∏ i ∈ s, u i ∧ ∏ i ∈ s, u i ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hj0 := h0 j (Finset.mem_insert_self _ _)
    have hj1 := h1 j (Finset.mem_insert_self _ _)
    have hp0 : 0 ≤ ∏ i ∈ s, u i :=
      Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    constructor
    · nlinarith
    · nlinarith

lemma g_bounds {d Q : ℕ} (a : ℝ) (hQa : (Q : ℝ) ≤ a) (ha1 : 1 ≤ a)
    (hdeg : ((gPoly d Q).natDegree : ℝ) ≤ a) (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / (2 * a ^ 2)) :
    1 / 2 ≤ (gPoly d Q).eval x ∧ (gPoly d Q).eval x ≤ 1 := by
  have hlin : ∀ j ∈ Finset.Ico 1 Q, (1 - (j : ℝ[X]) * X) = C (-(j : ℝ)) * X + C 1 := by
    intro j _; simp [map_natCast]; ring
  have hnd1 : ∀ j ∈ Finset.Ico 1 Q, (1 - (j : ℝ[X]) * X).natDegree = 1 := by
    intro j hj
    rw [hlin j hj]
    apply natDegree_linear
    have : 1 ≤ j := (Finset.mem_Ico.1 hj).1
    have : (1 : ℝ) ≤ j := by exact_mod_cast this
    linarith
  have hne : ∀ j ∈ Finset.Ico 1 Q, (1 - (j : ℝ[X]) * X) ≠ 0 := by
    intro j hj h
    have := hnd1 j hj
    rw [h] at this; simp at this
  have hnd : (gPoly d Q).natDegree = ∑ j ∈ Finset.Ico 1 Q, min d (Q / (j + 1)) := by
    rw [gPoly, natDegree_prod _ _ (fun j hj => pow_ne_zero _ (hne j hj))]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [natDegree_pow, hnd1 j hj, mul_one]
  have hx1 : x * a ≤ 1 / (2 * a) := by
    calc x * a ≤ 1 / (2 * a ^ 2) * a := mul_le_mul_of_nonneg_right hx (by linarith)
      _ = 1 / (2 * a) := by field_simp
  have hxa : x * a ≤ 1 / 2 := by
    refine hx1.trans ?_
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hj : ∀ j ∈ Finset.Ico 1 Q, 0 ≤ 1 - (j : ℝ) * x ∧ (j : ℝ) * x ≤ a * x := by
    intro j hj'
    have hjQ : (j : ℝ) ≤ a := by
      have : j < Q := (Finset.mem_Ico.1 hj').2
      have : (j : ℝ) ≤ Q := by exact_mod_cast this.le
      linarith
    have : (j : ℝ) * x ≤ a * x := mul_le_mul_of_nonneg_right hjQ hx0
    constructor <;> nlinarith
  have hev : (gPoly d Q).eval x = ∏ j ∈ Finset.Ico 1 Q, (1 - (j : ℝ) * x) ^ min d (Q / (j + 1)) := by
    simp [gPoly, eval_prod]
  rw [hev]
  set u : ℕ → ℝ := fun j => (1 - (j : ℝ) * x) ^ min d (Q / (j + 1)) with hu
  have hu0 : ∀ j ∈ Finset.Ico 1 Q, 0 ≤ u j := fun j h => pow_nonneg (hj j h).1 _
  have hu1 : ∀ j ∈ Finset.Ico 1 Q, u j ≤ 1 := fun j h =>
    pow_le_one₀ (hj j h).1 (by have := (hj j h).2; nlinarith [mul_nonneg (Nat.cast_nonneg j) hx0])
  obtain ⟨hA, hB⟩ := prod_one_sub_ge _ u hu0 hu1
  refine ⟨?_, hB⟩
  have hb : ∀ j ∈ Finset.Ico 1 Q, 1 - u j ≤ (min d (Q / (j + 1)) : ℕ) * (a * x) := by
    intro j h
    have hb1 := one_add_mul_le_pow (show (-2 : ℝ) ≤ -((j : ℝ) * x) by
      have := (hj j h).1; nlinarith [mul_nonneg (Nat.cast_nonneg j) hx0]) (min d (Q / (j + 1)))
    rw [← sub_eq_add_neg] at hb1
    have := (hj j h).2
    have h2 : (0 : ℝ) ≤ (min d (Q / (j + 1)) : ℕ) := Nat.cast_nonneg _
    simp only [hu]
    nlinarith [mul_le_mul_of_nonneg_left this h2]
  have hsum : ∑ j ∈ Finset.Ico 1 Q, (1 - u j) ≤ 1 / 2 := by
    calc ∑ j ∈ Finset.Ico 1 Q, (1 - u j)
        ≤ ∑ j ∈ Finset.Ico 1 Q, (min d (Q / (j + 1)) : ℕ) * (a * x) := Finset.sum_le_sum hb
      _ = ((gPoly d Q).natDegree : ℝ) * (a * x) := by
          rw [hnd, ← Finset.sum_mul]; push_cast; rfl
      _ ≤ a * (a * x) := mul_le_mul_of_nonneg_right hdeg (by positivity)
      _ = a * (x * a) := by ring
      _ ≤ a * (1 / (2 * a)) := mul_le_mul_of_nonneg_left hx1 (by linarith)
      _ = 1 / 2 := by field_simp
  linarith

lemma density_lemma (M : ℕ) (hM : 0 < M) (q : ℝ) (hq0 : 0 < q) (hq : 4 * q ^ 2 ≤ 2 * M) :
    Set.Icc (0 : ℝ) (1 / M) ⊆ {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)} +
      Set.Icc (-((1 / (M : ℝ)) / (4 * q ^ 2))) ((1 / (M : ℝ)) / (4 * q ^ 2)) := by
  intro y hy
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  set δ : ℝ := (1 / (M : ℝ)) / (4 * q ^ 2) with hδ
  have hq2 : 0 < 4 * q ^ 2 := by positivity
  have hδD : 1 / (2 * (M : ℝ) ^ 2) ≤ δ := by
    rw [hδ, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have key : ∃ x ∈ {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)}, |y - x| ≤ δ := by
    rcases eq_or_lt_of_le hy.1 with h0 | hpos
    · subst h0
      obtain ⟨n, hn⟩ := exists_nat_ge (1 / δ)
      refine ⟨1 / ((max n M + 1 : ℕ) : ℝ), ⟨_, by omega, rfl⟩, ?_⟩
      have hn' : (1 / δ) ≤ ((max n M + 1 : ℕ) : ℝ) := by
        refine hn.trans ?_
        have : n ≤ max n M + 1 := by omega
        exact_mod_cast this
      have hpos : (0 : ℝ) < ((max n M + 1 : ℕ) : ℝ) := by positivity
      rw [zero_sub, abs_neg, abs_of_pos (by positivity)]
      rw [div_le_iff₀ hpos]
      rw [div_le_iff₀ hδpos] at hn'
      linarith
    · have hyM : (M : ℝ) ≤ 1 / y := by
        rw [le_div_iff₀ hpos]
        have := hy.2
        rw [le_div_iff₀ hMp] at this
        linarith
      set n := ⌊1 / y⌋₊ with hn
      have hnM : M ≤ n := Nat.le_floor hyM
      have hn1 : (n : ℝ) ≤ 1 / y := Nat.floor_le (by positivity)
      have hn2 : 1 / y < n + 1 := Nat.lt_floor_add_one _
      have hnp : (0 : ℝ) < n := by
        have : (M : ℝ) ≤ n := by exact_mod_cast hnM
        linarith
      have hy1 : y ≤ 1 / (n : ℝ) := by
        rw [le_div_iff₀ hnp]; rw [le_div_iff₀ hpos] at hn1; linarith
      have hy2 : 1 / ((n : ℝ) + 1) < y := by
        rw [div_lt_iff₀ (by positivity)]; rw [div_lt_iff₀ hpos] at hn2; linarith
      have hgap : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) ≤ 1 / (M : ℝ) ^ 2 := by
        have : 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) = 1 / ((n : ℝ) * (n + 1)) := by
          field_simp; ring
        rw [this]
        have hnM' : (M : ℝ) ≤ n := by exact_mod_cast hnM
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      have hD : 1 / (M : ℝ) ^ 2 = 2 * (1 / (2 * (M : ℝ) ^ 2)) := by field_simp
      by_cases hc : 1 / (n : ℝ) - y ≤ 1 / (2 * (M : ℝ) ^ 2)
      · refine ⟨1 / (n : ℝ), ⟨n, hnM, rfl⟩, ?_⟩
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      · push Not at hc
        refine ⟨1 / ((n + 1 : ℕ) : ℝ), ⟨n + 1, by omega, rfl⟩, ?_⟩
        push_cast
        rw [abs_of_nonneg (by linarith)]
        linarith
  obtain ⟨x, hx, hxy⟩ := key
  refine Set.mem_add.2 ⟨x, hx, y - x, ?_, by ring⟩
  rw [Set.mem_Icc]
  exact abs_le.1 hxy

lemma cNorm_zero_eq (h : ℝ → ℝ) (a b : ℝ) :
    cNorm 0 h a b = sSup ((fun x => |iteratedDeriv 0 h x|) '' Set.Icc a b) := by
  simp [cNorm, supOn]

lemma abs_le_cNorm_zero (h : ℝ → ℝ) (a b : ℝ) (hc : ContinuousOn (iteratedDeriv 0 h) (Set.Icc a b))
    (x : ℝ) (hx : x ∈ Set.Icc a b) : |iteratedDeriv 0 h x| ≤ cNorm 0 h a b := by
  rw [cNorm_zero_eq]
  exact le_csSup (isCompact_Icc.bddAbove_image hc.abs) ⟨x, hx, rfl⟩

lemma polyc {n : ℕ} (p : ℝ[X]) : ContDiff ℝ n (fun x => p.eval x) := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) p (n : WithTop ℕ∞)
  simpa only [Polynomial.coe_aeval_eq_eval] using this

lemma poly_div_contDiffAt (f g : ℝ[X]) (n : ℕ) (y : ℝ) (hy : g.eval y ≠ 0) :
    ContDiffAt ℝ n (fun x => f.eval x / g.eval x) y :=
  (polyc f).contDiffAt.div (polyc g).contDiffAt hy

lemma poly_div_continuousOn_iteratedDeriv (f g : ℝ[X]) (b : ℝ) (hb : 0 < b)
    (hg0 : ∀ x ∈ Set.Icc 0 b, g.eval x ≠ 0) (m : ℕ) :
    ContinuousOn (iteratedDeriv m (fun x => f.eval x / g.eval x)) (Set.Icc 0 b) := by
  have hcd : ContDiffOn ℝ m (fun x => f.eval x / g.eval x) (Set.Icc 0 b) :=
    fun y hy => (poly_div_contDiffAt f g m y (hg0 y hy)).contDiffWithinAt
  have := hcd.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Icc hb)
  refine this.congr fun y hy => ?_
  exact (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hb)
    (poly_div_contDiffAt f g m y (hg0 y hy)) hy).symm

lemma taylor_step (Ψ : ℝ → ℝ) (x : ℝ) (hx : 0 < x) (n : ℕ)
    (hcd : ∀ y ∈ Set.Icc 0 x, ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ y) (C : ℝ)
    (hC : ∀ y ∈ Set.Icc 0 x, |iteratedDeriv (n + 1) Ψ y| ≤ C) :
    |Ψ x - ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * x ^ k| ≤
      C * x ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  have hu : Set.uIcc (0 : ℝ) x = Set.Icc 0 x := Set.uIcc_of_le hx.le
  have hcdOn : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) Ψ (Set.uIcc 0 x) := by
    rw [hu]; exact fun y hy => (hcd y hy).contDiffWithinAt
  obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx.ne hcdOn
  have hx'I : x' ∈ Set.Icc 0 x := by
    rw [Set.uIoo_of_le hx.le] at hx'
    exact ⟨hx'.1.le, hx'.2.le⟩
  have htay : taylorWithinEval Ψ n (Set.uIcc 0 x) 0 x =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * x ^ k := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
    rw [hu, smul_eq_mul, iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
      ((hcd 0 ⟨le_rfl, hx.le⟩).of_le (by exact_mod_cast (by omega : k ≤ n + 1))) ⟨le_rfl, hx.le⟩]
    rw [sub_zero]; field_simp
  rw [htay] at hrem
  rw [hrem, sub_zero, abs_div, abs_mul, abs_pow, abs_of_pos hx,
    abs_of_pos (by positivity : (0 : ℝ) < ((n + 1).factorial : ℝ))]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (hC x' hx'I) (by positivity)

lemma four_mul_pow_le (m : ℕ) (hm : 1 ≤ m) : (4 : ℝ) * 40 ^ m ≤ 256 ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h : (40 : ℝ) ^ k ≤ 256 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
  have h0 : (0 : ℝ) ≤ 40 ^ k := by positivity
  rw [pow_succ, pow_succ]
  nlinarith

/-- `core_estimate` (s67/PartC.lean) with a real parameter `a`: only `deg f, deg g_L ≤ a` and
`L ≤ a` are used. -/
lemma core_estimate_gen {d L : ℕ} (a : ℝ) (ha1 : 1 ≤ a) (hQa : (L : ℝ) ≤ a)
    (hgdeg : ((gPoly d L).natDegree : ℝ) ≤ a) (f : ℝ[X]) (hf : (f.natDegree : ℝ) ≤ a)
    (F : ℕ → ℝ) (s : ℝ) (T : ℕ) (hT : (T : ℝ) ≤ 2 * a ^ 2)
    (hF : ∀ N : ℕ, T ≤ N → F N = f.eval (1 / (N : ℝ)) / (gPoly d L).eval (1 / (N : ℝ)))
    (hs : ∀ N : ℕ, T ≤ N → |F N| ≤ s) (m : ℕ) (hm : 1 ≤ m) (N : ℕ)
    (hN : 2 * a ^ 2 ≤ (N : ℝ)) :
    |F N - ∑ i ∈ Finset.range m,
        (iteratedDeriv i (fun x => f.eval x / (gPoly d L).eval x) 0 / (i.factorial : ℝ)) /
          (N : ℝ) ^ i| ≤ (4 * a) ^ (4 * m) / (N : ℝ) ^ m * s := by
  set g := gPoly d L with hgdef
  set M : ℕ := ⌈2 * a ^ 2⌉₊ with hMdef
  have hMge : 2 * a ^ 2 ≤ M := Nat.le_ceil _
  have hMle : (M : ℝ) ≤ 4 * a ^ 2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 2 * a ^ 2 by positivity)
    nlinarith
  have ha2 : 1 ≤ a ^ 2 := one_le_pow₀ ha1
  have hMp : (0 : ℝ) < M := by linarith
  have hMpos : 0 < M := by exact_mod_cast hMp
  have h1M : 1 / (M : ℝ) ≤ 1 / (2 * a ^ 2) := one_div_le_one_div_of_le (by positivity) hMge
  have hg : ∀ x : ℝ, 0 ≤ x → x ≤ 1 / (M : ℝ) → 1 / 2 ≤ g.eval x ∧ g.eval x ≤ 1 :=
    fun x h0 h1 => g_bounds a hQa ha1 hgdeg x h0 (h1.trans h1M)
  set Ψ : ℝ → ℝ := fun x => f.eval x / g.eval x with hΨ
  set q : ℕ := ⌊a⌋₊ with hqdef
  have hqa : (q : ℝ) ≤ a := Nat.floor_le (by linarith)
  have hq1 : 1 ≤ q := Nat.le_floor (by simpa using ha1)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hfq : f.natDegree ≤ q := Nat.le_floor hf
  have hgq : g.natDegree ≤ q := Nat.le_floor hgdeg
  have hnQ : ∀ n : ℕ, M ≤ n → T ≤ n := by
    intro n hn
    have : (M : ℝ) ≤ n := by exact_mod_cast hn
    have : (T : ℝ) ≤ n := by linarith
    exact_mod_cast this
  have hs0 : 0 ≤ s := (abs_nonneg _).trans (hs M (hnQ M le_rfl))
  have hb : (0 : ℝ) < 1 / M := by positivity
  have hg0 : ∀ x ∈ Set.Icc (0 : ℝ) (1 / M), g.eval x ≠ 0 := fun x hx =>
    by have := (hg x hx.1 hx.2).1; intro h; rw [h] at this; norm_num at this
  have hfI : ∀ n : ℕ, M ≤ n → |f.eval (1 / (n : ℝ))| ≤ s := by
    intro n hn
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hMp (by exact_mod_cast hn)
    have hx1 : 1 / (n : ℝ) ≤ 1 / (M : ℝ) :=
      one_div_le_one_div_of_le hMp (by exact_mod_cast hn)
    obtain ⟨hg1, hg2⟩ := hg _ (by positivity) hx1
    have hFn := hF n (hnQ n hn)
    have : f.eval (1 / (n : ℝ)) = F n * g.eval (1 / (n : ℝ)) := by
      rw [hFn]; field_simp
    rw [this, abs_mul, abs_of_pos (by linarith : 0 < g.eval (1 / (n : ℝ)))]
    calc |F n| * g.eval (1 / (n : ℝ)) ≤ s * 1 :=
          mul_le_mul (hs n (hnQ n hn)) hg2 (by linarith) hs0
      _ = s := mul_one s
  set I : Set ℝ := {x : ℝ | ∃ n : ℕ, M ≤ n ∧ x = 1 / (n : ℝ)} with hI
  have hIsub : I ⊆ Set.Icc 0 (1 / (M : ℝ)) := by
    rintro x ⟨n, hn, rfl⟩
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hMp (by exact_mod_cast hn)
    exact ⟨by positivity, one_div_le_one_div_of_le hMp (by exact_mod_cast hn)⟩
  have hdens := density_lemma M hMpos q (by linarith) (by nlinarith)
  have h42 := cNorm_le_two_mul_sSup_of_subset_add q f hfq (1 / (M : ℝ)) hb I hIsub hdens
  have hsup : sSup ((fun x => |f.eval x|) '' I) ≤ s := by
    refine csSup_le ⟨_, 1 / (M : ℝ), ⟨M, le_rfl, rfl⟩, rfl⟩ ?_
    rintro _ ⟨x, ⟨n, hn, rfl⟩, rfl⟩
    exact hfI n hn
  have hcf : cNorm 0 (fun x => f.eval x) 0 (1 / (M : ℝ)) ≤ 2 * s := by linarith
  have hfcont : ContinuousOn (iteratedDeriv 0 (fun x => f.eval x)) (Set.Icc 0 (1 / (M : ℝ))) := by
    rw [iteratedDeriv_zero]; exact (polyc (n := 0) f).continuous.continuousOn
  have hΨ4 : cNorm 0 Ψ 0 (1 / (M : ℝ)) ≤ 4 * s := by
    rw [cNorm_zero_eq]
    refine csSup_le ⟨_, 0, ⟨le_rfl, hb.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hg1, hg2⟩ := hg x hx.1 hx.2
    have h1 := abs_le_cNorm_zero (fun x => f.eval x) 0 (1 / (M : ℝ)) hfcont x hx
    rw [iteratedDeriv_zero] at h1 ⊢
    simp only [hΨ]
    rw [abs_div, abs_of_pos (by linarith : 0 < g.eval x), div_le_iff₀ (by linarith)]
    nlinarith [abs_nonneg (f.eval x)]
  have hmain := cNorm_iteratedDeriv_div_le q m f g hfq hgq (1 / (M : ℝ)) hb hg0
  set S := sSup {t | ∃ x ∈ Set.Icc (0 : ℝ) (1 / M), ∃ y ∈ Set.Icc (0 : ℝ) (1 / M),
    t = |g.eval x / g.eval y|} with hS
  have hS0 : 0 ≤ S := by
    refine Real.sSup_nonneg ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩; exact abs_nonneg _
  have hS2 : S ≤ 2 := by
    refine csSup_le ⟨_, 0, ⟨le_rfl, hb.le⟩, 0, ⟨le_rfl, hb.le⟩, rfl⟩ ?_
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨hx1, hx2⟩ := hg x hx.1 hx.2
    obtain ⟨hy1, hy2⟩ := hg y hy.1 hy.2
    rw [abs_div, abs_of_pos (by linarith : 0 < g.eval x), abs_of_pos (by linarith : 0 < g.eval y),
      div_le_iff₀ (by linarith)]
    linarith
  have hbase : 5 * S * (q : ℝ) ^ 2 / (1 / (M : ℝ)) ≤ 40 * a ^ 4 := by
    have e : 5 * S * (q : ℝ) ^ 2 / (1 / (M : ℝ)) = 5 * S * (q : ℝ) ^ 2 * M := by
      field_simp
    rw [e]
    have hq2 : (q : ℝ) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (by linarith) hqa 2
    calc 5 * S * (q : ℝ) ^ 2 * M ≤ 5 * 2 * a ^ 2 * (4 * a ^ 2) := by
          have h1 : 5 * S * (q : ℝ) ^ 2 ≤ 5 * 2 * a ^ 2 :=
            mul_le_mul (by linarith) hq2 (by positivity) (by norm_num)
          exact mul_le_mul h1 hMle hMp.le (by positivity)
      _ = 40 * a ^ 4 := by ring
  have hbase0 : 0 ≤ 5 * S * (q : ℝ) ^ 2 / (1 / (M : ℝ)) := by positivity
  have hC : cNorm 0 (iteratedDeriv m Ψ) 0 (1 / (M : ℝ)) ≤
      m.factorial * (40 * a ^ 4) ^ m * (4 * s) := by
    refine hmain.trans ?_
    have hp := pow_le_pow_left₀ hbase0 hbase m
    have h4 : 0 ≤ cNorm 0 Ψ 0 (1 / (M : ℝ)) := by
      rw [cNorm_zero_eq]; exact Real.sSup_nonneg (by rintro _ ⟨x, _, rfl⟩; exact abs_nonneg _)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hΨ4 h4 (by positivity)
  have hMN : M ≤ N := Nat.ceil_le.2 hN
  have hNQ : T ≤ N := hnQ N hMN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le hMp (by exact_mod_cast hMN)
  have hx : (0 : ℝ) < 1 / (N : ℝ) := by positivity
  have hxM : 1 / (N : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hMp (by exact_mod_cast hMN)
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hT := taylor_step Ψ (1 / (N : ℝ)) hx n
    (fun y hy => poly_div_contDiffAt f g _ y (hg0 y ⟨hy.1, hy.2.trans hxM⟩))
    (cNorm 0 (iteratedDeriv (n + 1) Ψ) 0 (1 / (M : ℝ)))
    (fun y hy => by
      have hyM : y ∈ Set.Icc (0 : ℝ) (1 / M) := ⟨hy.1, hy.2.trans hxM⟩
      have := abs_le_cNorm_zero (iteratedDeriv (n + 1) Ψ) 0 (1 / (M : ℝ))
        (by rw [iteratedDeriv_zero]; exact poly_div_continuousOn_iteratedDeriv f g _ hb hg0 _) y hyM
      rwa [iteratedDeriv_zero] at this)
  have hFN : F N = Ψ (1 / (N : ℝ)) := hF N hNQ
  have hsum : ∑ i ∈ Finset.range (n + 1), iteratedDeriv i Ψ 0 / (i.factorial : ℝ) / (N : ℝ) ^ i =
      ∑ k ∈ Finset.range (n + 1), iteratedDeriv k Ψ 0 / (k.factorial : ℝ) * (1 / (N : ℝ)) ^ k := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_div, inv_pow, div_eq_mul_inv]
  rw [hFN, hsum]
  refine hT.trans ?_
  have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
  have hxp : (1 / (N : ℝ)) ^ (n + 1) = 1 / (N : ℝ) ^ (n + 1) := by rw [one_div, one_div, inv_pow]
  calc cNorm 0 (iteratedDeriv (n + 1) Ψ) 0 (1 / (M : ℝ)) * (1 / (N : ℝ)) ^ (n + 1) /
        ((n + 1).factorial : ℝ)
      ≤ ((n + 1).factorial * (40 * a ^ 4) ^ (n + 1) * (4 * s)) * (1 / (N : ℝ)) ^ (n + 1) /
        ((n + 1).factorial : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hfac.le
        exact mul_le_mul_of_nonneg_right hC (by positivity)
    _ = 4 * 40 ^ (n + 1) * (a ^ 4) ^ (n + 1) / (N : ℝ) ^ (n + 1) * s := by
        rw [hxp, mul_pow]; field_simp
    _ ≤ (4 * a) ^ (4 * (n + 1)) / (N : ℝ) ^ (n + 1) * s := by
        have e : (4 * a) ^ (4 * (n + 1)) = 256 ^ (n + 1) * (a ^ 4) ^ (n + 1) := by
          rw [pow_mul, show (4 * a) ^ 4 = 256 * a ^ 4 by ring, mul_pow]
        rw [e]
        refine mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right ?_ (pow_pos hNp _).le) hs0
        exact mul_le_mul_of_nonneg_right (four_mul_pow_le (n + 1) hm) (by positivity)

/-- `Tⱼ(x/K)` as a polynomial. -/
noncomputable def chebK (K : ℝ) (j : ℕ) : ℝ[X] := (Chebyshev.T ℝ j).comp (Polynomial.C K⁻¹ * X)

lemma sum_range_succ_eq_add_Icc (f : ℕ → ℝ) (q : ℕ) :
    ∑ j ∈ Finset.range (q + 1), f j = f 0 + ∑ j ∈ Finset.Icc 1 q, f j := by
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  rfl

lemma natDegree_chebK_le (K : ℝ) (j : ℕ) : (chebK K j).natDegree ≤ j := by
  unfold chebK
  refine (natDegree_comp_le).trans ?_
  have h1 : (C K⁻¹ * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_C_mul_le _ _).trans ?_
    simp
  simp only [Chebyshev.natDegree_T, Int.natAbs_natCast]
  nlinarith [h1]

lemma supOn_le_of_forall {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) {c : ℝ}
    (h : ∀ x ∈ Set.Icc a b, |f x| ≤ c) : supOn f a b ≤ c := by
  unfold supOn
  apply csSup_le ((Set.nonempty_Icc.mpr hab).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact h x hx

lemma cNorm_chebK_le (K : ℝ) (hK : 0 < K) (j : ℕ) :
    cNorm 0 (fun x => (chebK K j).eval x) (-K) K ≤ 1 := by
  unfold cNorm
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, iteratedDeriv_zero]
  apply supOn_le_of_forall (by linarith)
  intro x hx
  simp only [chebK, eval_comp, eval_mul, eval_C, eval_X]
  apply Chebyshev.abs_eval_T_real_le_one
  rw [abs_mul, abs_inv, abs_of_pos hK, inv_mul_le_iff₀ hK, mul_one]
  exact abs_le.mpr ⟨hx.1, hx.2⟩

lemma cNorm_le_of_abs_le (k : ℕ) (f : ℝ → ℝ) (R : ℝ) (hR : 0 ≤ R) (ε : ℝ)
    (hf : ∀ r ≤ k, ∀ x ∈ Set.Icc (-R) R, |iteratedDeriv r f x| ≤ ε) :
    cNorm k f (-R) R ≤ (k + 1) * ε := by
  unfold cNorm
  calc ∑ j ∈ Finset.range (k + 1), supOn (iteratedDeriv j f) (-R) R
      ≤ ∑ j ∈ Finset.range (k + 1), ε := by
        apply Finset.sum_le_sum
        intro j hj
        exact supOn_le_of_forall (by linarith) (hf j (by simp at hj; omega))
    _ = (k + 1) * ε := by simp

lemma iteratedDeriv_sub_of_contDiff (f g : ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (r : ℕ) :
    iteratedDeriv r (fun x => f x - g x) = fun x => iteratedDeriv r f x - iteratedDeriv r g x := by
  funext x
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  exact iteratedDeriv_fun_sub (hf.contDiffAt.of_le hr) (hg.contDiffAt.of_le hr)

lemma abs_iteratedDeriv_cos_le (i : ℕ) (θ : ℝ) : |iteratedDeriv i Real.cos θ| ≤ 1 := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' i
  · rw [Real.iteratedDeriv_even_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_cos_le_one θ
  · rw [Real.iteratedDeriv_odd_cos]
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, Pi.one_apply, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul]
    exact Real.abs_sin_le_one θ

lemma abs_iteratedDeriv_comp_cos_le (g : ℝ → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (K : ℝ)
    (hK : 0 ≤ K) (r : ℕ) (ε : ℝ)
    (hε : ∀ i ≤ r, ∀ x ∈ Set.Icc (-K) K, |iteratedDeriv i g x| ≤ ε) (θ : ℝ) :
    |iteratedDeriv r (fun θ => g (K * Real.cos θ)) θ| ≤ (r.factorial : ℝ) * ε * (max K 1) ^ r := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun θ => K * Real.cos θ) := contDiff_const.mul Real.contDiff_cos
  have hr : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hmem : K * Real.cos θ ∈ Set.Icc (-K) K := by
    have h1 := Real.neg_one_le_cos θ
    have h2 := Real.cos_le_one θ
    constructor <;> nlinarith
  have key := norm_iteratedFDeriv_comp_le (g := g) (f := fun θ => K * Real.cos θ) (n := r)
    hg hf hr θ (C := ε) (D := max K 1) ?_ ?_
  · rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at key
    exact key
  · intro i hi
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hε i hi _ hmem
  · intro i hi1 _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, iteratedDeriv_const_mul_field,
      abs_mul, abs_of_nonneg hK]
    calc K * |iteratedDeriv i Real.cos θ| ≤ K * 1 :=
          mul_le_mul_of_nonneg_left (abs_iteratedDeriv_cos_le i θ) hK
      _ ≤ max K 1 := by rw [mul_one]; exact le_max_left _ _
      _ ≤ max K 1 ^ i := le_self_pow₀ (le_max_right _ _) (by omega)

lemma lpNormCircle_le_add (β : ℝ) (hβ : 1 < β) (F G : ℝ → ℝ) (hF : Continuous F)
    (hG : Continuous G) (δ : ℝ) (hδ : ∀ θ, |F θ - G θ| ≤ δ) :
    lpNormCircle β F ≤ lpNormCircle β G + (2 * Real.pi + 1) * δ := by
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hδ 0)
  set μ := MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))
  set p := ENNReal.ofReal β
  have hp1 : 1 ≤ p := by
    rw [show (1 : ENNReal) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hβ.le
  have hptr : p.toReal = β := ENNReal.toReal_ofReal (by linarith)
  have hμ : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    simp [μ, Real.volume_Icc]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hbound : ∀ (H : ℝ → ℝ) (C : ℝ), 0 ≤ C → (∀ x ∈ Set.Icc 0 (2 * Real.pi), ‖H x‖ ≤ C) →
      MeasureTheory.eLpNorm H p μ ≤ ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * C) := by
    intro H C hC hH
    refine (MeasureTheory.eLpNorm_le_of_ae_bound
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hH)).trans (le_of_eq ?_)
    rw [hμ, hptr, ENNReal.ofReal_rpow_of_nonneg hpi (by positivity), ← ENNReal.ofReal_mul
      (by positivity)]
  have hFG : MeasureTheory.eLpNorm (fun x => F x - G x) p μ ≤
      ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * δ) :=
    hbound _ δ hδ0 (fun x _ => by rw [Real.norm_eq_abs]; exact hδ x)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := G)
    (s := Set.Icc 0 (2 * Real.pi)) hG.continuousOn
  have hGfin : MeasureTheory.eLpNorm G p μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hbound G (max M 0) (le_max_right _ _) (fun x hx => (hM x hx).trans (le_max_left _ _)))
  have htri : MeasureTheory.eLpNorm F p μ ≤
      MeasureTheory.eLpNorm G p μ + MeasureTheory.eLpNorm (fun x => F x - G x) p μ := by
    have := MeasureTheory.eLpNorm_add_le (μ := μ) (p := p) (f := G) (g := fun x => F x - G x)
      hG.aestronglyMeasurable (hF.sub hG).aestronglyMeasurable hp1
    convert this using 2
    funext x; simp
  have hsum : MeasureTheory.eLpNorm F p μ ≤
      MeasureTheory.eLpNorm G p μ + ENNReal.ofReal ((2 * Real.pi) ^ β⁻¹ * δ) :=
    htri.trans (add_le_add_right hFG _)
  unfold lpNormCircle
  have h1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hGfin, ENNReal.ofReal_ne_top⟩) hsum
  rw [ENNReal.toReal_add hGfin ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity)] at h1
  refine h1.trans (add_le_add_right ?_ _)
  apply mul_le_mul_of_nonneg_right _ hδ0
  have hpi1 : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc (2 * Real.pi) ^ β⁻¹ ≤ (2 * Real.pi) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hpi1 (inv_le_one_of_one_le₀ hβ.le)
    _ ≤ 2 * Real.pi + 1 := by rw [Real.rpow_one]; linarith

lemma natDegree_chebK (K : ℝ) (hK : 0 < K) (j : ℕ) : (chebK K j).natDegree = j := by
  unfold chebK
  rw [natDegree_comp, natDegree_C_mul_X _ (inv_ne_zero hK.ne')]
  simp

lemma chebK_coeff_ne_zero (K : ℝ) (hK : 0 < K) (j : ℕ) : (chebK K j).coeff j ≠ 0 := by
  have h := natDegree_chebK K hK j
  have hne : chebK K j ≠ 0 := by
    intro h0
    have h1 : (chebK K j).leadingCoeff ≠ 0 := by
      unfold chebK
      rw [leadingCoeff_comp (by rw [natDegree_C_mul_X _ (inv_ne_zero hK.ne')]; norm_num)]
      simp [hK.ne']
    rw [h0] at h1
    simp at h1
  have := leadingCoeff_ne_zero.mpr hne
  rwa [leadingCoeff, h] at this

lemma exists_chebyshev_expansion_aux (K : ℝ) (hK : 0 < K) (m : ℕ) :
    ∀ p : ℝ[X], p.natDegree ≤ m →
      ∃ a : ℕ → ℝ, p = ∑ j ∈ Finset.range (m + 1), Polynomial.C (a j) * chebK K j := by
  induction m with
  | zero =>
    intro p hp
    refine ⟨fun _ => p.coeff 0, ?_⟩
    rw [eq_C_of_natDegree_le_zero hp]
    simp [chebK]
  | succ m ih =>
    intro p hp
    set c := p.coeff (m + 1) / (chebK K (m + 1)).coeff (m + 1)
    have hc : c * (chebK K (m + 1)).coeff (m + 1) = p.coeff (m + 1) :=
      div_mul_cancel₀ _ (chebK_coeff_ne_zero K hK (m + 1))
    have hdeg : (p - Polynomial.C c * chebK K (m + 1)).natDegree ≤ m := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [coeff_sub, coeff_C_mul]
      rcases Nat.lt_or_ge (m + 1) N with h | h
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h),
          coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_chebK_le K (m + 1)) h)]
        simp
      · obtain rfl : N = m + 1 := by omega
        rw [hc]; simp
    obtain ⟨a, ha⟩ := ih _ hdeg
    refine ⟨fun j => if j = m + 1 then c else a j, ?_⟩
    rw [Finset.sum_range_succ]
    simp only [if_true]
    have : ∑ j ∈ Finset.range (m + 1),
        Polynomial.C (if j = m + 1 then c else a j) * chebK K j =
        ∑ j ∈ Finset.range (m + 1), Polynomial.C (a j) * chebK K j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp at hj
      rw [if_neg (by omega)]
    rw [this, ← ha]
    ring

lemma exists_chebyshev_expansion (p : ℝ[X]) (K : ℝ) (hK : 0 < K) :
    ∃ a : ℕ → ℝ,
      (∀ x : ℝ, p.eval x = ∑ j ∈ Finset.range (p.natDegree + 1),
        a j * (Chebyshev.T ℝ j).eval (x / K)) ∧
      p = ∑ j ∈ Finset.range (p.natDegree + 1), Polynomial.C (a j) * chebK K j := by
  obtain ⟨a, ha⟩ := exists_chebyshev_expansion_aux K hK p.natDegree p le_rfl
  refine ⟨a, ?_, ha⟩
  intro x
  conv_lhs => rw [ha]
  rw [eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j _
  simp [chebK, eval_comp, div_eq_inv_mul]

lemma exists_antiderivative (q : ℝ[X]) : ∃ Q : ℝ[X], derivative Q = q := by
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1),
    Polynomial.C (q.coeff i / ((i : ℝ) + 1)) * X ^ (i + 1), ?_⟩
  rw [derivative_sum]
  conv_rhs => rw [as_sum_range_C_mul_X_pow q]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_C_mul_X_pow]
  congr 2
  · push_cast
    field_simp

lemma exists_poly_approx (h : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h) (k : ℕ) (R ε : ℝ)
    (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ r ≤ k, ∀ x ∈ Set.Icc (-R) R,
      |iteratedDeriv r h x - iteratedDeriv r (fun x => p.eval x) x| ≤ ε := by
  induction k generalizing h ε with
  | zero =>
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R h
      hh.continuous.continuousOn ε hε
    refine ⟨p, fun r hr x hx => ?_⟩
    obtain rfl : r = 0 := by omega
    simp only [iteratedDeriv_zero]
    rw [abs_sub_comm]
    exact (hp x hx).le
  | succ k ih =>
    rcases lt_or_ge R 0 with hR | hR
    · refine ⟨0, fun r _ x hx => ?_⟩
      exfalso
      have := hx.1.trans hx.2
      linarith
    have hR1 : 0 < 2 * R + 1 := by linarith
    set ε' := ε / (2 * R + 1) with hε'
    have hε'pos : 0 < ε' := div_pos hε hR1
    have hε'mul : ε' * (2 * R + 1) = ε := div_mul_cancel₀ _ hR1.ne'
    have hε'le : ε' ≤ ε := by nlinarith
    obtain ⟨hdiff, hd⟩ := contDiff_infty_iff_deriv.mp hh
    obtain ⟨q, hq⟩ := ih (deriv h) hd ε' hε'pos
    obtain ⟨Q, hQ⟩ := exists_antiderivative q
    set p := Q + Polynomial.C (h (-R) - Q.eval (-R)) with hpdef
    have hpd : derivative p = q := by
      rw [hpdef, derivative_add, derivative_C, add_zero, hQ]
    have hderiv : deriv (fun x => p.eval x) = fun x => q.eval x := by
      funext x
      rw [Polynomial.deriv, hpd]
    refine ⟨p, fun r hr x hx => ?_⟩
    rcases r with _ | s
    · simp only [iteratedDeriv_zero]
      have hg0 : h (-R) - p.eval (-R) = 0 := by
        rw [hpdef]; simp
      have hmem : (-R) ∈ Set.Icc (-R) R := ⟨le_rfl, by linarith⟩
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (f := fun y => h y - p.eval y) (s := Set.Icc (-R) R) (C := ε')
        (fun y _ => (hdiff y).sub p.differentiableAt) ?_ (convex_Icc _ _) hmem hx
      · simp only [hg0, sub_zero, Real.norm_eq_abs] at hmvt
        have hxR : |x - -R| ≤ 2 * R := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
        calc |h x - eval x p| ≤ ε' * |x - -R| := hmvt
          _ ≤ ε' * (2 * R) := mul_le_mul_of_nonneg_left hxR hε'pos.le
          _ ≤ ε := by nlinarith
      · intro y hy
        rw [deriv_fun_sub (hdiff y) p.differentiableAt, Polynomial.deriv, hpd, Real.norm_eq_abs]
        have := hq 0 (Nat.zero_le _) y hy
        simpa only [iteratedDeriv_zero] using this
    · rw [iteratedDeriv_succ', iteratedDeriv_succ', hderiv]
      exact (hq s (by omega) x hx).trans hε'le

/-! ## The abstract family -/
lemma HasExp.congr {F G c : ℕ → ℝ} (hF : HasExp F c) (h : ∀ᶠ N in atTop, F N = G N) :
    HasExp G c := by
  intro m
  obtain ⟨C, hC⟩ := hF m
  exact ⟨C, by filter_upwards [hC, h] with N h1 h2; rwa [← h2]⟩

lemma HasExp.add {F G c e : ℕ → ℝ} (hF : HasExp F c) (hG : HasExp G e) :
    HasExp (fun N => F N + G N) (fun i => c i + e i) := by
  intro m
  obtain ⟨C₁, h₁⟩ := hF m
  obtain ⟨C₂, h₂⟩ := hG m
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂] with N hN₁ hN₂
  have : F N + G N - ∑ i ∈ Finset.range m, (c i + e i) / (N : ℝ) ^ i =
      (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i) +
        (G N - ∑ i ∈ Finset.range m, e i / (N : ℝ) ^ i) := by
    simp only [add_div, Finset.sum_add_distrib]; ring
  rw [this, add_div]
  exact (abs_add_le _ _).trans (add_le_add hN₁ hN₂)

lemma HasExp.const_mul {F c : ℕ → ℝ} (hF : HasExp F c) (r : ℝ) :
    HasExp (fun N => r * F N) (fun i => r * c i) := by
  intro m
  obtain ⟨C, h⟩ := hF m
  refine ⟨|r| * C, ?_⟩
  filter_upwards [h] with N hN
  have : r * F N - ∑ i ∈ Finset.range m, r * c i / (N : ℝ) ^ i =
      r * (F N - ∑ i ∈ Finset.range m, c i / (N : ℝ) ^ i) := by
    rw [mul_sub, Finset.mul_sum]; simp only [mul_div_assoc]
  rw [this, abs_mul, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hN (abs_nonneg r)

lemma cNorm_zero_eq_supOn (f : ℝ → ℝ) (a b : ℝ) : cNorm 0 f a b = supOn f a b := by
  simp [cNorm]

lemma natDegree_gPoly_le (d L : ℕ) : ((gPoly d L).natDegree : ℝ) ≤ L * (1 + Real.log d) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp [gPoly]
  · exact (exists_uniformExp_trN_wordEval_eq_div d L hL [] (by simp)).1

lemma isLinearMap_sum (φ : ℝ[X] → ℝ) (hφ : IsLinearMap ℝ φ) (s : Finset ℕ) (a : ℕ → ℝ)
    (g : ℕ → ℝ[X]) :
    φ (∑ j ∈ s, Polynomial.C (a j) * g j) = ∑ j ∈ s, a j * φ (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hφ.map_zero
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, hφ.map_add, ih, Polynomial.C_mul',
      hφ.map_smul, smul_eq_mul]

lemma eval_chebK_zero (K : ℝ) : (fun x => (chebK K 0).eval x) = fun _ : ℝ => (1 : ℝ) := by
  funext x; simp [chebK]

/-- The hypotheses of `abstract_master` other than `m` and the constant function. -/
structure AHyp (d Q₀ N₁ : ℕ) (K s : ℝ) (E : ℕ → (ℝ → ℝ) → ℝ) : Prop where
  hQ₀ : 1 ≤ Q₀
  hN₁ : N₁ ≤ Q₀
  hK : 0 < K
  hs : 0 ≤ s
  lin : ∀ N : ℕ, N₁ ≤ N → 1 ≤ N → ∀ f g : ℝ → ℝ, Continuous f → Continuous g → ∀ c : ℝ,
    E N (fun x => f x + c * g x) = E N f + c * E N g
  bd : ∀ N : ℕ, N₁ ≤ N → 1 ≤ N → ∀ f : ℝ → ℝ, Continuous f → |E N f| ≤ s * supOn f (-K) K
  rat : ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
    ∃ (L : ℕ) (f : ℝ[X]), L ≤ q * Q₀ ∧
      (f.natDegree : ℝ) ≤ ((q * Q₀ : ℕ) : ℝ) * (1 + Real.log d) ∧
      ∀ N : ℕ, N₁ ≤ N → q * Q₀ ≤ N →
        E N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / (gPoly d L).eval (1 / (N : ℝ))

/-- The expansion coefficients on polynomials. -/
def nuP (E : ℕ → (ℝ → ℝ) → ℝ) (i : ℕ) (h : ℝ[X]) : ℝ :=
  asympCoeff (fun N => E N (fun x => h.eval x)) i

lemma hasExp_const (E : ℕ → (ℝ → ℝ) → ℝ) (N₁ m : ℕ) (e : ℕ → ℝ)
    (he : ∀ N : ℕ, N₁ ≤ N → 1 ≤ N → E N (fun _ => 1) = ∑ i ∈ Finset.range m, e i / (N : ℝ) ^ i) :
    HasExp (fun N => E N (fun _ => 1)) (fun i => if i < m then e i else 0) := by
  intro m'
  set e' : ℕ → ℝ := fun i => if i < m then e i else 0 with he'
  refine ⟨∑ i ∈ Finset.Ico m' (m' + m), |e' i|, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₁ 1)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNp : (0 : ℝ) < N := by linarith
  have h1 : E N (fun _ => 1) = ∑ i ∈ Finset.range (m' + m), e' i / (N : ℝ) ^ i := by
    rw [he N (le_trans (le_max_left _ _) hN) hN1, add_comm m' m, Finset.sum_range_add]
    have h0 : ∑ x ∈ Finset.range m', e' (m + x) / (N : ℝ) ^ (m + x) = 0 :=
      Finset.sum_eq_zero fun i _ => by simp [he']
    rw [h0, add_zero]
    exact Finset.sum_congr rfl fun i hi => by
      simp [he', Finset.mem_range.mp hi]
  rw [h1, ← Finset.sum_range_add_sum_Ico _ (Nat.le_add_right m' m), add_sub_cancel_left,
    Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have him : m' ≤ i := (Finset.mem_Ico.mp hi).1
  rw [abs_div, abs_of_pos (pow_pos hNp i)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hNp m')
    (pow_le_pow_right₀ hNr him)

end StrongConv.Q202L1.PartS1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
noncomputable section
namespace StrongConv.Q202L1.PartS1
open StrongConv StrongConv.Q202L1
variable {d Q₀ N₁ : ℕ} {K s : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ}
lemma AHyp.exp_data (H : AHyp d Q₀ N₁ K s E) (q : ℕ) (hq : 1 ≤ q) (h : ℝ[X])
    (hh : h.natDegree ≤ q) :
    HasExp (fun N => E N (fun x => h.eval x)) (fun i => nuP E i h) ∧
    ∀ m : ℕ, 1 ≤ m → ∀ N : ℕ, 2 * ((q : ℝ) * Q₀ * (1 + Real.log d)) ^ 2 ≤ (N : ℝ) →
      |E N (fun x => h.eval x) - ∑ i ∈ Finset.range m, nuP E i h / (N : ℝ) ^ i| ≤
        (4 * ((q : ℝ) * Q₀ * (1 + Real.log d))) ^ (4 * m) / (N : ℝ) ^ m *
          (s * supOn (fun x => h.eval x) (-K) K) := by
  obtain ⟨L, f, hLq, hf, hF⟩ := H.rat q hq h hh
  set a : ℝ := (q : ℝ) * Q₀ * (1 + Real.log d) with ha
  set S := s * supOn (fun x => h.eval x) (-K) K with hS
  have hlog : (0 : ℝ) ≤ Real.log d := Real.log_natCast_nonneg d
  have hQ0 := H.hQ₀
  have hQ : 1 ≤ q * Q₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hQ1 : (1 : ℝ) ≤ ((q * Q₀ : ℕ) : ℝ) := by exact_mod_cast hQ
  have haf : ((q * Q₀ : ℕ) : ℝ) * (1 + Real.log d) = a := by rw [ha]; push_cast; ring
  have hqQ : ((q * Q₀ : ℕ) : ℝ) ≤ a := by
    rw [← haf]; nlinarith
  have ha1 : 1 ≤ a := hQ1.trans hqQ
  have hLa : (L : ℝ) ≤ a := (by exact_mod_cast hLq : (L : ℝ) ≤ ((q * Q₀ : ℕ) : ℝ)).trans hqQ
  have hgdeg : ((gPoly d L).natDegree : ℝ) ≤ a := by
    refine (natDegree_gPoly_le d L).trans ?_
    rw [← haf]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hLq) (by linarith)
  have hfa : (f.natDegree : ℝ) ≤ a := haf ▸ hf
  have hT : ((q * Q₀ : ℕ) : ℝ) ≤ 2 * a ^ 2 := by nlinarith
  have hN₁T : ∀ N, q * Q₀ ≤ N → N₁ ≤ N := by
    intro N hN
    have := H.hN₁
    have : Q₀ ≤ q * Q₀ := Nat.le_mul_of_pos_left Q₀ (by omega)
    omega
  have hbd : ∀ N : ℕ, q * Q₀ ≤ N → |E N (fun x => h.eval x)| ≤ S := fun N hN =>
    H.bd N (hN₁T N hN) (le_trans hQ hN) _ h.continuous
  have hcore := core_estimate_gen a ha1 hLa hgdeg f hfa (fun N => E N (fun x => h.eval x)) S
    (q * Q₀) hT (fun N hN => hF N (hN₁T N hN) hN) hbd
  set c : ℕ → ℝ := fun i =>
    iteratedDeriv i (fun x => f.eval x / (gPoly d L).eval x) 0 / (i.factorial : ℝ) with hc
  have hexp : HasExp (fun N => E N (fun x => h.eval x)) c := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · refine ⟨S, ?_⟩
      filter_upwards [eventually_ge_atTop (q * Q₀)] with N hN
      simpa using hbd N hN
    · refine ⟨(4 * a) ^ (4 * m) * S, ?_⟩
      obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * a ^ 2)
      filter_upwards [eventually_ge_atTop N₀] with N hN
      have := hcore m hm N (hN₀.trans (by exact_mod_cast hN))
      rwa [div_mul_eq_mul_div] at this
  have hnu : ∀ i, nuP E i h = c i := fun i => hexp.asympCoeff_eq i
  refine ⟨?_, ?_⟩
  · have : (fun i => nuP E i h) = c := funext hnu
    rw [this]; exact hexp
  · intro m hm N hN
    simpa [hnu] using hcore m hm N hN

lemma AHyp.abs_nu_le (H : AHyp d Q₀ N₁ K s E) (m q : ℕ) (hq : 1 ≤ q) (h : ℝ[X])
    (hh : h.natDegree ≤ q) :
    |nuP E m h| ≤ (4 * ((q : ℝ) * Q₀ * (1 + Real.log d))) ^ (4 * m) *
      (s * supOn (fun x => h.eval x) (-K) K) := by
  obtain ⟨hexp, hbound⟩ := H.exp_data q hq h hh
  set S := s * supOn (fun x => h.eval x) (-K) K with hS
  have ht := hexp.tendsto m
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [pow_zero, Finset.range_zero, Finset.sum_empty, sub_zero, one_mul] at ht
    have hle : ∀ᶠ N : ℕ in atTop, |E N (fun x => h.eval x)| ≤ S := by
      filter_upwards [eventually_ge_atTop (max N₁ 1)] with N hN
      exact H.bd N (le_trans (le_max_left _ _) hN) (le_trans (le_max_right _ _) hN) _
        h.continuous
    have := le_of_tendsto ht.abs (hle.mono fun N hN => hN)
    simpa using this
  · obtain ⟨N₀, hN₀⟩ := exists_nat_ge (2 * ((q : ℝ) * Q₀ * (1 + Real.log d)) ^ 2)
    have hle : ∀ᶠ N : ℕ in atTop, |(N : ℝ) ^ m * (E N (fun x => h.eval x) -
        ∑ i ∈ Finset.range m, nuP E i h / (N : ℝ) ^ i)| ≤
        (4 * ((q : ℝ) * Q₀ * (1 + Real.log d))) ^ (4 * m) * S := by
      filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
      have hN1 : (0 : ℝ) < (N : ℝ) := by
        have : 1 ≤ N := le_trans (le_max_right _ _) hN
        exact_mod_cast this
      have := hbound m hm N (hN₀.trans (by exact_mod_cast le_trans (le_max_left _ _) hN))
      rw [abs_mul, abs_of_pos (pow_pos hN1 m)]
      calc (N : ℝ) ^ m * |_| ≤ (N : ℝ) ^ m * ((4 * ((q : ℝ) * Q₀ * (1 + Real.log d))) ^ (4 * m) /
            (N : ℝ) ^ m * S) := mul_le_mul_of_nonneg_left this (pow_pos hN1 m).le
        _ = _ := by field_simp
    have := le_of_tendsto ht.abs hle
    simpa using this

lemma AHyp.master (H : AHyp d Q₀ N₁ K s E) (N m q : ℕ) (hN₁ : N₁ ≤ N) (hN : 1 ≤ N)
    (hm : 1 ≤ m) (hq : 1 ≤ q) (h : ℝ[X]) (hh : h.natDegree ≤ q) :
    |E N (fun x => h.eval x) - ∑ i ∈ Finset.range m, nuP E i h / (N : ℝ) ^ i| ≤
      (4 * ((q : ℝ) * Q₀ * (1 + Real.log d))) ^ (4 * m) / (N : ℝ) ^ m *
        (s * supOn (fun x => h.eval x) (-K) K) := by
  obtain ⟨hexp, hbound⟩ := H.exp_data q hq h hh
  set S := s * supOn (fun x => h.eval x) (-K) K with hS
  set a : ℝ := (q : ℝ) * Q₀ * (1 + Real.log d) with ha
  by_cases hM : 2 * a ^ 2 ≤ (N : ℝ)
  · exact hbound m hm N hM
  · push Not at hM
    have hL : (0 : ℝ) ≤ Real.log d := Real.log_natCast_nonneg d
    have ha1 : (1 : ℝ) ≤ a := by
      have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
      have h2 : (1 : ℝ) ≤ Q₀ := by exact_mod_cast H.hQ₀
      rw [ha]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ q - 1) (by linarith : (0:ℝ) ≤ Q₀ - 1)]
    have hs0 : |E N (fun x => h.eval x)| ≤ S := H.bd N hN₁ hN _ h.continuous
    have harith := small_N_arith a ha1 m hm N hN hM
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hs_nn : 0 ≤ S := (abs_nonneg _).trans hs0
    calc |E N (fun x => h.eval x) - ∑ i ∈ Finset.range m, nuP E i h / (N : ℝ) ^ i|
        ≤ |E N (fun x => h.eval x)| + ∑ i ∈ Finset.range m, |nuP E i h| / (N : ℝ) ^ i := by
          refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [abs_div, abs_of_pos (pow_pos hNpos i)]
      _ ≤ S + ∑ i ∈ Finset.range m, (4 * a) ^ (4 * i) * S / (N : ℝ) ^ i := by
          refine add_le_add hs0 (Finset.sum_le_sum fun i _ => ?_)
          exact div_le_div_of_nonneg_right (H.abs_nu_le i q hq h hh) (pow_pos hNpos i).le
      _ = S * (1 + ∑ i ∈ Finset.range m, (4 * a) ^ (4 * i) / (N : ℝ) ^ i) := by
          rw [mul_add S 1, mul_one, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ S * ((4 * a) ^ (4 * m) / (N : ℝ) ^ m) := mul_le_mul_of_nonneg_left harith hs_nn
      _ = _ := by ring

lemma AHyp.nuP_add (H : AHyp d Q₀ N₁ K s E) (i : ℕ) (h₁ h₂ : ℝ[X]) (r : ℝ) :
    nuP E i (h₁ + Polynomial.C r * h₂) = nuP E i h₁ + r * nuP E i h₂ := by
  set q := max (max h₁.natDegree h₂.natDegree) 1 with hq
  have hq1 : 1 ≤ q := le_max_right _ _
  have hh₁ : h₁.natDegree ≤ q := (le_max_left _ _).trans (le_max_left _ _)
  have hh₂ : h₂.natDegree ≤ q := (le_max_right _ _).trans (le_max_left _ _)
  have e₁ := (H.exp_data q hq1 h₁ hh₁).1
  have e₂ := (H.exp_data q hq1 h₂ hh₂).1
  have e₄ := e₁.add (e₂.const_mul r)
  have e₅ : HasExp (fun N => E N (fun x => (h₁ + Polynomial.C r * h₂).eval x))
      (fun i => nuP E i h₁ + r * nuP E i h₂) := by
    refine e₄.congr ?_
    filter_upwards [eventually_ge_atTop (max N₁ 1)] with N hN
    have hfun : (fun x => (h₁ + Polynomial.C r * h₂).eval x) =
        fun x => (fun x => h₁.eval x) x + r * (fun x => h₂.eval x) x := by
      funext x; simp [eval_add, eval_mul, eval_C]
    rw [hfun, H.lin N (le_trans (le_max_left _ _) hN) (le_trans (le_max_right _ _) hN) _ _
      h₁.continuous h₂.continuous r]
  exact e₅.asympCoeff_eq i

lemma AHyp.isLinearMap_nuP (H : AHyp d Q₀ N₁ K s E) (i : ℕ) : IsLinearMap ℝ (nuP E i) := by
  have hz : nuP E i 0 = 0 := by
    have := H.nuP_add i 0 0 1
    rw [mul_zero, add_zero, one_mul] at this
    linarith
  refine ⟨fun h₁ h₂ => ?_, fun r h => ?_⟩
  · have := H.nuP_add i h₁ h₂ 1
    rwa [Polynomial.C_1, one_mul, one_mul] at this
  · have := H.nuP_add i 0 h r
    rw [zero_add, hz, zero_add] at this
    rw [Polynomial.smul_eq_C_mul, this, smul_eq_mul]

lemma AHyp.exists_csExt (H : AHyp d Q₀ N₁ K s E) (i : ℕ) :
    ∃ μ : smoothFun →ₗ[ℝ] ℝ, IsCSDistribution μ ∧ ∀ h : ℝ[X], μ (polyFun h) = nuP E i h := by
  let ν : ℝ[X] →ₗ[ℝ] ℝ := IsLinearMap.mk' (nuP E i) (H.isLinearMap_nuP i)
  have hL : 0 ≤ 1 + Real.log d := by
    have := Real.log_natCast_nonneg d
    linarith
  have hs := H.hs
  have h1 : ∃ c m K : ℝ, 0 ≤ c ∧ 0 ≤ m ∧ 0 ≤ K ∧ ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X],
      h.natDegree ≤ q → |ν h| ≤ c * (q : ℝ) ^ m * cNorm 0 (fun x => h.eval x) (-K) K := by
    refine ⟨(4 * ((Q₀ : ℝ) * (1 + Real.log d))) ^ (4 * i) * s, ((4 * i : ℕ) : ℝ), K,
      by positivity, by positivity, H.hK.le, fun q hq h hh => ?_⟩
    have := H.abs_nu_le i q hq h hh
    rw [Real.rpow_natCast, cNorm_zero_eq_supOn]
    show |nuP E i h| ≤ _
    refine this.trans (le_of_eq ?_)
    rw [show (4 * ((q : ℝ) * Q₀ * (1 + Real.log d))) = (4 * ((Q₀ : ℝ) * (1 + Real.log d))) * q
      by ring, mul_pow]
    ring
  obtain ⟨μ, hμ, -⟩ := ((tfae_extends_csDistribution ν).out 0 2).mp h1
  exact ⟨μ, hμ.1, fun h => by rw [hμ.2 h]; rfl⟩

lemma AHyp.E_zero (H : AHyp d Q₀ N₁ K s E) (N : ℕ) (hN₁ : N₁ ≤ N) (hN : 1 ≤ N) :
    E N (fun _ => 0) = 0 := by
  have := H.lin N hN₁ hN (fun _ => 0) (fun _ => 0) continuous_const continuous_const 1
  simp only [mul_zero, add_zero, one_mul] at this
  linarith

lemma AHyp.E_sum (H : AHyp d Q₀ N₁ K s E) (N : ℕ) (hN₁ : N₁ ≤ N) (hN : 1 ≤ N)
    (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℝ[X]) :
    E N (fun x => (∑ j ∈ S, Polynomial.C (a j) * g j).eval x) =
      ∑ j ∈ S, a j * E N (fun x => (g j).eval x) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, eval_zero]
    exact H.E_zero N hN₁ hN
  | insert j S hj ih =>
    have hfun : (fun x => (∑ j ∈ insert j S, Polynomial.C (a j) * g j).eval x) =
        fun x => (fun x => (∑ j ∈ S, Polynomial.C (a j) * g j).eval x) x +
          a j * (fun x => (g j).eval x) x := by
      funext x
      simp only [Finset.sum_insert hj, eval_add, eval_mul, eval_C]
      ring
    rw [hfun, H.lin N hN₁ hN _ _ (Polynomial.continuous _) (Polynomial.continuous _) (a j), ih,
      Finset.sum_insert hj]
    ring

end StrongConv.Q202L1.PartS1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
noncomputable section
namespace StrongConv.Q202L1.PartS1
open StrongConv StrongConv.Q202L1
/-- The constant of Lemma 4.4. -/
noncomputable def Czyg : ℝ := Classical.choose abs_coeff_zero_le_and_sum_le_lpNormCircle

lemma Czyg_spec : ∀ (q : ℕ) (a : ℕ → ℝ) (K : ℝ), 0 < K →
      |a 0| ≤ cNorm 0 (fun x => ∑ j ∈ Finset.range (q + 1),
          a j * (Chebyshev.T ℝ j).eval (x / K)) (-K) K ∧
      ∀ (m : ℕ) (β : ℝ), 1 < β →
        ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ m * |a j| ≤
          Czyg * conjExp β * lpNormCircle β (iteratedDeriv (m + 1) (fun θ =>
            ∑ j ∈ Finset.range (q + 1), a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K))) :=
  Classical.choose_spec abs_coeff_zero_le_and_sum_le_lpNormCircle

lemma lpNormCircle_nonneg (β : ℝ) (F : ℝ → ℝ) : 0 ≤ lpNormCircle β F :=
  ENNReal.toReal_nonneg

lemma conjExp_pos (β : ℝ) (hβ : 1 < β) : 0 < conjExp β := by
  unfold conjExp
  have : 1 / β < 1 := by rw [div_lt_one (by linarith)]; exact hβ
  exact inv_pos.mpr (by linarith)

end StrongConv.Q202L1.PartS1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
noncomputable section
namespace StrongConv.Q202L1.PartS1
open StrongConv StrongConv.Q202L1
variable {d Q₀ N₁ : ℕ} {K s : ℝ} {E : ℕ → (ℝ → ℝ) → ℝ}
/-- The master inequality for polynomial test functions (pp. 22–23); the constant term is exact. -/
theorem AHyp.poly_master (H : AHyp d Q₀ N₁ K s E) (m : ℕ) (e : ℕ → ℝ)
    (he : ∀ N : ℕ, N₁ ≤ N → 1 ≤ N →
      E N (fun _ => 1) = ∑ i ∈ Finset.range m, e i / (N : ℝ) ^ i)
    (p : ℝ[X]) (N : ℕ) (hN₁ : N₁ ≤ N) (hN : 1 ≤ N) (hm : 1 ≤ m) (β : ℝ) (hβ : 1 < β) :
    |E N (fun x => p.eval x) - ∑ i ∈ Finset.range m, nuP E i p / (N : ℝ) ^ i| ≤
      max Czyg 0 * s * (4 * (Q₀ : ℝ) * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * conjExp β *
        lpNormCircle β (iteratedDeriv (4 * m + 1) (fun θ => p.eval (K * Real.cos θ))) := by
  have hK := H.hK
  have hs := H.hs
  have hL : (0 : ℝ) ≤ Real.log d := Real.log_natCast_nonneg d
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hβs := conjExp_pos β hβ
  set lp := lpNormCircle β (iteratedDeriv (4 * m + 1) (fun θ => p.eval (K * Real.cos θ)))
  have hlp : 0 ≤ lp := lpNormCircle_nonneg _ _
  obtain ⟨a, ha_eval, ha_poly⟩ := exists_chebyshev_expansion p K hK
  set q := p.natDegree
  set Er : ℕ → ℝ := fun j => E N (fun x => (chebK K j).eval x) -
    ∑ i ∈ Finset.range m, nuP E i (chebK K j) / (N : ℝ) ^ i with hEr
  have hexp : E N (fun x => p.eval x) =
      ∑ j ∈ Finset.range (q + 1), a j * E N (fun x => (chebK K j).eval x) := by
    rw [← H.E_sum N hN₁ hN _ a (chebK K), ← ha_poly]
  have hnu : ∀ i, nuP E i p = ∑ j ∈ Finset.range (q + 1), a j * nuP E i (chebK K j) := by
    intro i
    conv_lhs => rw [ha_poly]
    exact isLinearMap_sum _ (H.isLinearMap_nuP i) _ a (chebK K)
  have key : E N (fun x => p.eval x) - ∑ i ∈ Finset.range m, nuP E i p / (N : ℝ) ^ i =
      ∑ j ∈ Finset.range (q + 1), a j * Er j := by
    rw [hexp]
    simp only [hnu, hEr, mul_sub, Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [key, sum_range_succ_eq_add_Icc]
  -- the term j = 0 vanishes
  have hE0 : Er 0 = 0 := by
    have hc := (hasExp_const E N₁ m e he)
    have hnu0 : ∀ i ∈ Finset.range m, nuP E i (chebK K 0) = e i := by
      intro i hi
      have := hc.asympCoeff_eq i
      simp only [Finset.mem_range.mp hi, if_true] at this
      unfold nuP
      rw [eval_chebK_zero]
      exact this
    simp only [hEr]
    rw [eval_chebK_zero, he N hN₁ hN, sub_eq_zero]
    exact Finset.sum_congr rfl fun i hi => by rw [hnu0 i hi]
  -- the terms j ≥ 1
  have hEj : ∀ j ∈ Finset.Icc 1 q, |a j * Er j| ≤
      (4 * (Q₀ : ℝ) * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * s * ((j : ℝ) ^ (4 * m) * |a j|) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have h1 := H.master N m j hN₁ hN hm hj1 (chebK K j) (natDegree_chebK_le K j)
    have h2 : supOn (fun x => (chebK K j).eval x) (-K) K ≤ 1 := by
      rw [← cNorm_zero_eq_supOn]; exact cNorm_chebK_le K hK j
    have h3 : (0 : ℝ) ≤ (4 * ((j : ℝ) * Q₀ * (1 + Real.log d))) ^ (4 * m) / (N : ℝ) ^ m := by
      positivity
    have h4 : |Er j| ≤ (4 * ((j : ℝ) * Q₀ * (1 + Real.log d))) ^ (4 * m) / (N : ℝ) ^ m * s :=
      h1.trans (mul_le_mul_of_nonneg_left
        (by simpa using mul_le_mul_of_nonneg_left h2 hs) h3)
    rw [abs_mul]
    calc |a j| * |Er j| ≤ |a j| * ((4 * ((j : ℝ) * Q₀ * (1 + Real.log d))) ^ (4 * m) /
          (N : ℝ) ^ m * s) := mul_le_mul_of_nonneg_left h4 (abs_nonneg _)
      _ = _ := by
          rw [show (4 * ((j : ℝ) * Q₀ * (1 + Real.log d))) = j * (4 * Q₀ * (1 + Real.log d)) by ring,
            mul_pow]
          ring
  obtain ⟨-, hzyg⟩ := Czyg_spec q a K hK
  have hfun : (fun θ => ∑ j ∈ Finset.range (q + 1),
      a j * (Chebyshev.T ℝ j).eval (K * Real.cos θ / K)) = fun θ => p.eval (K * Real.cos θ) := by
    funext θ; rw [ha_eval]
  have hZ := hzyg (4 * m) β hβ
  rw [hfun] at hZ
  have hZ' : ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ (4 * m) * |a j| ≤ max Czyg 0 * conjExp β * lp := by
    refine hZ.trans ?_
    have : 0 ≤ conjExp β * lp := by positivity
    calc Czyg * conjExp β * lp = Czyg * (conjExp β * lp) := by ring
      _ ≤ max Czyg 0 * (conjExp β * lp) := mul_le_mul_of_nonneg_right (le_max_left _ _) this
      _ = _ := by ring
  have hsum : |∑ j ∈ Finset.Icc 1 q, a j * Er j| ≤
      max Czyg 0 * s * (4 * (Q₀ : ℝ) * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * conjExp β * lp := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hEj).trans ?_)
    rw [← Finset.mul_sum]
    have h3 : (0 : ℝ) ≤ (4 * (Q₀ : ℝ) * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * s := by
      positivity
    calc (4 * (Q₀ : ℝ) * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * s *
          ∑ j ∈ Finset.Icc 1 q, (j : ℝ) ^ (4 * m) * |a j|
        ≤ (4 * (Q₀ : ℝ) * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * s *
            (max Czyg 0 * conjExp β * lp) := mul_le_mul_of_nonneg_left hZ' h3
      _ = _ := by ring
  rw [hE0, mul_zero, zero_add]
  exact hsum

end StrongConv.Q202L1.PartS1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
noncomputable section
namespace StrongConv.Q202L1.PartS1
open StrongConv StrongConv.Q202L1
lemma smooth_coe (h : smoothFun) : ContDiff ℝ (⊤ : ℕ∞) (h : ℝ → ℝ) := h.2

lemma poly_smooth (p : ℝ[X]) : ContDiff ℝ (⊤ : ℕ∞) (fun x => p.eval x) := (polyFun p).2

/-- The `L^β` side passes to the limit: a polynomial close to `h` in `C^(r)[-K, K]`. -/
lemma lp_perturb (h : smoothFun) (p : ℝ[X]) (K : ℝ) (hK : 0 ≤ K) (r : ℕ) (β : ℝ) (hβ : 1 < β)
    (ε : ℝ) (hε : ∀ i ≤ r, ∀ x ∈ Set.Icc (-K) K,
      |iteratedDeriv i (fun x => (h : ℝ → ℝ) x - p.eval x) x| ≤ ε) :
    lpNormCircle β (iteratedDeriv r (fun θ => p.eval (K * Real.cos θ))) ≤
      lpNormCircle β (iteratedDeriv r (fun θ => (h : ℝ → ℝ) (K * Real.cos θ))) +
        (2 * Real.pi + 1) * ((r.factorial : ℝ) * ε * (max K 1) ^ r) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun θ : ℝ => K * Real.cos θ) :=
    contDiff_const.mul Real.contDiff_cos
  have hhc : ContDiff ℝ (⊤ : ℕ∞) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)) :=
    (smooth_coe h).comp hc
  have hpc : ContDiff ℝ (⊤ : ℕ∞) (fun θ => p.eval (K * Real.cos θ)) := (poly_smooth p).comp hc
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => (h : ℝ → ℝ) x - p.eval x) :=
    (smooth_coe h).sub (poly_smooth p)
  refine lpNormCircle_le_add β hβ _ _ (hpc.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top))
    (hhc.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)) _ fun θ => ?_
  have h1 := abs_iteratedDeriv_comp_cos_le _ hg K hK r ε hε θ
  have h2 := iteratedDeriv_sub_of_contDiff _ _ hhc hpc r
  have h3 : (fun θ => (fun x => (h : ℝ → ℝ) x - p.eval x) (K * Real.cos θ)) =
      fun θ => (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)) θ - (fun θ => p.eval (K * Real.cos θ)) θ :=
    rfl
  rw [h3, h2] at h1
  rw [abs_sub_comm]
  exact h1

theorem abstract_master :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d Q₀ N₁ m : ℕ) (K s : ℝ) (E : ℕ → (ℝ → ℝ) → ℝ),
      1 ≤ m → 1 ≤ Q₀ → N₁ ≤ Q₀ → 0 < K → 0 ≤ s →
      (∀ N : ℕ, N₁ ≤ N → 1 ≤ N → ∀ f g : ℝ → ℝ, Continuous f → Continuous g → ∀ c : ℝ,
        E N (fun x => f x + c * g x) = E N f + c * E N g) →
      (∀ N : ℕ, N₁ ≤ N → 1 ≤ N → ∀ f : ℝ → ℝ, Continuous f → |E N f| ≤ s * supOn f (-K) K) →
      (∃ e : ℕ → ℝ, ∀ N : ℕ, N₁ ≤ N → 1 ≤ N →
        E N (fun _ => 1) = ∑ i ∈ Finset.range m, e i / (N : ℝ) ^ i) →
      (∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
        ∃ (L : ℕ) (f : ℝ[X]), L ≤ q * Q₀ ∧
          (f.natDegree : ℝ) ≤ ((q * Q₀ : ℕ) : ℝ) * (1 + Real.log d) ∧
          ∀ N : ℕ, N₁ ≤ N → q * Q₀ ≤ N →
            E N (fun x => h.eval x) = f.eval (1 / (N : ℝ)) / (gPoly d L).eval (1 / (N : ℝ))) →
      ∃ ν : ℕ → smoothFun →ₗ[ℝ] ℝ, (∀ i, IsCSDistribution (ν i)) ∧
        ∀ N : ℕ, N₁ ≤ N → 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
          |E N (h : ℝ → ℝ) - ∑ i ∈ Finset.range m, ν i h / (N : ℝ) ^ i| ≤
            C * s * (4 * (Q₀ : ℝ) * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m * conjExp β *
              lpNormCircle β (iteratedDeriv (4 * m + 1) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ))) := by
  refine ⟨max Czyg 0, le_max_right _ _, ?_⟩
  intro d Q₀ N₁ m K s E hm hQ₀ hN₁Q hK hs hlin hbd ⟨e, he⟩ hrat
  have H : AHyp d Q₀ N₁ K s E := ⟨hQ₀, hN₁Q, hK, hs, hlin, hbd, hrat⟩
  choose ν hν using fun i => H.exists_csExt i
  refine ⟨ν, fun i => (hν i).1, ?_⟩
  intro N hN₁ hN β hβ h
  choose c Kc k hc0 hKc hck using fun i => (hν i).1
  have hK0 : 0 ≤ K := hK.le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set R := K + ∑ i ∈ Finset.range m, Kc i with hR
  set kk := 4 * m + 1 + ∑ i ∈ Finset.range m, k i with hkk
  have hKR : K ≤ R := by
    have : 0 ≤ ∑ i ∈ Finset.range m, Kc i := Finset.sum_nonneg fun i _ => (hKc i).le
    linarith
  have hKiR : ∀ i ∈ Finset.range m, Kc i ≤ R := by
    intro i hi
    have : Kc i ≤ ∑ i ∈ Finset.range m, Kc i :=
      Finset.single_le_sum (fun j _ => (hKc j).le) hi
    linarith
  have hkikk : ∀ i ∈ Finset.range m, k i ≤ kk := by
    intro i hi
    have : k i ≤ ∑ i ∈ Finset.range m, k i := Finset.single_le_sum (fun j _ => Nat.zero_le _) hi
    omega
  set A := max Czyg 0 * s * (4 * (Q₀ : ℝ) * (1 + Real.log d)) ^ (4 * m) / (N : ℝ) ^ m *
    conjExp β with hA
  have hA0 : 0 ≤ A := by
    have := le_max_right Czyg 0
    have := conjExp_pos β hβ
    have : (0 : ℝ) ≤ 4 * Q₀ * (1 + Real.log d) := by
      have := Real.log_natCast_nonneg d; positivity
    positivity
  set lph := lpNormCircle β (iteratedDeriv (4 * m + 1) (fun θ => (h : ℝ → ℝ) (K * Real.cos θ)))
  set B := A * ((2 * Real.pi + 1) * (((4 * m + 1).factorial : ℝ) * (max K 1) ^ (4 * m + 1)))
  have hB0 : 0 ≤ B := by
    have : (0 : ℝ) ≤ max K 1 := le_trans zero_le_one (le_max_right _ _)
    have := Real.pi_pos
    positivity
  set M := 1 + s + ∑ i ∈ Finset.range m, c i * ((k i : ℝ) + 1) / (N : ℝ) ^ i + B with hM
  have hM0 : 0 < M := by
    have : 0 ≤ ∑ i ∈ Finset.range m, c i * ((k i : ℝ) + 1) / (N : ℝ) ^ i :=
      Finset.sum_nonneg fun i _ => by have := hc0 i; positivity
    linarith
  have main : ∀ ε > 0, |E N (h : ℝ → ℝ) - ∑ i ∈ Finset.range m, ν i h / (N : ℝ) ^ i| ≤
      A * lph + ε * M := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_poly_approx (h : ℝ → ℝ) (smooth_coe h) kk R ε hε
    set g : ℝ → ℝ := fun x => (h : ℝ → ℝ) x - p.eval x with hgdef
    have hg : ∀ r ≤ kk, ∀ x ∈ Set.Icc (-R) R, |iteratedDeriv r g x| ≤ ε := by
      intro r hr x hx
      rw [hgdef, iteratedDeriv_sub_of_contDiff _ _ (smooth_coe h) (poly_smooth p) r]
      exact hp r hr x hx
    -- (a) the `E` side
    have ha : |E N (h : ℝ → ℝ) - E N (fun x => p.eval x)| ≤ s * ε := by
      have hl := H.lin N hN₁ hN (h : ℝ → ℝ) (fun x => p.eval x) (smooth_coe h).continuous
        p.continuous (-1)
      have hb := H.bd N hN₁ hN (fun x => (h : ℝ → ℝ) x + -1 * p.eval x)
        ((smooth_coe h).continuous.add (continuous_const.mul p.continuous))
      have hsup : supOn (fun x => (h : ℝ → ℝ) x + -1 * p.eval x) (-K) K ≤ ε := by
        apply supOn_le_of_forall (by linarith)
        intro x hx
        have := hg 0 (Nat.zero_le _) x ⟨by linarith [hx.1], by linarith [hx.2]⟩
        simp only [iteratedDeriv_zero, hgdef] at this
        rw [show (h : ℝ → ℝ) x + -1 * p.eval x = (h : ℝ → ℝ) x - p.eval x by ring]
        exact this
      rw [hl] at hb
      have : E N (h : ℝ → ℝ) - E N (fun x => p.eval x) =
          E N (h : ℝ → ℝ) + -1 * E N (fun x => p.eval x) := by ring
      rw [this]
      exact hb.trans (mul_le_mul_of_nonneg_left hsup hs)
    -- (b) the distributions
    have hb : ∀ i ∈ Finset.range m, |ν i h - nuP E i p| ≤ c i * (((k i : ℝ) + 1) * ε) := by
      intro i hi
      have e1 : ν i h - nuP E i p = ν i (h - polyFun p) := by
        rw [map_sub, (hν i).2 p]
      have e2 : ((h - polyFun p : smoothFun) : ℝ → ℝ) = g := rfl
      rw [e1]
      refine (hck i _).trans (mul_le_mul_of_nonneg_left ?_ (hc0 i).le)
      rw [e2]
      exact cNorm_le_of_abs_le (k i) g (Kc i) (hKc i).le ε fun r hr x hx =>
        hg r (hr.trans (hkikk i hi)) x
          ⟨by linarith [hx.1, hKiR i hi], by linarith [hx.2, hKiR i hi]⟩
    -- (c) the polynomial master inequality and the `L^β` side
    have hc := H.poly_master m e he p N hN₁ hN hm β hβ
    have hlp := lp_perturb h p K hK0 (4 * m + 1) β hβ ε fun i hi x hx =>
      hg i (by omega) x ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hc' : |E N (fun x => p.eval x) - ∑ i ∈ Finset.range m, nuP E i p / (N : ℝ) ^ i| ≤
        A * lph + ε * B := by
      refine hc.trans ?_
      calc A * lpNormCircle β (iteratedDeriv (4 * m + 1) (fun θ => p.eval (K * Real.cos θ)))
          ≤ A * (lph + (2 * Real.pi + 1) * (((4 * m + 1).factorial : ℝ) * ε *
              (max K 1) ^ (4 * m + 1))) := mul_le_mul_of_nonneg_left hlp hA0
        _ = A * lph + ε * B := by ring
    have hsplit : E N (h : ℝ → ℝ) - ∑ i ∈ Finset.range m, ν i h / (N : ℝ) ^ i =
        (E N (fun x => p.eval x) - ∑ i ∈ Finset.range m, nuP E i p / (N : ℝ) ^ i) +
        (E N (h : ℝ → ℝ) - E N (fun x => p.eval x)) -
        ∑ i ∈ Finset.range m, (ν i h - nuP E i p) / (N : ℝ) ^ i := by
      simp only [sub_div, Finset.sum_sub_distrib]; ring
    have hbs : |∑ i ∈ Finset.range m, (ν i h - nuP E i p) / (N : ℝ) ^ i| ≤
        ε * ∑ i ∈ Finset.range m, c i * ((k i : ℝ) + 1) / (N : ℝ) ^ i := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_div, abs_of_pos (pow_pos hNpos i)]
      have := hb i hi
      have hpow := pow_pos hNpos i
      rw [show ε * (c i * ((k i : ℝ) + 1) / (N : ℝ) ^ i) = c i * (((k i : ℝ) + 1) * ε) / (N : ℝ) ^ i
        by ring]
      exact div_le_div_of_nonneg_right this hpow.le
    rw [hsplit]
    calc _ ≤ |(E N (fun x => p.eval x) - ∑ i ∈ Finset.range m, nuP E i p / (N : ℝ) ^ i) +
            (E N (h : ℝ → ℝ) - E N (fun x => p.eval x))| +
          |∑ i ∈ Finset.range m, (ν i h - nuP E i p) / (N : ℝ) ^ i| := abs_sub _ _
      _ ≤ (A * lph + ε * B) + s * ε +
            ε * ∑ i ∈ Finset.range m, c i * ((k i : ℝ) + 1) / (N : ℝ) ^ i := by
          have := abs_add_le (E N (fun x => p.eval x) -
            ∑ i ∈ Finset.range m, nuP E i p / (N : ℝ) ^ i)
            (E N (h : ℝ → ℝ) - E N (fun x => p.eval x))
          linarith
      _ ≤ A * lph + ε * M := by rw [hM]; nlinarith
  have hfin : |E N (h : ℝ → ℝ) - ∑ i ∈ Finset.range m, ν i h / (N : ℝ) ^ i| ≤ A * lph := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := main (δ / M) (div_pos hδ hM0)
    rwa [div_mul_cancel₀ δ hM0.ne'] at this
  simpa [hA] using hfin

end StrongConv.Q202L1.PartS1
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L1
open StrongConv
/-! ## Part S1: the abstract master inequality (§§6–7) -/
alias abstract_master := StrongConv.Q202L1.PartS1.abstract_master

end StrongConv.Q202L1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR.Op
open StrongConv StrongConv.Q202L1 Matrix
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-!
# q202 Part R: `stable_rational` (CGTvH Lemma 10.1 for `stE`)

Route: `h(P(Πᴺ))` is a noncommutative polynomial `B(Πᴺ)`; its trace is `∑_w tr(B_w) χ_N(w(σ))`;
`χ_N = φ(ξ₁, …, ξ_r)` for `N ≥ N₀`; the expectation of a product of fixed-point counts of words is
a sum of `N^{(v)} / ∏ N^{(e_i)}` (multi-walk Lemma 5.1); each term is rational in `1/N` with
denominator `g_L`; the bound `|χ_N| ≤ dim N ≤ κ N^α` removes the excess powers of `N`.
-/
omit [CompleteSpace H] in
lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (v : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    tensorOp A T v a = ∑ b, A a b • T (v b) := by
  simp [tensorOp, Finset.sum_apply, Pi.single_apply, smul_ite, Finset.sum_ite_eq]

lemma tensorOp_ext {m n : ℕ} {S S' : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H)}
    (h : ∀ v a, S v a = S' v a) : S = S' :=
  ContinuousLinearMap.ext fun v => PiLp.ext fun a => h v a

lemma tensorOp_add_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, add_smul, Finset.sum_add_distrib]

lemma tensorOp_zero_left {m n : ℕ} (T : H →L[ℂ] H) :
    tensorOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply]

lemma tensorOp_smul_left {m n : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (c • A) T = c • tensorOp A T := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, Finset.smul_sum, smul_smul]

lemma tensorOp_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ)
    (X X' : H →L[ℂ] H) :
    tensorOp A X * tensorOp A' X' = tensorOp (A * A') (X * X') := by
  apply tensorOp_ext; intro v a
  simp only [ContinuousLinearMap.mul_apply, tensorOp_apply, map_sum, map_smul, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

lemma tensorOp_one {n : ℕ} : tensorOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, Matrix.one_apply]

lemma tensorOp_star {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (X : H →L[ℂ] H) :
    star (tensorOp A X) = tensorOp Aᴴ (star X) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simp only [PiLp.inner_apply, tensorOp_apply, ContinuousLinearMap.star_eq_adjoint]
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right, Matrix.conjTranspose_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    Matrix.star_apply, RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]

/-! ## words -/
lemma wordOp_mul {d : ℕ} (u : Fin d → H →L[ℂ] H) (w₁ w₂ : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp u (w₁ * w₂) = wordOp u w₁ * wordOp u w₂ := by
  simp [wordOp, FreeMonoid.toList_mul, List.map_append, List.prod_append]

lemma wordOp_one {d : ℕ} (u : Fin d → H →L[ℂ] H) : wordOp u 1 = 1 := by
  simp [wordOp]

lemma letterOp_swap {d : ℕ} (u : Fin d → H →L[ℂ] H) (a : Fin d ⊕ Fin d) :
    letterOp u a.swap = star (letterOp u a) := by
  cases a <;> simp [letterOp]

lemma star_wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    star (wordOp u w) = wordOp u (NCPoly.wordStar w) := by
  unfold wordOp NCPoly.wordStar
  generalize w.toList = l
  simp only [FreeMonoid.toList_ofList]
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
      List.map_nil, List.prod_nil, mul_one, star_mul, ← ih, List.map_singleton, List.prod_singleton,
      letterOp_swap]

lemma wordStar_wordStar {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (NCPoly.wordStar w) = w := by
  simp [NCPoly.wordStar, List.map_reverse, Function.comp_def]

end StrongConv.Q202L1.PartR.Op
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR.Op
open StrongConv StrongConv.Q202L1 Matrix
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {D d : ℕ}
/-! ## eval as an additive map -/
def evalAdd (u : Fin d → H →L[ℂ] H) :
    NCPoly D d →+ (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) :=
  Finsupp.liftAddHom fun w =>
    { toFun := fun A => tensorOp A (wordOp u w)
      map_zero' := tensorOp_zero_left _
      map_add' := fun A B => tensorOp_add_left A B _ }

lemma eval_eq_evalAdd (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) : P.eval u = evalAdd u P := by
  simp [NCPoly.eval, evalAdd, Finsupp.liftAddHom_apply, Finsupp.sum]

lemma ncEval_single (w : FreeMonoid (Fin d ⊕ Fin d)) (A : Matrix (Fin D) (Fin D) ℂ)
    (u : Fin d → H →L[ℂ] H) : NCPoly.eval (Finsupp.single w A : NCPoly D d) u = tensorOp A (wordOp u w) := by
  rw [eval_eq_evalAdd]; unfold evalAdd; rw [Finsupp.liftAddHom_apply_single]; rfl

lemma ncEval_add (P Q : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (P + Q).eval u = P.eval u + Q.eval u := by
  simp only [eval_eq_evalAdd, map_add]

lemma ncEval_sum {ι : Type*} (s : Finset ι) (f : ι → NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (∑ i ∈ s, f i).eval u = ∑ i ∈ s, (f i).eval u := by
  simp only [eval_eq_evalAdd, map_sum]

lemma ncEval_smul (c : ℂ) (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (c • P).eval u = c • P.eval u := by
  induction P using Finsupp.induction_linear with
  | zero => simp only [smul_zero, eval_eq_evalAdd, map_zero]; ext x i; simp
  | add P Q hP hQ => rw [smul_add, ncEval_add, ncEval_add, hP, hQ, smul_add]
  | single w A =>
    rw [Finsupp.smul_single, ncEval_single, ncEval_single, tensorOp_smul_left]

/-! ## degree -/
lemma ncDegree_le_iff (P : NCPoly D d) (n : ℕ) :
    P.degree ≤ n ↔ ∀ w, P w ≠ 0 → w.length ≤ n := by
  unfold NCPoly.degree
  rw [Finset.sup_le_iff]
  simp

lemma ncDegree_sum_le {ι : Type*} (s : Finset ι) (f : ι → NCPoly D d) (n : ℕ)
    (h : ∀ i ∈ s, (f i).degree ≤ n) : (∑ i ∈ s, f i).degree ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [NCPoly.degree]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, ncDegree_le_iff]
    intro w hw
    have h1 := (ncDegree_le_iff _ _).1 (h a (Finset.mem_insert_self _ _))
    have h2 := (ncDegree_le_iff _ _).1 (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [Finsupp.add_apply] at hw
    by_cases ha' : f a w = 0
    · rw [ha', zero_add] at hw; exact h2 w hw
    · exact h1 w ha'

lemma ncDegree_smul_le (c : ℂ) (P : NCPoly D d) (n : ℕ) (h : P.degree ≤ n) :
    (c • P).degree ≤ n := by
  rw [ncDegree_le_iff] at h ⊢
  intro w hw
  apply h
  intro h0
  apply hw
  simp [h0]

lemma ncDegree_single_le (w : FreeMonoid (Fin d ⊕ Fin d)) (A : Matrix (Fin D) (Fin D) ℂ) (n : ℕ)
    (h : w.length ≤ n) : NCPoly.degree (Finsupp.single w A : NCPoly D d) ≤ n := by
  rw [ncDegree_le_iff]
  intro v hv
  by_cases hvw : v = w
  · subst hvw; exact h
  · simp [Finsupp.single_apply, Ne.symm hvw] at hv

/-- product -/
def mulNC (B P : NCPoly D d) : NCPoly D d :=
  ∑ w ∈ B.support, ∑ w' ∈ P.support, Finsupp.single (w * w') (B w * P w')

lemma eval_mulNC (B P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    (mulNC B P).eval u = B.eval u * P.eval u := by
  unfold mulNC
  have hB : B.eval u = ∑ w ∈ B.support, tensorOp (B w) (wordOp u w) := rfl
  have hP : P.eval u = ∑ w ∈ P.support, tensorOp (P w) (wordOp u w) := rfl
  rw [ncEval_sum, hB, hP, Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [ncEval_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w' _ => ?_
  rw [ncEval_single, wordOp_mul, tensorOp_mul]

lemma degree_mulNC (B P : NCPoly D d) : (mulNC B P).degree ≤ B.degree + P.degree := by
  unfold mulNC
  refine ncDegree_sum_le _ _ _ fun w hw => ncDegree_sum_le _ _ _ fun w' hw' => ?_
  refine ncDegree_single_le _ _ _ ?_
  rw [FreeMonoid.length_mul]
  exact add_le_add (Finset.le_sup (f := FreeMonoid.length) hw) (Finset.le_sup (f := FreeMonoid.length) hw')

lemma pow_expansion (P : NCPoly D d) (q₀ : ℕ) (hq₀ : P.degree ≤ q₀) (k : ℕ) :
    ∃ B : NCPoly D d, B.degree ≤ k * q₀ ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (u : Fin d → H →L[ℂ] H), (P.eval u) ^ k = B.eval u := by
  induction k with
  | zero =>
    refine ⟨(Finsupp.single 1 1 : NCPoly D d), ncDegree_single_le _ _ _ (by simp [FreeMonoid.length_one]), ?_⟩
    intro H _ _ _ u
    rw [ncEval_single, wordOp_one, tensorOp_one, pow_zero]
  | succ k ih =>
    obtain ⟨B, hB, hBe⟩ := ih
    refine ⟨mulNC B P, ?_, ?_⟩
    · refine (degree_mulNC B P).trans ?_
      rw [add_mul, one_mul]
      exact add_le_add hB hq₀
    · intro H _ _ _ u
      rw [pow_succ, hBe, eval_mulNC]

lemma star_eval {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    star (P.eval u) = ∑ w ∈ P.support, tensorOp (P w)ᴴ (wordOp u (NCPoly.wordStar w)) := by
  unfold NCPoly.eval
  erw [star_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [tensorOp_star, star_wordOp]

end StrongConv.Q202L1.PartR.Op
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR.Op
open StrongConv StrongConv.Q202L1 Matrix
lemma exists_poly_expansion {D d q₀ : ℕ} (P : NCPoly D d) (hq₀ : P.degree ≤ q₀) (h : ℝ[X]) :
    ∃ B : NCPoly D d, B.degree ≤ h.natDegree * q₀ ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (u : Fin d → H →L[ℂ] H),
        ∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • (P.eval u) ^ k = B.eval u := by
  choose Bk hBk hBke using pow_expansion P q₀ hq₀
  refine ⟨∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • Bk k, ?_, ?_⟩
  · refine ncDegree_sum_le _ _ _ fun k hk => ncDegree_smul_le _ _ _ ((hBk k).trans ?_)
    exact Nat.mul_le_mul_right _ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
  · intro H _ _ _ u
    rw [ncEval_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ncEval_smul, hBke k H u]

lemma fnCalc_poly {A : Type*} [CStarAlgebra A] (T : A) (hT : IsSelfAdjoint T) (h : ℝ[X]) :
    fnCalc (fun x => h.eval x) T = ∑ k ∈ Finset.range (h.natDegree + 1), (h.coeff k : ℂ) • T ^ k := by
  have := hT.isStarNormal
  unfold fnCalc
  have : cfc (fun z : ℂ => ((h.eval z.re : ℝ) : ℂ)) T =
      cfc (fun z : ℂ => (h.map (algebraMap ℝ ℂ)).eval z) T := by
    apply cfc_congr
    intro z hz
    have := hT.mem_spectrum_eq_re hz
    simp only
    conv_rhs => rw [this]
    simp [Polynomial.eval_map, ← Complex.coe_algebraMap, Polynomial.eval₂_at_apply]
  rw [this, cfc_polynomial (h.map (algebraMap ℝ ℂ)) T, aeval_eq_sum_range, natDegree_map]
  simp [coeff_map]

lemma isSelfAdjoint_eval {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (P.eval u) := by
  unfold IsSelfAdjoint
  rw [star_eval]
  have hmem : ∀ w, w ∈ P.support → NCPoly.wordStar w ∈ P.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    rw [hP]
    simpa using hw
  calc _ = ∑ w ∈ P.support, tensorOp (P (NCPoly.wordStar w)) (wordOp u (NCPoly.wordStar w)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hP]
    _ = P.eval u := by
        unfold NCPoly.eval
        exact Finset.sum_nbij' NCPoly.wordStar NCPoly.wordStar hmem hmem
          (fun _ _ => wordStar_wordStar _) (fun _ _ => wordStar_wordStar _) (fun _ _ => rfl)

/-! ### Traces -/
/-- The free-group element of a word in `s, s*`. -/
def fw {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) : FreeGroup (Fin d) :=
  (w.toList.map fun
    | Sum.inl i => FreeGroup.of i
    | Sum.inr i => (FreeGroup.of i)⁻¹).prod

/-- The character `χ_N(g) = Tr π_N(g)`. -/
def chi (π : StableRep) (N : ℕ) (g : Equiv.Perm (Fin N)) : ℂ :=
  (π.π N g : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ).trace

lemma trace_toEuclideanCLM {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ _ ((Matrix.toEuclideanCLM (𝕜 := ℂ) M :
      EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :
        EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = M.trace := by
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin, Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Matrix.trace_toLin_eq]

lemma trace_tensorOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => H))
        ((tensorOp A T : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) :
          PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) =
      A.trace * LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  classical
  unfold tensorOp
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul, map_sum,
    map_smul]
  rw [Matrix.trace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have key : ∀ b : Fin D,
      LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => H))
        ((((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => H)).symm.toContinuousLinearMap.comp
          ((ContinuousLinearMap.single ℂ (fun _ : Fin D => H) a).comp
            (T.comp (PiLp.proj 2 (fun _ : Fin D => H) b : PiLp 2 (fun _ : Fin D => H) →L[ℂ] H))))) :
              PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) =
        if a = b then LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) else 0 := by
    intro b
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
      ← ContinuousLinearMap.toLinearMap_comp]
    have : (PiLp.proj 2 (fun _ : Fin D => H) b : PiLp 2 (fun _ : Fin D => H) →L[ℂ] H).comp
        ((((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => H)).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.single ℂ (fun _ : Fin D => H) a)).comp T) =
          if a = b then T else 0 := by
      ext x
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [this]
    split_ifs <;> simp
  simp only [key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.diag_apply]

lemma wordOp_model (π : StableRep) {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N))
    (w : FreeMonoid (Fin d ⊕ Fin d)) :
    wordOp (π.model σ) w = Matrix.toEuclideanCLM (𝕜 := ℂ)
      (π.π N (FreeGroup.lift σ (fw w)) :
        Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) := by
  unfold wordOp fw
  generalize w.toList = L
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, Submonoid.coe_mul] at ih ⊢
    rw [ih]
    congr 1
    rcases l with i | i
    · simp [letterOp, StableRep.model]
    · simp only [letterOp, StableRep.model, ← map_star]
      congr 1
      simp

theorem trace_eval_model (π : StableRep) {D d N : ℕ} (P : NCPoly D d)
    (σ : Fin d → Equiv.Perm (Fin N)) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
        ((P.eval (π.model σ) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
          PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
            PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) =
      ∑ w ∈ P.support, (P w).trace * chi π N (FreeGroup.lift σ (fw w)) := by
  unfold NCPoly.eval
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [trace_tensorOp, wordOp_model, trace_toEuclideanCLM]
  rfl

theorem norm_chi_le (π : StableRep) (N : ℕ) (g : Equiv.Perm (Fin N)) :
    ‖chi π N g‖ ≤ π.dim N := by
  unfold chi Matrix.trace
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖Matrix.diag (π.π N g : Matrix (Fin (π.dim N)) (Fin (π.dim N)) ℂ) i‖
      ≤ ∑ _i : Fin (π.dim N), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary (π.π N g).2 i i
    _ = π.dim N := by simp

/-- The uniform average of a real function. -/
lemma uniformExp_sum {X ι : Type*} [Fintype X] (s : Finset ι) (f : ι → X → ℝ) :
    uniformExp (fun x => ∑ a ∈ s, f a x) = ∑ a ∈ s, uniformExp (f a) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]

/-- `h(P(Πᴺ))` expanded over words. -/
theorem stE_eq (π : StableRep) {D d q₀ : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (hq₀ : P.degree ≤ q₀) (h : ℝ[X]) :
    ∃ B : NCPoly D d, B.degree ≤ h.natDegree * q₀ ∧ ∀ N : ℕ,
      stE π P N (fun x => h.eval x) = ∑ w ∈ B.support,
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((B w).trace * chi π N (FreeGroup.lift σ (fw w))).re / (N : ℝ) ^ π.alpha) := by
  obtain ⟨B, hB, hBe⟩ := exists_poly_expansion P hq₀ h
  refine ⟨B, hB, fun N => ?_⟩
  unfold stE
  rw [← uniformExp_sum]
  congr 1
  funext σ
  rw [fnCalc_poly _ (isSelfAdjoint_eval P hP (π.model σ)) h,
    hBe (EuclideanSpace ℂ (Fin (π.dim N))) (π.model σ), trace_eval_model, Complex.re_sum,
    Finset.sum_div]

end StrongConv.Q202L1.PartR.Op
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
/-- The permutation a letter stands for. -/
def letterPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) : Letter d → Equiv.Perm (Fin N)
  | none => 1
  | some (Sum.inl i) => σ i
  | some (Sum.inr i) => (σ i)⁻¹

/-- The permutation a word stands for (product in the order the letters appear). -/
def wordPerm {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : List (Letter d)) :
    Equiv.Perm (Fin N) :=
  (w.map (letterPerm σ)).prod

/-- Number of fixed points. -/
def fixCount {N : ℕ} (π : Equiv.Perm (Fin N)) : ℕ :=
  (Finset.univ.filter fun x => π x = x).card

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
/-- A finite set of pairs is the graph of a partial injection. -/
def PInj (E : Finset (α × α)) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, (p.1 = q.1 ↔ p.2 = q.2)

instance (E : Finset (α × α)) : Decidable (PInj E) := by
  unfold PInj; infer_instance

lemma card_stab (A : Finset α) :
    (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      (Fintype.card α - A.card).factorial := by
  have e := Equiv.Perm.subtypeEquivSubtypePerm (fun a : α => a ∉ A)
  have h1 : (univ.filter fun π : Equiv.Perm α => ∀ a ∈ A, π a = a).card =
      Fintype.card { f : Equiv.Perm α // ∀ a, ¬ (a ∉ A) → f a = a } := by
    rw [Fintype.card_subtype]; congr 1; ext π; simp
  rw [h1, ← Fintype.card_congr e, Fintype.card_perm, Fintype.card_subtype]
  congr 1
  rw [← Finset.card_compl]
  congr 1
  ext a; simp

lemma exists_ext (E : Finset (α × α)) (h : PInj E) :
    ∃ τ : Equiv.Perm α, ∀ p ∈ E, τ p.1 = p.2 := by
  have key : ∀ a ∈ E.image Prod.fst, ∃ p ∈ E, p.1 = a := by
    intro a ha; simpa using ha
  let f : {a // a ∈ E.image Prod.fst} → {b // b ∈ E.image Prod.snd} := fun a =>
    ⟨(Classical.choose (key a.1 a.2)).2,
      mem_image_of_mem _ (Classical.choose_spec (key a.1 a.2)).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have h1 := Classical.choose_spec (key a.1 a.2)
      have h2 := Classical.choose_spec (key a'.1 a'.2)
      have : (Classical.choose (key a.1 a.2)).2 = (Classical.choose (key a'.1 a'.2)).2 :=
        congrArg Subtype.val haa
      apply Subtype.ext
      rw [← h1.2, ← h2.2]
      exact (h _ h1.1 _ h2.1).2 this
    · intro b
      obtain ⟨q, hq, hqb⟩ := mem_image.1 b.2
      refine ⟨⟨q.1, mem_image_of_mem _ hq⟩, Subtype.ext ?_⟩
      have h1 := Classical.choose_spec (key q.1 (mem_image_of_mem _ hq))
      show (Classical.choose (key q.1 (mem_image_of_mem _ hq))).2 = b.1
      rw [← hqb]
      exact (h _ h1.1 _ hq).1 h1.2
  refine ⟨(Equiv.ofBijective f hf).extendSubtype, fun p hp => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem _ _ (mem_image_of_mem _ hp)]
  have h1 := Classical.choose_spec (key p.1 (mem_image_of_mem _ hp))
  exact (h _ h1.1 _ hp).1 h1.2

lemma card_ext (E : Finset (α × α)) :
    (univ.filter fun τ : Equiv.Perm α => ∀ p ∈ E, τ p.1 = p.2).card =
      if PInj E then (Fintype.card α - E.card).factorial else 0 := by
  split_ifs with h
  · obtain ⟨τ₀, hτ₀⟩ := exists_ext E h
    have hA : (E.image Prod.fst).card = E.card :=
      card_image_of_injOn (fun p hp q hq hpq => Prod.ext hpq ((h p hp q hq).1 hpq))
    rw [← hA, ← card_stab]
    refine card_nbij' (fun τ => τ₀⁻¹ * τ) (fun π => τ₀ * π) ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hτ ⊢
      intro a ha
      obtain ⟨p, hp, rfl⟩ : ∃ p ∈ E, p.1 = a := by simpa using ha
      rw [Equiv.Perm.mul_apply, hτ p hp, ← hτ₀ p hp]
      simp
    · intro π hπ
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hπ ⊢
      intro p hp
      rw [Equiv.Perm.mul_apply, hπ p.1 (mem_image_of_mem _ hp), hτ₀ p hp]
    · intro τ _; simp
    · intro π _; simp
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro τ _ hτ
    apply h
    intro p hp q hq
    constructor
    · intro e; rw [← hτ p hp, ← hτ q hq, e]
    · intro e; apply τ.injective; rw [hτ p hp, hτ q hq, e]

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} (w : List (Letter d))
/-! ## Paths along a word -/
/-- The label `i` of a letter `sᵢ` or `sᵢ*`. -/
def lab : Letter d → Option (Fin d)
  | none => none
  | some (Sum.inl i) => some i
  | some (Sum.inr i) => some i

/-- The directed edge `(a', b')` with `σᵢ a' = b'` forced by a step `xₜ = letter (xₜ₊₁)`, where
`a = xₜ`, `b = xₜ₊₁`. -/
def edge {α : Type*} : Letter d → α → α → α × α
  | some (Sum.inl _), a, b => (b, a)
  | _, a, b => (a, b)

lemma edge_cases {α : Type*} (l : Letter d) (a b : α) :
    ((edge l a b).1 = a ∧ (edge l a b).2 = b) ∨ ((edge l a b).1 = b ∧ (edge l a b).2 = a) := by
  rcases l with _ | i | i <;> simp [edge]

lemma edge_map {α β : Type*} (φ : β → α) (l : Letter d) (a b : β) :
    edge l (φ a) (φ b) = Prod.map φ φ (edge l a b) := by
  rcases l with _ | i | i <;> simp [edge]

/-- The edge set of label `i` of a path. -/
def Es {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) (i : Fin d) :
    Finset (α × α) :=
  (univ.filter fun t : Fin w.length => lab (w.get t) = some i).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

/-- The path stands still at the `none` letters. -/
def Cons {α : Type*} (x : Fin (w.length + 1) → α) : Prop :=
  ∀ t : Fin w.length, w.get t = none → x t.castSucc = x t.succ

/-- A closed consistent path whose edge sets are partial injections. -/
def Good {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) : Prop :=
  Cons w x ∧ (∀ i, PInj (Es w x i)) ∧ x 0 = x (Fin.last _)

instance {α : Type*} [DecidableEq α] (x : Fin (w.length + 1) → α) : Decidable (Cons w x) := by
  unfold Cons; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (w.length + 1) → α) :
    Decidable (Good w x) := by
  unfold Good; infer_instance

/-- `σ` realises the path `x`. -/
def Rz {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) : Prop :=
  ∀ t : Fin w.length, x t.castSucc = letterPerm σ (w.get t) (x t.succ)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Decidable (Rz w σ x) := by
  unfold Rz; infer_instance

/-- The path of `y` under `σ`. -/
def path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) : Fin (w.length + 1) → Fin N :=
  fun t => wordPerm σ (w.drop t) y

lemma wordPerm_cons_apply {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (l : Letter d)
    (ws : List (Letter d)) (y : Fin N) :
    wordPerm σ (l :: ws) y = letterPerm σ l (wordPerm σ ws y) := by
  simp [wordPerm, Equiv.Perm.mul_apply]

lemma path_last {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y (Fin.last _) = y := by
  simp [path, wordPerm]

lemma path_zero {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) :
    path w σ y 0 = wordPerm σ w y := by
  simp [path]

lemma path_step {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (y : Fin N) (t : Fin w.length) :
    path w σ y t.castSucc = letterPerm σ (w.get t) (path w σ y t.succ) := by
  simp only [path, Fin.val_castSucc, Fin.val_succ]
  rw [List.drop_eq_getElem_cons t.2, wordPerm_cons_apply]
  rfl

lemma eq_path {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N)
    (hx : Rz w σ x) : x = path w σ (x (Fin.last _)) := by
  funext t
  induction t using Fin.reverseInduction with
  | last => rw [path_last]
  | cast t ih => rw [hx t, path_step, ← ih]

lemma fixCount_eq {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    fixCount (wordPerm σ w) =
      (univ.filter fun x : Fin (w.length + 1) → Fin N => Rz w σ x ∧ x 0 = x (Fin.last _)).card := by
  unfold fixCount
  symm
  refine card_nbij' (fun x => x (Fin.last _)) (path w σ) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    have := eq_path w σ x hx.1
    conv_rhs => rw [← hx.2, this]
    rw [path_zero]
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
    exact ⟨fun t => path_step w σ y t, by rw [path_zero, path_last, hy]⟩
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    exact (eq_path w σ x hx.1).symm
  · intro y _
    exact path_last w σ y

lemma Rz_iff {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (w.length + 1) → Fin N) :
    Rz w σ x ↔ Cons w x ∧ ∀ i, ∀ p ∈ Es w x i, σ i p.1 = p.2 := by
  constructor
  · intro h
    refine ⟨fun t ht => by have := h t; rw [ht] at this; simpa [letterPerm] using this, ?_⟩
    intro i p hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    rw [mem_filter] at ht
    have h' := h t
    generalize w.get t = l at ht h'
    rcases l with _ | j | j
    · simp [lab] at ht
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge]; exact h'.symm
    · simp only [lab, Option.some.injEq] at ht
      obtain ⟨-, rfl⟩ := ht
      simp only [edge, letterPerm] at h' ⊢
      rw [h']; simp
  · rintro ⟨hc, he⟩ t
    have hmem : ∀ j, lab (w.get t) = some j →
        edge (w.get t) (x t.castSucc) (x t.succ) ∈ Es w x j := fun j hj =>
      mem_image.2 ⟨t, mem_filter.2 ⟨mem_univ _, hj⟩, rfl⟩
    have hct := hc t
    generalize w.get t = l at hmem hct
    rcases l with _ | j | j
    · simp [letterPerm, hct rfl]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, this]
    · have := he j _ (hmem j rfl)
      simp only [edge] at this
      simp [letterPerm, ← this]

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {n : ℕ} {α : Type*} [DecidableEq α]
/-! ## Canonical representatives of kernels -/
/-- The first position where `x` takes the value `x t`. -/
def canon (x : Fin n → α) (t : Fin n) : Fin n :=
  (univ.filter fun s => x s = x t).min' ⟨t, by simp⟩

lemma canon_spec (x : Fin n → α) (t : Fin n) : x (canon x t) = x t := by
  unfold canon
  exact (mem_filter.1 (min'_mem (univ.filter fun s => x s = x t) _)).2

lemma canon_eq_of_ker {β : Type*} [DecidableEq β] (x : Fin n → α) (y : Fin n → β)
    (h : ∀ s t, x s = x t ↔ y s = y t) : canon x = canon y := by
  funext t
  simp only [canon, h]

lemma canon_ker (x : Fin n → α) (s t : Fin n) : canon x s = canon x t ↔ x s = x t := by
  constructor
  · intro h
    have := congrArg x h
    rwa [canon_spec x s, canon_spec x t] at this
  · intro h
    have : ∀ r, (x r = x s) ↔ (x r = x t) := fun r => by rw [h]
    simp only [canon, this]

lemma canon_canon (x : Fin n → α) : canon (canon x) = canon x :=
  canon_eq_of_ker _ _ (canon_ker x)

lemma canon_canon_apply (x : Fin n → α) (t : Fin n) : canon x (canon x t) = canon x t :=
  (canon_ker x _ _).2 (canon_spec x t)

lemma injOn_canon (x : Fin n → α) : Set.InjOn x (Set.range (canon x)) := by
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ h
  rw [canon_spec x s, canon_spec x t] at h
  exact (canon_ker x s t).2 h

lemma comp_canon (x : Fin n → α) : x ∘ canon x = x := funext (canon_spec x)

/-- The number of values of a path. -/
def nv (x : Fin n → α) : ℕ := (univ.image x).card

lemma card_fiber [Fintype α] (c : Fin n → Fin n) (hc : canon c = c) :
    (univ.filter fun x : Fin n → α => canon x = c).card =
      (Fintype.card α).descFactorial (nv c) := by
  have hcc : ∀ t, c (c t) = c t := fun t => by
    have := canon_canon_apply c t; rwa [hc] at this
  have hmem : ∀ t, c t ∈ univ.image c := fun t => mem_image_of_mem _ (mem_univ _)
  rw [nv, ← Fintype.card_coe (univ.image c), ← Fintype.card_embedding_eq, ← card_univ]
  refine card_bij' (fun x hx => ⟨fun s => x s.1, ?_⟩) (fun φ _ => fun t => φ ⟨c t, hmem t⟩)
    (fun _ _ => mem_univ _) ?_ ?_ ?_
  · rintro ⟨s, hs⟩ ⟨s', hs'⟩ h
    have hx : canon x = c := (mem_filter.1 hx).2
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    obtain ⟨t', -, rfl⟩ := mem_image.1 hs'
    simp only at h
    apply Subtype.ext
    simp only
    rw [← hx] at h ⊢
    rw [canon_spec x t, canon_spec x t'] at h
    exact (canon_ker x t t').2 h
  · intro φ _
    simp only [mem_filter, mem_univ, true_and]
    refine Eq.trans ?_ hc
    refine canon_eq_of_ker _ _ fun s t => ?_
    rw [φ.injective.eq_iff, Subtype.mk.injEq]
  · intro x hx
    have hx : canon x = c := (mem_filter.1 hx).2
    funext t
    show x (c t) = x t
    rw [← hx]
    exact canon_spec x t
  · intro φ _
    apply Function.Embedding.ext
    rintro ⟨s, hs⟩
    obtain ⟨t, -, rfl⟩ := mem_image.1 hs
    show φ ⟨c (c t), hmem (c t)⟩ = φ ⟨c t, hs⟩
    congr 2
    exact hcc t

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} (w : List (Letter d))
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
/-! ## Invariance under relabelling -/
omit [Fintype α] [Fintype β] in
lemma Es_comp (c : Fin (w.length + 1) → β) (φ : β → α) (i : Fin d) :
    Es w (φ ∘ c) i = (Es w c i).image (Prod.map φ φ) := by
  simp only [Es, image_image]
  refine image_congr fun t _ => ?_
  simp [edge_map]

omit [Fintype β] in
lemma Es_range (c : Fin (w.length + 1) → β) (i : Fin d) (p : β × β) (hp : p ∈ Es w c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  obtain ⟨t, -, rfl⟩ := mem_image.1 hp
  rcases edge_cases (w.get t) (c t.castSucc) (c t.succ) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} (w : List (Letter d))
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (c : Fin (w.length + 1) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} (w : List (Letter d)) {α : Type*} [DecidableEq α]
/-! ## The bounds on the invariants -/
lemma sum_card_Es_le (x : Fin (w.length + 1) → α) : ∑ i, (Es w x i).card ≤ w.length := by
  calc ∑ i, (Es w x i).card
      ≤ ∑ i, (univ.filter fun t : Fin w.length => lab (w.get t) = some i).card :=
        sum_le_sum fun i _ => card_image_le
    _ = (univ.biUnion fun i => univ.filter fun t : Fin w.length => lab (w.get t) = some i).card := by
        rw [card_biUnion]
        intro i _ j _ hij
        show Disjoint _ _
        rw [disjoint_filter]
        intro t _ hi hj
        exact hij (Option.some.inj (hi.symm.trans hj))
    _ ≤ w.length := (card_le_univ _).trans (Fintype.card_fin _).le

/-- The values of a path at positions `≤ k`. -/
def U (x : Fin (w.length + 1) → α) (k : ℕ) : Finset α :=
  (univ.filter fun t : Fin (w.length + 1) => t.val ≤ k).image x

/-- The edges of a path at steps `< k`. -/
def Ed (x : Fin (w.length + 1) → α) (k : ℕ) : Finset (α × α) :=
  (univ.filter fun t : Fin w.length => t.val < k ∧ lab (w.get t) ≠ none).image
    fun t => edge (w.get t) (x t.castSucc) (x t.succ)

lemma Ed_mem_U (x : Fin (w.length + 1) → α) (k : ℕ) (p : α × α) (hp : p ∈ Ed w x k) :
    p.1 ∈ U w x k ∧ p.2 ∈ U w x k := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 hp
  have hs := (mem_filter.1 hs).2.1
  have h1 : x s.castSucc ∈ U w x k :=
    mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp; omega⟩)
  have h2 : x s.succ ∈ U w x k :=
    mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp; omega⟩)
  rcases edge_cases (w.get s) (x s.castSucc) (x s.succ) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2]
  exacts [⟨h1, h2⟩, ⟨h2, h1⟩]

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
/-! ## Several closed walks -/
/-- Positions of the closed walks. -/
abbrev Pos := Σ k : ι, Fin ((u k).length + 1)

/-- Number of positions. -/
def nP : ℕ := Fintype.card (Pos u)

/-- An enumeration of the positions. -/
def eP : Pos u ≃ Fin (nP u) := Fintype.equivFin _

/-- The `k`-th walk of a labelling of the positions. -/
def cmp {α : Type*} (x : Fin (nP u) → α) (k : ι) : Fin ((u k).length + 1) → α :=
  fun j => x (eP u ⟨k, j⟩)

/-- All edges of label `i`. -/
def EsM {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) (i : Fin d) : Finset (α × α) :=
  univ.biUnion fun k => Es (u k) (cmp u x k) i

/-- Every walk is closed. -/
def ClM {α : Type*} (x : Fin (nP u) → α) : Prop :=
  ∀ k, cmp u x k 0 = cmp u x k (Fin.last _)

/-- Every walk stands still at `none`. -/
def ConsM {α : Type*} (x : Fin (nP u) → α) : Prop :=
  ∀ k, Cons (u k) (cmp u x k)

/-- Good labellings. -/
def GoodM {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Prop :=
  ConsM u x ∧ (∀ i, PInj (EsM u x i)) ∧ ClM u x

instance {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Decidable (ClM u x) := by
  unfold ClM; infer_instance

instance {α : Type*} [DecidableEq α] (x : Fin (nP u) → α) : Decidable (ConsM u x) := by
  unfold ConsM; infer_instance

instance {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (nP u) → α) :
    Decidable (GoodM u x) := by
  unfold GoodM; infer_instance

/-- `σ` realises all walks. -/
def RzM {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) : Prop :=
  ∀ k, Rz (u k) σ (cmp u x k)

instance {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) :
    Decidable (RzM u σ x) := by
  unfold RzM; infer_instance

/-- The weight. -/
def GM (N : ℕ) {α : Type*} [Fintype α] [DecidableEq α] (x : Fin (nP u) → α) : ℕ :=
  if GoodM u x then ∏ i, (N - (EsM u x i).card).factorial else 0

lemma prod_fixCount_eq {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) :
    ∏ k, fixCount (wordPerm σ (u k)) =
      (univ.filter fun x : Fin (nP u) → Fin N => RzM u σ x ∧ ClM u x).card := by
  have hk : ∀ k, fixCount (wordPerm σ (u k)) =
      (univ.filter fun y : Fin ((u k).length + 1) → Fin N =>
        Rz (u k) σ y ∧ y 0 = y (Fin.last _)).card := fun k => fixCount_eq (u k) σ
  rw [prod_congr rfl (fun k _ => hk k), ← Fintype.card_piFinset]
  symm
  refine card_bij' (fun x _ => fun k => cmp u x k)
    (fun y _ => fun v => y ((eP u).symm v).1 ((eP u).symm v).2) ?_ ?_ ?_ ?_
  · intro x hx
    have hx := (mem_filter.1 hx).2
    rw [Fintype.mem_piFinset]
    exact fun k => mem_filter.2 ⟨mem_univ _, hx.1 k, hx.2 k⟩
  · intro y hy
    rw [Fintype.mem_piFinset] at hy
    have : ∀ k, cmp u (fun v => y ((eP u).symm v).1 ((eP u).symm v).2) k = y k := by
      intro k; funext j; simp only [cmp]; rw [Equiv.symm_apply_apply]
    refine mem_filter.2 ⟨mem_univ _, fun k => ?_, fun k => ?_⟩
    · rw [this]; exact (mem_filter.1 (hy k)).2.1
    · show cmp u _ k 0 = cmp u _ k _
      rw [this]; exact (mem_filter.1 (hy k)).2.2
  · intro x _
    funext v
    simp only [cmp]
    rw [Sigma.eta, Equiv.apply_symm_apply]
  · intro y _
    funext k j
    simp only [cmp]
    rw [Equiv.symm_apply_apply]

lemma RzM_iff {N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (x : Fin (nP u) → Fin N) :
    RzM u σ x ↔ ConsM u x ∧ ∀ i, ∀ p ∈ EsM u x i, σ i p.1 = p.2 := by
  constructor
  · intro h
    refine ⟨fun k => ((Rz_iff (u k) σ _).1 (h k)).1, fun i p hp => ?_⟩
    obtain ⟨k, -, hk⟩ := mem_biUnion.1 hp
    exact ((Rz_iff (u k) σ _).1 (h k)).2 i p hk
  · rintro ⟨h1, h2⟩ k
    exact (Rz_iff (u k) σ _).2 ⟨h1 k, fun i p hp =>
      h2 i p (mem_biUnion.2 ⟨k, mem_univ _, hp⟩)⟩

lemma card_RzM {N : ℕ} (x : Fin (nP u) → Fin N) :
    (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => RzM u σ x).card =
      if ConsM u x then
        ∏ i, (if PInj (EsM u x i) then (N - (EsM u x i).card).factorial else 0)
      else 0 := by
  split_ifs with hc
  · have : (univ.filter fun σ : Fin d → Equiv.Perm (Fin N) => RzM u σ x) =
        Fintype.piFinset (fun i => univ.filter fun τ : Equiv.Perm (Fin N) =>
          ∀ p ∈ EsM u x i, τ p.1 = p.2) := by
      ext σ; simp [RzM_iff, hc, Fintype.mem_piFinset]
    rw [this, Fintype.card_piFinset]
    refine prod_congr rfl fun i _ => ?_
    rw [card_ext, Fintype.card_fin]
  · rw [card_eq_zero, filter_eq_empty_iff]
    intro σ _ h
    exact hc ((RzM_iff u σ x).1 h).1

lemma sum_prod_fixCount (N : ℕ) :
    ∑ σ : Fin d → Equiv.Perm (Fin N), ∏ k, fixCount (wordPerm σ (u k)) =
      ∑ x : Fin (nP u) → Fin N, GM u N x := by
  simp only [prod_fixCount_eq, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [← card_filter]
  by_cases hcl : ClM u x
  · simp only [hcl, and_true]
    rw [card_RzM, GM]
    by_cases hg : GoodM u x
    · rw [if_pos hg, if_pos hg.1]
      exact prod_congr rfl fun i _ => if_pos (hg.2.1 i)
    · rw [if_neg hg]
      split_ifs with hc
      · have : ¬ ∀ i, PInj (EsM u x i) := fun h => hg ⟨hc, h, hcl⟩
        push Not at this
        obtain ⟨i, hi⟩ := this
        exact prod_eq_zero (mem_univ i) (if_neg hi)
      · rfl
  · simp only [hcl, and_false, GM]
    rw [if_neg (fun h => hcl h.2.2)]
    simp

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
omit [Fintype α] [Fintype β] in
lemma EsM_comp (c : Fin (nP u) → β) (φ : β → α) (i : Fin d) :
    EsM u (φ ∘ c) i = (EsM u c i).image (Prod.map φ φ) := by
  unfold EsM
  rw [biUnion_image]
  refine biUnion_congr rfl fun k _ => ?_
  exact Es_comp (u k) (cmp u c k) φ i

omit [Fintype β] in
lemma EsM_range (c : Fin (nP u) → β) (i : Fin d) (p : β × β) (hp : p ∈ EsM u c i) :
    p.1 ∈ Set.range c ∧ p.2 ∈ Set.range c := by
  obtain ⟨k, -, hk⟩ := mem_biUnion.1 hp
  have h := Es_range (u k) (cmp u c k) i p hk
  obtain ⟨⟨j1, hj1⟩, ⟨j2, hj2⟩⟩ := h
  exact ⟨⟨_, hj1⟩, ⟨_, hj2⟩⟩

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable (c : Fin (nP u) → β) (φ : β → α) (hφ : Set.InjOn φ (Set.range c))
include hφ
omit [Fintype α] [Fintype β] in
lemma card_EsM_comp (i : Fin d) : (EsM u (φ ∘ c) i).card = (EsM u c i).card := by
  rw [EsM_comp]
  refine card_image_of_injOn fun p hp q hq hpq => ?_
  have hp' := EsM_range u c i p hp
  have hq' := EsM_range u c i q hq
  simp only [Prod.map, Prod.mk.injEq] at hpq
  exact Prod.ext (hφ hp'.1 hq'.1 hpq.1) (hφ hp'.2 hq'.2 hpq.2)

lemma goodM_comp : GoodM u (φ ∘ c) ↔ GoodM u c := by
  have key : ∀ s t, φ (c s) = φ (c t) ↔ c s = c t := fun s t =>
    hφ.eq_iff ⟨s, rfl⟩ ⟨t, rfl⟩
  have hP : ∀ i, PInj (EsM u (φ ∘ c) i) ↔ PInj (EsM u c i) := by
    intro i
    rw [EsM_comp]
    unfold PInj
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Prod.map_fst,
      Prod.map_snd]
    refine forall₂_congr fun p hp => forall₂_congr fun q hq => ?_
    have hp' := EsM_range u c i p hp
    have hq' := EsM_range u c i q hq
    rw [hφ.eq_iff hp'.1 hq'.1, hφ.eq_iff hp'.2 hq'.2]
  unfold GoodM ConsM ClM Cons cmp
  simp only [Function.comp, key, hP]

lemma GM_comp (N : ℕ) : GM u N (φ ∘ c) = GM u N c := by
  unfold GM
  simp only [goodM_comp u c φ hφ, card_EsM_comp u c φ hφ]

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
variable {α : Type*} [DecidableEq α]
lemma sum_card_EsM_le (x : Fin (nP u) → α) : ∑ i, (EsM u x i).card ≤ ∑ k, (u k).length := by
  calc ∑ i, (EsM u x i).card ≤ ∑ i, ∑ k, (Es (u k) (cmp u x k) i).card :=
        sum_le_sum fun i _ => card_biUnion_le
    _ = ∑ k, ∑ i, (Es (u k) (cmp u x k) i).card := sum_comm
    _ ≤ ∑ k, (u k).length := sum_le_sum fun k _ => sum_card_Es_le (u k) _

lemma U_Ed_rel (w : List (Letter d)) (x : Fin (w.length + 1) → α) (hc : Cons w x)
    (BU : Finset α) (BE : Finset (α × α)) (hB : ∀ p ∈ BE, p.1 ∈ BU ∧ p.2 ∈ BU) :
    ∀ k, k ≤ w.length → (BU ∪ U w x k).card + BE.card ≤ (BE ∪ Ed w x k).card + BU.card + 1
  | 0, _ => by
      have : U w x 0 ⊆ {x 0} := by
        intro a ha
        obtain ⟨t, ht, rfl⟩ := mem_image.1 ha
        have : t = 0 := Fin.ext (by have := (mem_filter.1 ht).2; simp only [Fin.val_zero]; omega)
        simp [this]
      have h1 : (BU ∪ U w x 0).card ≤ BU.card + 1 :=
        (card_le_card (union_subset_union (le_refl BU) this)).trans
          ((card_union_le _ _).trans (by simp))
      have h2 : BE.card ≤ (BE ∪ Ed w x 0).card := card_le_card subset_union_left
      omega
  | k + 1, hk => by
      have ih := U_Ed_rel w x hc BU BE hB k (by omega)
      let t : Fin w.length := ⟨k, by omega⟩
      have hU : U w x (k + 1) ⊆ insert (x t.succ) (U w x k) := by
        intro a ha
        obtain ⟨s, hs, rfl⟩ := mem_image.1 ha
        have hs := (mem_filter.1 hs).2
        rcases Nat.lt_or_ge s.val (k + 1) with h | h
        · exact mem_insert_of_mem (mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by omega⟩))
        · have : s = t.succ := Fin.ext (by simp [t]; omega)
          rw [this]; exact mem_insert_self _ _
      have hE : Ed w x k ⊆ Ed w x (k + 1) := by
        intro p hp
        obtain ⟨s, hs, rfl⟩ := mem_image.1 hp
        have hs := (mem_filter.1 hs).2
        exact mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by omega, hs.2⟩)
      have hE' : BE ∪ Ed w x k ⊆ BE ∪ Ed w x (k + 1) := union_subset_union (le_refl BE) hE
      by_cases hmem : x t.succ ∈ BU ∪ U w x k
      · have hsub : BU ∪ U w x (k + 1) ⊆ BU ∪ U w x k := by
          intro a ha
          rcases mem_union.1 ha with h | h
          · exact mem_union_left _ h
          · rcases mem_insert.1 (hU h) with h' | h'
            · rw [h']; exact hmem
            · exact mem_union_right _ h'
        have := card_le_card hsub
        have := card_le_card hE'
        omega
      · have hmemU : x t.succ ∉ U w x k := fun h => hmem (mem_union_right _ h)
        have hcs : x t.castSucc ∈ U w x k :=
          mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp [t]⟩)
        have hl : lab (w.get t) ≠ none := by
          intro hl
          apply hmemU
          have hnone : w.get t = none := by
            generalize w.get t = l at hl
            rcases l with _ | j | j <;> simp_all [lab]
          rw [← hc t hnone]; exact hcs
        set e := edge (w.get t) (x t.castSucc) (x t.succ) with he
        have hnew : e ∉ BE ∪ Ed w x k := by
          intro h
          rcases mem_union.1 h with h | h
          · have := hB e h
            rcases edge_cases (w.get t) (x t.castSucc) (x t.succ) with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [← he] at e2; rw [e2] at this; exact hmem (mem_union_left _ this.2)
            · rw [← he] at e1; rw [e1] at this; exact hmem (mem_union_left _ this.1)
          · have := Ed_mem_U w x k e h
            rcases edge_cases (w.get t) (x t.castSucc) (x t.succ) with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [← he] at e2; rw [e2] at this; exact hmemU this.2
            · rw [← he] at e1; rw [e1] at this; exact hmemU this.1
        have hsub : insert e (BE ∪ Ed w x k) ⊆ BE ∪ Ed w x (k + 1) := by
          refine insert_subset ?_ hE'
          exact mem_union_right _ (mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, by simp [t], hl⟩))
        have h3 := card_le_card hsub
        rw [card_insert_of_notMem hnew] at h3
        have hU' : BU ∪ U w x (k + 1) ⊆ insert (x t.succ) (BU ∪ U w x k) := by
          intro a ha
          rcases mem_union.1 ha with h | h
          · exact mem_insert_of_mem (mem_union_left _ h)
          · rcases mem_insert.1 (hU h) with h' | h'
            · rw [h']; exact mem_insert_self _ _
            · exact mem_insert_of_mem (mem_union_right _ h')
        have h4 := card_le_card hU'
        have h5 := card_insert_le (x t.succ) (BU ∪ U w x k)
        omega

lemma card_biUnion_U_le (x : Fin (nP u) → α) (hc : ConsM u x) (S : Finset ι) :
    (S.biUnion fun k => U (u k) (cmp u x k) (u k).length).card ≤
      (S.biUnion fun k => Ed (u k) (cmp u x k) (u k).length).card + S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    rw [biUnion_insert, biUnion_insert, card_insert_of_notMem hk]
    have hB : ∀ p ∈ S.biUnion (fun k => Ed (u k) (cmp u x k) (u k).length),
        p.1 ∈ S.biUnion (fun k => U (u k) (cmp u x k) (u k).length) ∧
        p.2 ∈ S.biUnion (fun k => U (u k) (cmp u x k) (u k).length) := by
      intro p hp
      obtain ⟨k', hk', hp'⟩ := mem_biUnion.1 hp
      have := Ed_mem_U (u k') (cmp u x k') _ p hp'
      exact ⟨mem_biUnion.2 ⟨k', hk', this.1⟩, mem_biUnion.2 ⟨k', hk', this.2⟩⟩
    have h := U_Ed_rel (u k) (cmp u x k) (hc k) _ _ hB (u k).length le_rfl
    rw [union_comm (U (u k) (cmp u x k) (u k).length),
      union_comm (Ed (u k) (cmp u x k) (u k).length)]
    omega

lemma nvM_le (x : Fin (nP u) → α) (hc : ConsM u x) :
    nv x ≤ ∑ i, (EsM u x i).card + Fintype.card ι := by
  have h1 : univ.image x = univ.biUnion fun k => U (u k) (cmp u x k) (u k).length := by
    ext a
    simp only [mem_image, mem_univ, true_and, mem_biUnion, U, mem_filter]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨((eP u).symm v).1, ((eP u).symm v).2, Nat.lt_succ_iff.1 ((eP u).symm v).2.2, ?_⟩
      simp [cmp]
    · rintro ⟨k, j, -, rfl⟩
      exact ⟨_, rfl⟩
  have h2 : (univ.biUnion fun k => Ed (u k) (cmp u x k) (u k).length) ⊆
      univ.biUnion (EsM u x) := by
    intro p hp
    obtain ⟨k, -, hp⟩ := mem_biUnion.1 hp
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hp
    obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.1 (mem_filter.1 ht).2.2
    exact mem_biUnion.2 ⟨i, mem_univ _, mem_biUnion.2 ⟨k, mem_univ _,
      mem_image_of_mem _ (mem_filter.2 ⟨mem_univ _, hi⟩)⟩⟩
  have h3 := card_biUnion_U_le u x hc univ
  have h4 := (card_le_card h2).trans card_biUnion_le
  rw [nv, h1]
  rw [card_univ] at h3
  omega

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ι → List (Letter d))
theorem exists_prod_fixCount_expectation :
    ∃ M : Multiset (ℕ × (Fin d → ℕ)),
      (∀ p ∈ M, p.1 ≤ ∑ i, p.2 i + Fintype.card ι ∧ ∑ i, p.2 i ≤ ∑ k, (u k).length) ∧
      ∀ N : ℕ, ∑ k, (u k).length ≤ N →
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            ((∏ k, fixCount (wordPerm σ (u k)) : ℕ) : ℝ)) =
          (M.map fun p => (N.descFactorial p.1 : ℝ) / ∏ i, (N.descFactorial (p.2 i) : ℝ)).sum := by
  let C : Finset (Fin (nP u) → Fin (nP u)) :=
    (univ.filter fun c => canon c = c).filter (GoodM u)
  refine ⟨C.val.map fun c => (nv c, fun i => (EsM u c i).card), ?_, ?_⟩
  · intro p hp
    obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hp
    have hc := (mem_filter.1 hc).2
    exact ⟨nvM_le u c hc.1, sum_card_EsM_le u c⟩
  · intro N hL
    have h1 : ∑ σ : Fin d → Equiv.Perm (Fin N), ∏ k, fixCount (wordPerm σ (u k)) =
        ∑ c ∈ (univ.filter fun c : Fin (nP u) → Fin (nP u) => canon c = c),
          if GoodM u c then N.descFactorial (nv c) * ∏ i, (N - (EsM u c i).card).factorial
          else 0 := by
      rw [sum_prod_fixCount, ← sum_fiberwise_of_maps_to (s := univ)
        (t := univ.filter fun c : Fin (nP u) → Fin (nP u) => canon c = c)
        (g := canon) (fun x _ => mem_filter.2 ⟨mem_univ _, canon_canon x⟩)]
      refine sum_congr rfl fun c hc => ?_
      have hc := (mem_filter.1 hc).2
      have hG : ∀ x ∈ univ.filter fun x : Fin (nP u) → Fin N => canon x = c,
          GM u N x = GM u N c := by
        intro x hx
        have hx := (mem_filter.1 hx).2
        rw [← hx]
        conv_lhs => rw [← comp_canon x]
        exact GM_comp u (canon x) x (injOn_canon x) N
      rw [sum_congr rfl hG, sum_const, card_fiber c hc, Fintype.card_fin, smul_eq_mul, GM]
      split_ifs <;> simp
    unfold uniformExp
    rw [← Nat.cast_sum, h1, ← sum_filter, Multiset.map_map, ← Finset.sum_eq_multiset_sum]
    have hcard : (Fintype.card (Fin d → Equiv.Perm (Fin N)) : ℝ) = (N.factorial : ℝ) ^ d := by
      simp [Fintype.card_perm]
    rw [hcard, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun c _ => ?_
    have he : ∀ i, (EsM u c i).card ≤ N := fun i =>
      (single_le_sum (fun j _ => Nat.zero_le _) (mem_univ i)).trans
        ((sum_card_EsM_le u c).trans hL)
    have hfac : (N.factorial : ℝ) ^ d =
        (∏ i, (N.descFactorial (EsM u c i).card : ℝ)) *
          ∏ i, ((N - (EsM u c i).card).factorial : ℝ) := by
      rw [← prod_mul_distrib,
        show (N.factorial : ℝ) ^ d = ∏ _i : Fin d, (N.factorial : ℝ) by simp]
      refine prod_congr rfl fun i _ => ?_
      rw [← Nat.cast_mul, mul_comm, Nat.factorial_mul_descFactorial (he i)]
    simp only [Function.comp, Nat.cast_mul, Nat.cast_prod]
    rw [hfac, mul_div_mul_right _ _ (prod_ne_zero_iff.2 fun i _ => by positivity)]

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartR
open StrongConv StrongConv.Q202L1 Finset
/-- The linear factor `1 - j X`. -/
abbrev L (j : ℕ) : ℝ[X] := 1 - (j : ℝ[X]) * X

lemma L_eq (j : ℕ) : L j = C (-(j : ℝ)) * X + C 1 := by
  simp [L, sub_eq_add_neg, add_comm, map_natCast]

lemma natDegree_L (j : ℕ) (hj : 1 ≤ j) : (L j).natDegree = 1 := by
  rw [L_eq]
  apply natDegree_linear
  have : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  simpa using this

lemma natDegree_L_le (j : ℕ) : (L j).natDegree ≤ 1 := by
  rw [L_eq]; exact natDegree_linear_le

lemma eval_L (j : ℕ) (x : ℝ) : (L j).eval x = 1 - j * x := by
  simp [L]

lemma natDegree_gPoly (d q : ℕ) :
    (gPoly d q).natDegree = ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := by
  unfold gPoly
  rw [natDegree_prod]
  · apply sum_congr rfl
    intro j hj
    rw [mem_Ico] at hj
    rw [natDegree_pow, natDegree_L j hj.1, mul_one]
  · intro j hj
    rw [mem_Ico] at hj
    apply pow_ne_zero
    intro h
    have := natDegree_L j hj.1
    change L j = 0 at h
    rw [h] at this; simp at this

lemma factor_pos (j q N : ℕ) (hj : j < q) (hN : q ≤ N) (hN1 : 1 ≤ N) :
    0 < 1 - (j : ℝ) * (1 / (N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have : (j : ℝ) < N := by exact_mod_cast (by omega : j < N)
  rw [mul_one_div, sub_pos, div_lt_one hNpos]
  exact this

lemma eval_prod_pos (q N : ℕ) (hN : q ≤ N) (hN1 : 1 ≤ N) (s : Finset ℕ) (hs : ∀ j ∈ s, j < q)
    (k : ℕ → ℕ) : 0 < (∏ j ∈ s, L j ^ k j).eval (1 / (N : ℝ)) := by
  rw [eval_prod]
  apply prod_pos
  intro j hj
  rw [eval_pow, eval_L]
  exact pow_pos (factor_pos j q N (hs j hj) hN hN1) _

theorem gPoly_eval_ne_zero (d q N : ℕ) (hN : q ≤ N) (hN1 : 1 ≤ N) :
    (gPoly d q).eval (1 / (N : ℝ)) ≠ 0 := by
  have := eval_prod_pos q N hN hN1 (Ico 1 q) (fun j hj => (mem_Ico.1 hj).2)
    (fun j => min d (q / (j + 1)))
  exact ne_of_gt this

lemma descFactorial_eq (N m : ℕ) (hN1 : 1 ≤ N) :
    (N.descFactorial m : ℝ) = (N : ℝ) ^ m * ∏ j ∈ Ico 1 m, (1 - (j : ℝ) * (1 / (N : ℝ))) := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  induction m with
  | zero => simp
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    rw [Nat.descFactorial_succ, prod_Ico_succ_top (by omega : 1 ≤ m), Nat.cast_mul]
    by_cases hmN : m ≤ N
    · rw [Nat.cast_sub hmN, ih]
      field_simp
      ring
    · have h0 : N.descFactorial m = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
      have hih : (N : ℝ) ^ m * ∏ j ∈ Ico 1 m, (1 - (j : ℝ) * (1 / (N : ℝ))) = 0 := by
        rw [← ih, h0]; simp
      rw [h0]
      simp only [Nat.cast_zero, mul_zero]
      calc (0 : ℝ) = (N : ℝ) * ((N : ℝ) ^ m * ∏ j ∈ Ico 1 m, (1 - (j : ℝ) * (1 / (N : ℝ))))
            * (1 - (m : ℝ) * (1 / (N : ℝ))) := by rw [hih]; ring
        _ = _ := by ring

lemma filter_lt_Ico (e q : ℕ) (he : e ≤ q) : (Ico 1 q).filter (· < e) = Ico 1 e := by
  ext j; simp only [mem_filter, mem_Ico]; omega

lemma prod_prod_Ico {d : ℕ} (e : Fin d → ℕ) (q : ℕ) (he : ∀ i, e i ≤ q) (f : ℕ → ℝ) :
    ∏ i, ∏ j ∈ Ico 1 (e i), f j =
      ∏ j ∈ Ico 1 q, f j ^ (univ.filter (fun i => j < e i)).card := by
  have : ∀ i, ∏ j ∈ Ico 1 (e i), f j = ∏ j ∈ Ico 1 q, (if j < e i then f j else 1) := by
    intro i
    rw [← prod_filter, filter_lt_Ico _ _ (he i)]
  simp_rw [this]
  rw [Finset.prod_comm]
  apply prod_congr rfl
  intro j _
  rw [← prod_filter, prod_const]

theorem exists_poly_term_s (d q s : ℕ) (hq : 1 ≤ q) (p : ℕ × (Fin d → ℕ))
    (h2 : p.1 ≤ ∑ i, p.2 i + s) (h3 : ∑ i, p.2 i ≤ q) :
    ∃ φ : ℝ[X], φ.natDegree ≤ (gPoly d q).natDegree + min d q + s ∧
      ∀ N : ℕ, q ≤ N → 1 ≤ N →
        (1 / (N : ℝ)) ^ s * ((N.descFactorial p.1 : ℝ) / ∏ i, (N.descFactorial (p.2 i) : ℝ)) =
          φ.eval (1 / (N : ℝ)) / (gPoly d q).eval (1 / (N : ℝ)) := by
  obtain ⟨v, e⟩ := p
  simp only at h2 h3 ⊢
  set E := ∑ i, e i with hE
  have he : ∀ i, e i ≤ q := fun i =>
    le_trans (single_le_sum (fun i _ => Nat.zero_le (e i)) (mem_univ i)) h3
  set c : ℕ → ℕ := fun j => (univ.filter (fun i => j < e i)).card with hc
  set dd : ℕ → ℕ := fun j => min d (q / (j + 1)) with hdd
  have hcd : ∀ j, c j ≤ dd j := by
    intro j
    apply le_min
    · exact (card_filter_le _ _).trans (by simp)
    · rw [Nat.le_div_iff_mul_le (by omega)]
      calc c j * (j + 1) = ∑ i ∈ univ.filter (fun i => j < e i), (j + 1) := by
            simp [hc]
        _ ≤ ∑ i ∈ univ.filter (fun i => j < e i), e i := by
            apply sum_le_sum; intro i hi; simp at hi; omega
        _ ≤ E := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
        _ ≤ q := h3
  have hsumc : ∑ j ∈ range q, c j = E := by
    simp only [hc, card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [← card_filter]
    have : (range q).filter (fun j => j < e i) = range (e i) := by
      ext j; simp only [mem_filter, mem_range]; have := he i; omega
    rw [this, card_range]
  have hc0 : c 0 ≤ min d q := by
    apply le_min
    · exact (card_filter_le _ _).trans (by simp)
    · calc c 0 = ∑ i ∈ univ.filter (fun i => 0 < e i), 1 := by simp [hc]
        _ ≤ ∑ i ∈ univ.filter (fun i => 0 < e i), e i := by
            apply sum_le_sum; intro i hi; simp at hi; omega
        _ ≤ E := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; omega)
        _ ≤ q := h3
  have hsplit : ∑ j ∈ range q, c j = c 0 + ∑ j ∈ Ico 1 q, c j := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
  refine ⟨X ^ (E + s - v) * (∏ j ∈ Ico 1 v, L j) * ∏ j ∈ Ico 1 q, L j ^ (dd j - c j), ?_, ?_⟩
  · rw [natDegree_gPoly]
    have hA : (∏ j ∈ Ico 1 v, L j).natDegree ≤ v - 1 := by
      refine (natDegree_prod_le _ _).trans ?_
      calc ∑ j ∈ Ico 1 v, (L j).natDegree ≤ ∑ j ∈ Ico 1 v, 1 :=
            sum_le_sum (fun j _ => natDegree_L_le j)
        _ = v - 1 := by simp
    have hR : (∏ j ∈ Ico 1 q, L j ^ (dd j - c j)).natDegree ≤ ∑ j ∈ Ico 1 q, (dd j - c j) := by
      refine (natDegree_prod_le _ _).trans ?_
      apply sum_le_sum
      intro j _
      refine natDegree_pow_le.trans ?_
      calc (dd j - c j) * (L j).natDegree ≤ (dd j - c j) * 1 :=
            Nat.mul_le_mul_left _ (natDegree_L_le j)
        _ = _ := mul_one _
    have hX : (X ^ (E + s - v) : ℝ[X]).natDegree ≤ E + s - v := natDegree_X_pow_le _
    have hsub : ∑ j ∈ Ico 1 q, (dd j - c j) + ∑ j ∈ Ico 1 q, c j = ∑ j ∈ Ico 1 q, dd j := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _; have := hcd j; omega
    refine (natDegree_mul_le).trans ?_
    have := (natDegree_mul_le (p := (X ^ (E + s - v) : ℝ[X])) (q := ∏ j ∈ Ico 1 v, L j))
    have hdd : ∑ j ∈ Ico 1 q, dd j = ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := rfl
    omega
  · intro N hN hN1
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    set x : ℝ := 1 / (N : ℝ) with hx
    have hden : ∏ i, (N.descFactorial (e i) : ℝ) =
        (N : ℝ) ^ E * ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j := by
      simp_rw [descFactorial_eq N _ hN1]
      rw [prod_mul_distrib, prod_pow_eq_pow_sum, prod_prod_Ico e q he]
    have hCpos : 0 < ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j := by
      apply prod_pos; intro j hj
      exact pow_pos (factor_pos j q N (mem_Ico.1 hj).2 hN hN1) _
    have hRpos : 0 < ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      apply prod_pos; intro j hj
      exact pow_pos (factor_pos j q N (mem_Ico.1 hj).2 hN hN1) _
    have hg : (gPoly d q).eval x = (∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j) *
        ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      unfold gPoly
      rw [eval_prod, ← prod_mul_distrib]
      apply prod_congr rfl
      intro j _
      rw [← pow_add, eval_pow]
      change (L j).eval x ^ _ = _
      rw [eval_L]
      congr 1
      have := hcd j
      simp only [hdd] at this ⊢
      omega
    have hφ : (X ^ (E + s - v) * (∏ j ∈ Ico 1 v, L j) *
        ∏ j ∈ Ico 1 q, L j ^ (dd j - c j)).eval x =
        x ^ (E + s - v) * (∏ j ∈ Ico 1 v, (1 - (j : ℝ) * x)) *
          ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j) := by
      simp [eval_prod]
    rw [hφ, hg, hden, descFactorial_eq N v hN1]
    have hpow : x ^ s * (N : ℝ) ^ v = x ^ (E + s - v) * (N : ℝ) ^ E := by
      rw [hx, one_div, inv_pow, inv_pow, inv_mul_eq_div, inv_mul_eq_div,
        div_eq_div_iff (by positivity) (by positivity), ← pow_add, ← pow_add]
      congr 1
      omega
    rw [← hx, mul_div_assoc', div_eq_div_iff (by positivity) (by positivity)]
    calc x ^ s * ((N : ℝ) ^ v * ∏ j ∈ Ico 1 v, (1 - (j : ℝ) * x)) *
          ((∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j) *
            ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j))
        = (x ^ s * (N : ℝ) ^ v) * (∏ j ∈ Ico 1 v, (1 - (j : ℝ) * x)) *
          ((∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ c j) *
            ∏ j ∈ Ico 1 q, (1 - (j : ℝ) * x) ^ (dd j - c j)) := by ring
      _ = _ := by rw [hpow]; ring

/-- `#{j < d : (j+1) b ≤ q} = min d (q / b)`. -/
lemma card_filter_mul_le (d b q : ℕ) (hb : 0 < b) :
    ((range d).filter (fun j => (j + 1) * b ≤ q)).card = min d (q / b) := by
  have : (range d).filter (fun j => (j + 1) * b ≤ q) = range (min d (q / b)) := by
    ext j
    simp only [mem_filter, mem_range, lt_min_iff]
    rw [← Nat.le_div_iff_mul_le hb]
    omega
  rw [this, card_range]

theorem natDegree_gPoly_add_min_le (d q : ℕ) (hq : 1 ≤ q) :
    (((gPoly d q).natDegree + min d q : ℕ) : ℝ) ≤ q * (1 + Real.log d) := by
  have key : (gPoly d q).natDegree + min d q = ∑ j ∈ range d, q / (j + 1) := by
    rw [natDegree_gPoly]
    have h1 : ∑ m ∈ range q, min d (q / (m + 1)) =
        min d q + ∑ j ∈ Ico 1 q, min d (q / (j + 1)) := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega)]
      simp
    rw [add_comm, ← h1]
    have h2 : ∀ m, min d (q / (m + 1)) =
        ∑ j ∈ range d, if (j + 1) * (m + 1) ≤ q then 1 else 0 := by
      intro m
      rw [← card_filter_mul_le d (m + 1) q (by omega), card_filter]
    have h3 : ∀ j, q / (j + 1) =
        ∑ m ∈ range q, if (j + 1) * (m + 1) ≤ q then 1 else 0 := by
      intro j
      have := card_filter_mul_le q (j + 1) q (by omega)
      rw [min_eq_right (Nat.div_le_self _ _), card_filter] at this
      rw [← this]
      apply sum_congr rfl; intro m _; rw [mul_comm]
    simp_rw [h2, h3]
    rw [sum_comm]
  rw [key]
  have hq0 : (0 : ℝ) ≤ q := by positivity
  calc ((∑ j ∈ range d, q / (j + 1) : ℕ) : ℝ) ≤ ∑ j ∈ range d, (q : ℝ) / ((j : ℝ) + 1) := by
        push_cast
        apply sum_le_sum; intro j _
        have := Nat.cast_div_le (α := ℝ) (m := q) (n := j + 1)
        push_cast at this
        exact this
    _ = q * (harmonic d : ℝ) := by
        simp only [harmonic]
        push_cast
        rw [mul_sum]
        apply sum_congr rfl; intro j _
        field_simp
    _ ≤ q * (1 + Real.log d) := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log d) hq0

/-! ## Per-word rationality -/
open Op in
lemma wordPerm_lift {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    FreeGroup.lift σ (fw w) = wordPerm σ (w.toList.map some) := by
  unfold fw wordPerm
  generalize w.toList = l
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    congr 1
    rcases a with i | i <;> simp [letterPerm]

lemma wordPerm_append {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (a b : List (Letter d)) :
    wordPerm σ (a ++ b) = wordPerm σ a * wordPerm σ b := by
  simp [wordPerm, List.map_append, List.prod_append]

lemma wordPerm_rep {d N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (u : List (Letter d)) (n : ℕ) :
    wordPerm σ (List.replicate n u).flatten = (wordPerm σ u) ^ n := by
  induction n with
  | zero => simp [wordPerm]
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, wordPerm_append, ih, pow_succ']

lemma length_rep {d : ℕ} (u : List (Letter d)) (n : ℕ) :
    ((List.replicate n u).flatten).length = n * u.length := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; ring

lemma prod_xi {d r N : ℕ} (σ : Fin d → Equiv.Perm (Fin N)) (u : List (Letter d))
    (a : Fin r →₀ ℕ) :
    ∏ i : Fin r, (xi ((i : ℕ) + 1) (wordPerm σ u)) ^ (a i) =
      ∏ k : (Σ i : Fin r, Fin (a i)),
        fixCount (wordPerm σ (List.replicate ((k.1 : ℕ) + 1) u).flatten) := by
  rw [Fintype.prod_sigma]
  refine prod_congr rfl fun i _ => ?_
  dsimp only
  rw [prod_const, card_univ, Fintype.card_fin, wordPerm_rep]
  rfl

theorem natDegree_multiset_sum_le' {ι : Type*} (M : Multiset ι) (φ : ι → ℝ[X]) (B : ℕ)
    (h : ∀ p ∈ M, (φ p).natDegree ≤ B) : (M.map φ).sum.natDegree ≤ B := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons]
    refine (natDegree_add_le _ _).trans (max_le (h a (Multiset.mem_cons_self _ _)) ?_)
    exact ih fun p hp => h p (Multiset.mem_cons_of_mem hp)

lemma rat_monomial {d r : ℕ} (u : List (Letter d)) (a : Fin r →₀ ℕ) (L : ℕ) (hL : 1 ≤ L)
    (hlen : (∑ i : Fin r, ((i : ℕ) + 1) * a i) * u.length ≤ L) :
    ∃ Φ : ℝ[X], Φ.natDegree ≤ (gPoly d L).natDegree + min d L + ∑ i, a i ∧
      ∀ N : ℕ, L ≤ N →
        (1 / (N : ℝ)) ^ (∑ i, a i) * uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((∏ i : Fin r, (xi ((i : ℕ) + 1) (wordPerm σ u)) ^ (a i) : ℕ) : ℝ)) =
        Φ.eval (1 / (N : ℝ)) / (gPoly d L).eval (1 / (N : ℝ)) := by
  set Uw : (Σ i : Fin r, Fin (a i)) → List (Letter d) :=
    fun k => (List.replicate ((k.1 : ℕ) + 1) u).flatten with hUw
  obtain ⟨M, hM, hE⟩ := exists_prod_fixCount_expectation Uw
  have hcard : Fintype.card (Σ i : Fin r, Fin (a i)) = ∑ i, a i := by
    simp [Fintype.card_sigma]
  have hlenU : ∑ k, (Uw k).length ≤ L := by
    calc ∑ k, (Uw k).length = ∑ i : Fin r, ((i : ℕ) + 1) * a i * u.length := by
          rw [Fintype.sum_sigma]
          refine sum_congr rfl fun i _ => ?_
          simp only [hUw, length_rep, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
          ring
      _ ≤ L := by rw [← sum_mul]; exact hlen
  have hφ : ∀ p ∈ M, ∃ φ : ℝ[X], φ.natDegree ≤ (gPoly d L).natDegree + min d L + ∑ i, a i ∧
      ∀ N : ℕ, L ≤ N → 1 ≤ N →
        (1 / (N : ℝ)) ^ (∑ i, a i) *
            ((N.descFactorial p.1 : ℝ) / ∏ i, (N.descFactorial (p.2 i) : ℝ)) =
          φ.eval (1 / (N : ℝ)) / (gPoly d L).eval (1 / (N : ℝ)) := by
    intro p hp
    have h1 := (hM p hp).1
    rw [hcard] at h1
    exact exists_poly_term_s d L (∑ i, a i) hL p h1 ((hM p hp).2.trans hlenU)
  choose! φ hφdeg hφeq using hφ
  refine ⟨(M.map φ).sum, natDegree_multiset_sum_le' M φ _ hφdeg, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := hL.trans hN
  have hne := gPoly_eval_ne_zero d L N hN hN1
  have hfun : (fun σ : Fin d → Equiv.Perm (Fin N) =>
      ((∏ i : Fin r, (xi ((i : ℕ) + 1) (wordPerm σ u)) ^ (a i) : ℕ) : ℝ)) =
      fun σ => ((∏ k, fixCount (wordPerm σ (Uw k)) : ℕ) : ℝ) := by
    funext σ; rw [prod_xi]
  rw [hfun, hE N (hlenU.trans hN), eval_multisetSum, Multiset.map_map, eq_div_iff hne,
    ← Multiset.sum_map_mul_left, ← Multiset.sum_map_mul_right]
  congr 1
  refine Multiset.map_congr rfl fun p hp => ?_
  simp only [Function.comp]
  rw [hφeq p hp N hN hN1, div_mul_cancel₀ _ hne]

lemma abs_eval_le_of_abs_le_one (p : ℝ[X]) (x : ℝ) (hx : |x| ≤ 1) :
    |p.eval x| ≤ ∑ i ∈ range (p.natDegree + 1), |p.coeff i| := by
  rw [eval_eq_sum_range]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hx)

lemma X_pow_dvd_of_bound (m : ℕ) : ∀ (F : ℝ[X]) (C : ℝ) (N₁ : ℕ),
    (∀ N : ℕ, N₁ ≤ N → |F.eval (1 / (N : ℝ))| ≤ C * (1 / (N : ℝ)) ^ m) → X ^ m ∣ F := by
  induction m with
  | zero => intros; simp
  | succ m ih =>
    intro F C N₁ hF
    have hF' : ∀ N : ℕ, max N₁ 1 ≤ N → |F.eval (1 / (N : ℝ))| ≤ |C| * (1 / (N : ℝ)) ^ m := by
      intro N hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
      have hx0 : 0 ≤ 1 / (N : ℝ) := by positivity
      have hx1 : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hN1
      calc |F.eval (1 / (N : ℝ))| ≤ C * (1 / (N : ℝ)) ^ (m + 1) :=
            hF N ((le_max_left _ _).trans hN)
        _ ≤ |C| * (1 / (N : ℝ)) ^ (m + 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| * (1 / (N : ℝ)) ^ m :=
            mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hx0 hx1 (by omega)) (abs_nonneg C)
    obtain ⟨G, rfl⟩ := ih F |C| (max N₁ 1) hF'
    have hG : ∀ N : ℕ, max N₁ 1 ≤ N → |G.eval (1 / (N : ℝ))| ≤ C * (1 / (N : ℝ)) := by
      intro N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (le_max_right _ _).trans hN
      have h1 := hF N ((le_max_left _ _).trans hN)
      rw [eval_mul, eval_pow, eval_X, abs_mul, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / N), pow_succ] at h1
      have hpos : (0 : ℝ) < (1 / (N : ℝ)) ^ m := by positivity
      rw [show C * ((1 / (N : ℝ)) ^ m * (1 / N)) = (1 / (N : ℝ)) ^ m * (C * (1 / N)) by ring] at h1
      exact le_of_mul_le_mul_left h1 hpos
    have hlim1 : Tendsto (fun N : ℕ => |G.eval (1 / (N : ℝ))|) atTop (𝓝 |G.eval 0|) :=
      ((G.continuous.tendsto 0).comp tendsto_one_div_atTop_nhds_zero_nat).abs
    have hlim2 : Tendsto (fun N : ℕ => C * (1 / (N : ℝ))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_atTop_nhds_zero_nat.const_mul C
    have h0 : |G.eval 0| ≤ 0 :=
      le_of_tendsto_of_tendsto hlim1 hlim2 (eventually_atTop.2 ⟨max N₁ 1, hG⟩)
    have hG0 : G.eval 0 = 0 := abs_nonpos_iff.1 h0
    have hX : X ∣ G := by
      rw [X_dvd_iff, coeff_zero_eq_eval_zero]; exact hG0
    rw [pow_succ]
    exact mul_dvd_mul_left _ hX

lemma uniformExp_mul_left {X : Type*} [Fintype X] (c : ℝ) (f : X → ℝ) :
    uniformExp (fun x => c * f x) = c * uniformExp f := by
  unfold uniformExp; rw [← Finset.mul_sum, mul_div_assoc]

lemma uniformExp_div_const {X : Type*} [Fintype X] (f : X → ℝ) (c : ℝ) :
    uniformExp (fun x => f x / c) = uniformExp f / c := by
  unfold uniformExp; rw [← Finset.sum_div]; ring

lemma abs_uniformExp_le {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (B : ℝ)
    (h : ∀ x, |f x| ≤ B) : |uniformExp f| ≤ B := by
  unfold uniformExp
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
  calc |∑ x, f x| ≤ ∑ x, |f x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : X, B := sum_le_sum fun x _ => h x
    _ = B * Fintype.card X := by simp [mul_comm]

open Op in
lemma chi_eq (π : StableRep) {N : ℕ} (hN : π.N₀ ≤ N) (g : Equiv.Perm (Fin N)) :
    chi π N g = ∑ a ∈ π.φ.support, MvPolynomial.coeff a π.φ *
      (((∏ i : Fin π.r, (xi ((i : ℕ) + 1) g) ^ (a i) : ℕ)) : ℂ) := by
  rw [chi, π.trace_eq N hN g, MvPolynomial.eval_eq']
  push_cast
  rfl

lemma re_mul_sum {ι : Type*} (s : Finset ι) (t : ℂ) (c : ι → ℂ) (n : ι → ℕ) :
    (t * ∑ a ∈ s, c a * (n a : ℂ)).re = ∑ a ∈ s, (t * c a).re * (n a : ℝ) := by
  rw [Finset.mul_sum, Complex.re_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [← mul_assoc]
  simp [Complex.mul_re]

lemma dim_bound (π : StableRep) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
    (π.dim N : ℝ) ≤ K * (N : ℝ) ^ π.alpha := by
  set p : ℂ[X] := MvPolynomial.aeval (fun _ : Fin π.r => (X : ℂ[X])) π.φ with hp
  refine ⟨∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖, by positivity, fun N hN hN1 => ?_⟩
  have hdim : (π.dim N : ℂ) = p.eval (N : ℂ) := by
    have h1 := π.trace_eq N hN 1
    have hxi : ∀ j, xi j (1 : Equiv.Perm (Fin N)) = N := by intro j; simp [xi]
    simp only [hxi, map_one] at h1
    rw [hp, ← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply]
    simp only [Polynomial.aeval_X]
    have he : (MvPolynomial.aeval fun _ : Fin π.r => (N : ℂ)) π.φ =
        MvPolynomial.eval (fun _ : Fin π.r => (N : ℂ)) π.φ := rfl
    rw [he, ← h1]
    simp
  have hα : π.alpha = p.natDegree := rfl
  have key : ‖(π.dim N : ℂ)‖ ≤ (∑ i ∈ range (p.natDegree + 1), ‖p.coeff i‖) *
      (N : ℝ) ^ π.alpha := by
    rw [hdim, eval_eq_sum_range]
    refine (norm_sum_le _ _).trans ?_
    rw [sum_mul]
    refine sum_le_sum fun i hi => ?_
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast hN1) ?_) (norm_nonneg _)
    rw [mem_range] at hi
    omega
  simpa using key

open Op in
theorem perWord (π : StableRep) : ∃ β : ℕ, ∀ {d : ℕ} (u : List (Letter d)) (t : ℂ) (L : ℕ),
    1 ≤ L → β * u.length ≤ L →
    ∃ F : ℝ[X], F.natDegree ≤ π.alpha + ((gPoly d L).natDegree + min d L) ∧
      ∀ N : ℕ, π.N₀ ≤ N → L ≤ N →
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          (t * chi π N (wordPerm σ u)).re / (N : ℝ) ^ π.alpha) =
          F.eval (1 / (N : ℝ)) / (gPoly d L).eval (1 / (N : ℝ)) := by
  classical
  obtain ⟨K, hK0, hK⟩ := dim_bound π
  refine ⟨π.φ.support.sup (fun a => ∑ i : Fin π.r, ((i : ℕ) + 1) * a i), ?_⟩
  intro d u t L hL hlen
  set β := π.φ.support.sup (fun a => ∑ i : Fin π.r, ((i : ℕ) + 1) * a i) with hβ
  set α := π.alpha with hα
  set S := β + α with hS
  set g := gPoly d L with hg
  have hβa : ∀ a ∈ π.φ.support, ∑ i : Fin π.r, ((i : ℕ) + 1) * a i ≤ β := fun a ha =>
    Finset.le_sup (f := fun a : Fin π.r →₀ ℕ => ∑ i : Fin π.r, ((i : ℕ) + 1) * a i) ha
  have hsa : ∀ a ∈ π.φ.support, ∑ i, a i ≤ β := fun a ha =>
    le_trans (sum_le_sum fun i _ => Nat.le_mul_of_pos_left (a i) (Nat.succ_pos _)) (hβa a ha)
  have hrat : ∀ a ∈ π.φ.support, ∃ Φ : ℝ[X], Φ.natDegree ≤ g.natDegree + min d L + ∑ i, a i ∧
      ∀ N : ℕ, L ≤ N → (1 / (N : ℝ)) ^ (∑ i, a i) *
          uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
            ((∏ i : Fin π.r, (xi ((i : ℕ) + 1) (wordPerm σ u)) ^ (a i) : ℕ) : ℝ)) =
        Φ.eval (1 / (N : ℝ)) / g.eval (1 / (N : ℝ)) := fun a ha =>
    rat_monomial u a L hL ((Nat.mul_le_mul_right _ (hβa a ha)).trans hlen)
  choose! Φ hΦdeg hΦeq using hrat
  set rr : (Fin π.r →₀ ℕ) → ℝ := fun a => (t * MvPolynomial.coeff a π.φ).re with hrr
  set F₁ : ℝ[X] := ∑ a ∈ π.φ.support, C (rr a) * X ^ (S - ∑ i, a i) * Φ a with hF₁
  have hF₁deg : F₁.natDegree ≤ S + (g.natDegree + min d L) := by
    refine natDegree_sum_le_of_forall_le _ _ fun a ha => ?_
    refine (natDegree_mul_le).trans ?_
    have h1 := natDegree_mul_le (p := C (rr a)) (q := (X ^ (S - ∑ i, a i) : ℝ[X]))
    have h2 : (C (rr a)).natDegree = 0 := natDegree_C _
    have h3 : (X ^ (S - ∑ i, a i) : ℝ[X]).natDegree ≤ S - ∑ i, a i := natDegree_X_pow_le _
    have h4 := hΦdeg a ha
    have h5 := hsa a ha
    omega
  set Y : ℕ → ℝ := fun N => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
    (t * chi π N (wordPerm σ u)).re) with hYdef
  have hYexp : ∀ N, π.N₀ ≤ N → Y N = ∑ a ∈ π.φ.support, rr a *
      uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
        ((∏ i : Fin π.r, (xi ((i : ℕ) + 1) (wordPerm σ u)) ^ (a i) : ℕ) : ℝ)) := by
    intro N hN
    simp only [hYdef]
    simp_rw [← uniformExp_mul_left]
    rw [← uniformExp_sum]
    congr 1
    funext σ
    rw [chi_eq π hN, re_mul_sum]
  have hY : ∀ N, π.N₀ ≤ N → L ≤ N →
      (1 / (N : ℝ)) ^ S * Y N = F₁.eval (1 / (N : ℝ)) / g.eval (1 / (N : ℝ)) := by
    intro N hN hLN
    rw [hYexp N hN, mul_sum, hF₁, eval_finsetSum, sum_div]
    refine sum_congr rfl fun a ha => ?_
    have hs := hsa a ha
    have hsplit : (1 / (N : ℝ)) ^ S =
        (1 / (N : ℝ)) ^ (S - ∑ i, a i) * (1 / (N : ℝ)) ^ (∑ i, a i) := by
      rw [← pow_add]; congr 1; omega
    rw [eval_mul, eval_mul, eval_C, eval_pow, eval_X, hsplit, mul_div_assoc,
      ← hΦeq a ha N hLN]
    ring
  set Gb := ∑ i ∈ range (g.natDegree + 1), |g.coeff i| with hGb
  have hbound : ∀ N : ℕ, max π.N₀ L ≤ N →
      |F₁.eval (1 / (N : ℝ))| ≤ (Gb * (‖t‖ * K)) * (1 / (N : ℝ)) ^ (S - α) := by
    intro N hN
    have hN0 : π.N₀ ≤ N := (le_max_left _ _).trans hN
    have hLN : L ≤ N := (le_max_right _ _).trans hN
    have hN1 : 1 ≤ N := hL.trans hLN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hne := gPoly_eval_ne_zero d L N hLN hN1
    have hx1 : |1 / (N : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), div_le_one hNpos]; exact_mod_cast hN1
    have hgN : |g.eval (1 / (N : ℝ))| ≤ Gb := abs_eval_le_of_abs_le_one g _ hx1
    haveI : Nonempty (Fin d → Equiv.Perm (Fin N)) := ⟨fun _ => 1⟩
    have hYb : |Y N| ≤ ‖t‖ * (K * (N : ℝ) ^ α) := by
      apply abs_uniformExp_le
      intro σ
      calc |(t * chi π N (wordPerm σ u)).re| ≤ ‖t * chi π N (wordPerm σ u)‖ :=
            Complex.abs_re_le_norm _
        _ = ‖t‖ * ‖chi π N (wordPerm σ u)‖ := norm_mul _ _
        _ ≤ ‖t‖ * (π.dim N : ℝ) := mul_le_mul_of_nonneg_left (norm_chi_le π N _) (norm_nonneg _)
        _ ≤ ‖t‖ * (K * (N : ℝ) ^ α) :=
            mul_le_mul_of_nonneg_left (hK N hN0 hN1) (norm_nonneg _)
    have hFeq : F₁.eval (1 / (N : ℝ)) = (1 / (N : ℝ)) ^ S * Y N * g.eval (1 / (N : ℝ)) := by
      rw [hY N hN0 hLN, div_mul_cancel₀ _ hne]
    rw [hFeq, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ S)]
    have hsplit : (1 / (N : ℝ)) ^ S = (1 / (N : ℝ)) ^ (S - α) * (1 / (N : ℝ)) ^ α := by
      rw [← pow_add]; congr 1; omega
    have h1 : (1 / (N : ℝ)) ^ α * |Y N| ≤ ‖t‖ * K := by
      calc (1 / (N : ℝ)) ^ α * |Y N| ≤ (1 / (N : ℝ)) ^ α * (‖t‖ * (K * (N : ℝ) ^ α)) :=
            mul_le_mul_of_nonneg_left hYb (by positivity)
        _ = ‖t‖ * K := by
            rw [div_pow, one_pow]
            field_simp
    have hGb0 : 0 ≤ Gb := le_trans (abs_nonneg _) hgN
    calc (1 / (N : ℝ)) ^ S * |Y N| * |g.eval (1 / (N : ℝ))|
        = (1 / (N : ℝ)) ^ (S - α) * ((1 / (N : ℝ)) ^ α * |Y N|) * |g.eval (1 / (N : ℝ))| := by
          rw [hsplit]; ring
      _ ≤ (1 / (N : ℝ)) ^ (S - α) * (‖t‖ * K) * Gb := by gcongr
      _ = _ := by ring
  obtain ⟨F₂, hF₂⟩ := X_pow_dvd_of_bound (S - α) F₁ _ _ hbound
  refine ⟨F₂, ?_, ?_⟩
  · by_cases h0 : F₂ = 0
    · rw [h0]; simp
    · have := hF₁deg
      rw [hF₂, natDegree_X_pow_mul _ h0] at this
      omega
  · intro N hN hLN
    have hN1 : 1 ≤ N := hL.trans hLN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [uniformExp_div_const]
    have h := hY N hN hLN
    rw [hF₂, eval_mul, eval_pow, eval_X] at h
    have hsplit : (1 / (N : ℝ)) ^ S = (1 / (N : ℝ)) ^ (S - α) * (1 / (N : ℝ)) ^ α := by
      rw [← pow_add]; congr 1; omega
    rw [hsplit, mul_assoc, mul_div_assoc] at h
    have h' := mul_left_cancel₀ (pow_ne_zero _ (by positivity : (1 / (N : ℝ)) ≠ 0)) h
    rw [← h', div_pow, one_pow]
    field_simp
    rfl

/-! ## The target -/
open Op in
theorem stable_rational (π : StableRep) :
    ∃ R : ℕ, 1 ≤ R ∧ π.N₀ ≤ R ∧ ∀ {D d q₀ : ℕ} (P : NCPoly D d), P.IsSelfAdjoint →
      P.degree ≤ q₀ → 1 ≤ q₀ → ∀ q : ℕ, 1 ≤ q → ∀ h : ℝ[X], h.natDegree ≤ q →
        ∃ (L : ℕ) (f : ℝ[X]), L ≤ q * (R * q₀) ∧
          (f.natDegree : ℝ) ≤ ((q * (R * q₀) : ℕ) : ℝ) * (1 + Real.log d) ∧
          ∀ N : ℕ, π.N₀ ≤ N → q * (R * q₀) ≤ N →
            stE π P N (fun x => h.eval x) =
              f.eval (1 / (N : ℝ)) / (gPoly d L).eval (1 / (N : ℝ)) := by
  classical
  obtain ⟨β, hβ⟩ := perWord π
  refine ⟨π.N₀ + β + π.alpha + 1, by omega, by omega, ?_⟩
  intro D d q₀ P hP hq₀ hq₀1 q hq h hh
  set R := π.N₀ + β + π.alpha + 1 with hR
  set α := π.alpha with hα
  set Q := q * (R * q₀) with hQ
  obtain ⟨B, hB, hBe⟩ := stE_eq π P hP hq₀ h
  have hqq : 1 ≤ q * q₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hQ' : Q = R * (q * q₀) := by rw [hQ]; ring
  have hQge : (β + α + 1) * (q * q₀) ≤ Q := by
    rw [hQ']; exact Nat.mul_le_mul_right _ (by omega)
  have hQge' : β * (q * q₀) + α + 1 ≤ Q := by
    have : (β + α + 1) * (q * q₀) = β * (q * q₀) + (α + 1) * (q * q₀) := by ring
    have h2 : α + 1 ≤ (α + 1) * (q * q₀) := Nat.le_mul_of_pos_right _ hqq
    omega
  set L := Q - α with hL
  have hL1 : 1 ≤ L := by omega
  have hBdeg : B.degree ≤ q * q₀ := hB.trans (Nat.mul_le_mul_right _ hh)
  have hwlen : ∀ w ∈ B.support, β * (w.toList.map some).length ≤ L := by
    intro w hw
    have h1 : w.toList.length ≤ B.degree := Finset.le_sup (f := FreeMonoid.length) hw
    rw [List.length_map]
    have h2 := Nat.mul_le_mul_left β (h1.trans hBdeg)
    omega
  have hF : ∀ w ∈ B.support, ∃ F : ℝ[X],
      F.natDegree ≤ α + ((gPoly d L).natDegree + min d L) ∧
      ∀ N : ℕ, π.N₀ ≤ N → L ≤ N →
        uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
          ((B w).trace * chi π N (wordPerm σ (w.toList.map some))).re / (N : ℝ) ^ α) =
          F.eval (1 / (N : ℝ)) / (gPoly d L).eval (1 / (N : ℝ)) := fun w hw =>
    hβ (w.toList.map some) (B w).trace L hL1 (hwlen w hw)
  choose! F hFdeg hFeq using hF
  refine ⟨L, ∑ w ∈ B.support, F w, by omega, ?_, ?_⟩
  · have h1 : (∑ w ∈ B.support, F w).natDegree ≤ α + ((gPoly d L).natDegree + min d L) :=
      natDegree_sum_le_of_forall_le _ _ fun w hw => hFdeg w hw
    have h2 := natDegree_gPoly_add_min_le d L hL1
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    have hQL : (Q : ℝ) = (L : ℝ) + α := by
      rw [hL]; push_cast [show α ≤ Q by omega]; ring
    have h1' : ((∑ w ∈ B.support, F w).natDegree : ℝ) ≤
        α + (((gPoly d L).natDegree + min d L : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hQL]
    have : (α : ℝ) ≤ α * (1 + Real.log d) := by nlinarith [(Nat.cast_nonneg α : (0 : ℝ) ≤ α)]
    nlinarith
  · intro N hN hQN
    have hLN : L ≤ N := by omega
    rw [hBe N, eval_finsetSum, sum_div]
    refine sum_congr rfl fun w hw => ?_
    rw [← hFeq w hw N hN hLN]
    congr 1
    funext σ
    rw [wordPerm_lift]

end StrongConv.Q202L1.PartR
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L1
open StrongConv
/-! ## Part R: rationality for stable representations (Lemma 10.1) -/
alias stable_rational := StrongConv.Q202L1.PartR.stable_rational

end StrongConv.Q202L1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartB
open StrongConv StrongConv.Q202L1 Matrix
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-!
# q202 Part B: `stable_bound`, `stable_linear`, `stable_const`, `stable_degenerate`,
# `fullNorm_nonneg'`

The eigenvalues of `P(Πᴺ)` lie in `[-‖P‖, ‖P‖]`, `‖P‖ = P.fullNorm`; `Tr` is at most `D · dim N` times the
operator norm; `dim N = φ(N, …, N)` is a polynomial of degree `α` for `N ≥ N₀`. In the degenerate
case `P(Πᴺ) = A ⊗ 1` for a fixed matrix `A`, and `h(A ⊗ 1) = p_h(A) ⊗ 1` for the Lagrange interpolant
`p_h` of `h` on the eigenvalues of `A`.
-/
omit [CompleteSpace H] in
lemma tensorOp_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H)
    (v : PiLp 2 (fun _ : Fin n => H)) (a : Fin m) :
    tensorOp A T v a = ∑ b, A a b • T (v b) := by
  simp [tensorOp, Finset.sum_apply, Pi.single_apply, smul_ite, Finset.sum_ite_eq]

lemma tensorOp_ext {m n : ℕ} {S S' : PiLp 2 (fun _ : Fin n => H) →L[ℂ] PiLp 2 (fun _ : Fin m => H)}
    (h : ∀ v a, S v a = S' v a) : S = S' :=
  ContinuousLinearMap.ext fun v => PiLp.ext fun a => h v a

lemma tensorOp_add_left {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (A + B) T = tensorOp A T + tensorOp B T := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, add_smul, Finset.sum_add_distrib]

lemma tensorOp_zero_left {m n : ℕ} (T : H →L[ℂ] H) :
    tensorOp (0 : Matrix (Fin m) (Fin n) ℂ) T = 0 := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply]

lemma tensorOp_smul_left {m n : ℕ} (c : ℂ) (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    tensorOp (c • A) T = c • tensorOp A T := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, Finset.smul_sum, smul_smul]

lemma tensorOp_mul {n : ℕ} (A A' : Matrix (Fin n) (Fin n) ℂ)
    (X X' : H →L[ℂ] H) :
    tensorOp A X * tensorOp A' X' = tensorOp (A * A') (X * X') := by
  apply tensorOp_ext; intro v a
  simp only [ContinuousLinearMap.mul_apply, tensorOp_apply, map_sum, map_smul, Matrix.mul_apply,
    Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

lemma tensorOp_one {n : ℕ} : tensorOp (1 : Matrix (Fin n) (Fin n) ℂ) (1 : H →L[ℂ] H) = 1 := by
  apply tensorOp_ext; intro v a
  simp [tensorOp_apply, Matrix.one_apply]

lemma tensorOp_star {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (X : H →L[ℂ] H) :
    star (tensorOp A X) = tensorOp Aᴴ (star X) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v w
  simp only [PiLp.inner_apply, tensorOp_apply, ContinuousLinearMap.star_eq_adjoint]
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right, Matrix.conjTranspose_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    Matrix.star_apply, RCLike.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]

lemma wordOp_one {d : ℕ} (u : Fin d → H →L[ℂ] H) : wordOp u 1 = 1 := by
  simp [wordOp]

lemma letterOp_swap {d : ℕ} (u : Fin d → H →L[ℂ] H) (a : Fin d ⊕ Fin d) :
    letterOp u a.swap = star (letterOp u a) := by
  cases a <;> simp [letterOp]

lemma star_wordOp {d : ℕ} (u : Fin d → H →L[ℂ] H) (w : FreeMonoid (Fin d ⊕ Fin d)) :
    star (wordOp u w) = wordOp u (NCPoly.wordStar w) := by
  unfold wordOp NCPoly.wordStar
  generalize w.toList = l
  simp only [FreeMonoid.toList_ofList]
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, List.reverse_cons, List.map_append, List.prod_append,
      List.map_nil, List.prod_nil, mul_one, star_mul, ← ih, List.map_singleton, List.prod_singleton,
      letterOp_swap]

lemma wordStar_wordStar {d : ℕ} (w : FreeMonoid (Fin d ⊕ Fin d)) :
    NCPoly.wordStar (NCPoly.wordStar w) = w := by
  simp [NCPoly.wordStar, List.map_reverse, Function.comp_def]

lemma star_eval {D d : ℕ} (P : NCPoly D d) (u : Fin d → H →L[ℂ] H) :
    star (P.eval u) = ∑ w ∈ P.support, tensorOp (P w)ᴴ (wordOp u (NCPoly.wordStar w)) := by
  unfold NCPoly.eval
  erw [star_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [tensorOp_star, star_wordOp]

lemma isSelfAdjoint_eval {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (P.eval u) := by
  unfold IsSelfAdjoint
  rw [star_eval]
  have hmem : ∀ w, w ∈ P.support → NCPoly.wordStar w ∈ P.support := by
    intro w hw
    rw [Finsupp.mem_support_iff] at hw ⊢
    rw [hP]
    simpa using hw
  calc _ = ∑ w ∈ P.support, tensorOp (P (NCPoly.wordStar w)) (wordOp u (NCPoly.wordStar w)) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hP]
    _ = P.eval u := by
        unfold NCPoly.eval
        exact Finset.sum_nbij' NCPoly.wordStar NCPoly.wordStar hmem hmem
          (fun _ _ => wordStar_wordStar _) (fun _ _ => wordStar_wordStar _) (fun _ _ => rfl)

omit [CompleteSpace H] in
lemma norm_pi_le_sum {n : ℕ} (y : PiLp 2 (fun _ : Fin n => H)) : ‖y‖ ≤ ∑ a, ‖y a‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)

omit [CompleteSpace H] in
lemma tensorOp_norm_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (T : H →L[ℂ] H) :
    ‖tensorOp A T‖ ≤ (∑ a, ∑ b, ‖A a b‖) * ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  refine (norm_pi_le_sum _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [tensorOp_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [norm_smul]
  have h1 : ‖T (x b)‖ ≤ ‖T‖ * ‖x‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x b) (norm_nonneg _))
  calc ‖A a b‖ * ‖T (x b)‖ ≤ ‖A a b‖ * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖A a b‖ * ‖T‖ * ‖x‖ := by ring

end StrongConv.Q202L1.PartB
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartB
open StrongConv StrongConv.Q202L1 Matrix
/-! ### Norm bounds -/
lemma norm_le_one_of_unitary {A : Type*} [CStarAlgebra A] (U : A) (hU : U ∈ unitary A) :
    ‖U‖ ≤ 1 := by
  rcases subsingleton_or_nontrivial A with h | h
  · rw [Subsingleton.elim U 0]; simp
  · exact (CStarRing.norm_of_mem_unitary hU).le

lemma wordOp_norm_le_one {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (hu : ∀ i, ‖u i‖ ≤ 1)
    (w : FreeMonoid (Fin d ⊕ Fin d)) : ‖wordOp u w‖ ≤ 1 := by
  unfold wordOp
  generalize w.toList = l
  induction l with
  | nil => exact ContinuousLinearMap.norm_id_le
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (norm_mul_le _ _).trans ?_
    have : ‖letterOp u a‖ ≤ 1 := by
      rcases a with i | i
      · exact hu i
      · simpa [letterOp] using hu i
    nlinarith [norm_nonneg (letterOp u a), norm_nonneg ((l.map (letterOp u)).prod)]

lemma norm_eval_le {D d : ℕ} (P : NCPoly D d) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (u : Fin d → H →L[ℂ] H) (hu : ∀ i, ‖u i‖ ≤ 1) :
    ‖P.eval u‖ ≤ ∑ w ∈ P.support, ∑ a, ∑ b, ‖P w a b‖ := by
  unfold NCPoly.eval
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  refine (tensorOp_norm_le _ _).trans ?_
  have := wordOp_norm_le_one u hu w
  have h0 : 0 ≤ ∑ a, ∑ b, ‖P w a b‖ := by positivity
  nlinarith

lemma norm_toEuclideanCLM_le {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (U : Matrix (Fin n) (Fin n) ℂ)‖ ≤ 1 := by
  refine norm_le_one_of_unitary _ ?_
  have h := U.2
  rw [Unitary.mem_iff] at h ⊢
  constructor
  · rw [← map_star, ← map_mul, h.1, map_one]
  · rw [← map_star, ← map_mul, h.2, map_one]

lemma bddAbove_fullNorm {D d : ℕ} (P : NCPoly D d) :
    BddAbove {x | ∃ (n : ℕ) (U : Fin d → Matrix.unitaryGroup (Fin n) ℂ),
      x = ‖P.eval (fun i => Matrix.toEuclideanCLM (𝕜 := ℂ) (U i : Matrix (Fin n) (Fin n) ℂ))‖} := by
  refine ⟨∑ w ∈ P.support, ∑ a, ∑ b, ‖P w a b‖, ?_⟩
  rintro x ⟨n, U, rfl⟩
  exact norm_eval_le P _ fun i => norm_toEuclideanCLM_le (U i)

lemma norm_eval_model_le (π : StableRep) {D d N : ℕ} (P : NCPoly D d)
    (σ : Fin d → Equiv.Perm (Fin N)) : ‖P.eval (π.model σ)‖ ≤ P.fullNorm :=
  le_csSup (bddAbove_fullNorm P) ⟨π.dim N, fun i => π.π N (σ i), rfl⟩

theorem fullNorm_nonneg' {D d : ℕ} (P : NCPoly D d) : 0 ≤ P.fullNorm := by
  unfold NCPoly.fullNorm
  refine Real.sSup_nonneg fun x hx => ?_
  obtain ⟨n, U, rfl⟩ := hx
  exact norm_nonneg _

/-! ### Traces -/
lemma norm_trace_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (Y : V →L[ℂ] V) :
    ‖LinearMap.trace ℂ V (Y : V →ₗ[ℂ] V)‖ ≤ (Module.finrank ℂ V : ℝ) * ‖Y‖ := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ V)]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ i, ‖inner ℂ ((stdOrthonormalBasis ℂ V) i) (Y ((stdOrthonormalBasis ℂ V) i))‖ ≤ ‖Y‖ := by
    intro i
    refine (norm_inner_le_norm _ _).trans ?_
    have h1 := (stdOrthonormalBasis ℂ V).orthonormal.1 i
    have h2 := Y.le_opNorm ((stdOrthonormalBasis ℂ V) i)
    rw [h1] at h2
    simpa [h1] using h2
  refine (Finset.sum_le_sum fun i _ => this i).trans ?_
  simp

lemma finrank_pi (D n : ℕ) :
    Module.finrank ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin n))) = D * n := by
  rw [(WithLp.linearEquiv 2 ℂ (Fin D → EuclideanSpace ℂ (Fin n))).finrank_eq,
    Module.finrank_pi_fintype]
  simp

lemma trace_tensorOp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (T : H →L[ℂ] H) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => H))
        ((tensorOp A T : PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) :
          PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) =
      A.trace * LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) := by
  classical
  unfold tensorOp
  simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul, map_sum,
    map_smul]
  rw [Matrix.trace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  have key : ∀ b : Fin D,
      LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => H))
        ((((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => H)).symm.toContinuousLinearMap.comp
          ((ContinuousLinearMap.single ℂ (fun _ : Fin D => H) a).comp
            (T.comp (PiLp.proj 2 (fun _ : Fin D => H) b : PiLp 2 (fun _ : Fin D => H) →L[ℂ] H))))) :
              PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) =
        if a = b then LinearMap.trace ℂ H (T : H →ₗ[ℂ] H) else 0 := by
    intro b
    rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm',
      ← ContinuousLinearMap.toLinearMap_comp]
    have : (PiLp.proj 2 (fun _ : Fin D => H) b : PiLp 2 (fun _ : Fin D => H) →L[ℂ] H).comp
        ((((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin D => H)).symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.single ℂ (fun _ : Fin D => H) a)).comp T) =
          if a = b then T else 0 := by
      ext x
      by_cases h : a = b
      · subst h; simp
      · simp [h, Ne.symm h]
    rw [this]
    split_ifs <;> simp
  simp only [key, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Matrix.diag_apply]

/-! ### `dim N` -/
/-- The dimension polynomial `N ↦ φ(N, …, N)`. -/
def dimPoly (π : StableRep) : ℂ[X] := MvPolynomial.aeval (fun _ : Fin π.r => (X : ℂ[X])) π.φ

lemma dim_eq (π : StableRep) {N : ℕ} (hN : π.N₀ ≤ N) :
    (π.dim N : ℂ) = (dimPoly π).eval (N : ℂ) := by
  have h1 := π.trace_eq N hN 1
  have hxi : ∀ j, xi j (1 : Equiv.Perm (Fin N)) = N := by intro j; simp [xi]
  simp only [hxi, map_one] at h1
  rw [dimPoly, ← Polynomial.coe_aeval_eq_eval, MvPolynomial.comp_aeval_apply]
  simp only [Polynomial.aeval_X]
  have he : (MvPolynomial.aeval fun _ : Fin π.r => (N : ℂ)) π.φ =
      MvPolynomial.eval (fun _ : Fin π.r => (N : ℂ)) π.φ := rfl
  rw [he, ← h1]
  simp

lemma dim_bound (π : StableRep) : ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
    (π.dim N : ℝ) ≤ K * (N : ℝ) ^ π.alpha := by
  set p : ℂ[X] := dimPoly π with hp
  refine ⟨∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖, by positivity, fun N hN hN1 => ?_⟩
  have hdim := dim_eq π hN
  have hα : π.alpha = p.natDegree := rfl
  have key : ‖(π.dim N : ℂ)‖ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) *
      (N : ℝ) ^ π.alpha := by
    rw [hdim, eval_eq_sum_range]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by exact_mod_cast hN1) ?_) (norm_nonneg _)
    rw [Finset.mem_range] at hi
    show i ≤ (dimPoly π).natDegree
    omega
  simpa using key

lemma dim_expansion (π : StableRep) : ∃ e : ℕ → ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
    (π.dim N : ℝ) / (N : ℝ) ^ π.alpha = ∑ i ∈ Finset.range (π.alpha + 1), e i / (N : ℝ) ^ i := by
  set p : ℂ[X] := dimPoly π with hp
  have hα : π.alpha = p.natDegree := rfl
  refine ⟨fun i => (p.coeff (π.alpha - i)).re, fun N hN hN1 => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hdim : (π.dim N : ℝ) = ∑ k ∈ Finset.range (π.alpha + 1), (p.coeff k).re * (N : ℝ) ^ k := by
    have h := congrArg Complex.re (dim_eq π hN)
    rw [eval_eq_sum_range, ← hα, Complex.re_sum] at h
    rw [show ((π.dim N : ℂ)).re = (π.dim N : ℝ) by simp] at h
    rw [h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_mul_ofReal]
  rw [hdim, Finset.sum_div]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hk' : π.alpha + 1 - 1 - k = π.alpha - k := by omega
  rw [hk']
  show (p.coeff (π.alpha - k)).re * (N : ℝ) ^ (π.alpha - k) / (N : ℝ) ^ π.alpha =
    (p.coeff (π.alpha - k)).re / (N : ℝ) ^ k
  have : (N : ℝ) ^ π.alpha = (N : ℝ) ^ (π.alpha - k) * (N : ℝ) ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  have : (N : ℝ) ^ k ≠ 0 := by positivity
  have : (N : ℝ) ^ (π.alpha - k) ≠ 0 := by positivity
  field_simp

/-! ### Functional calculus -/
lemma le_supOn {f : ℝ → ℝ} (hf : Continuous f) {a b x : ℝ} (hx : x ∈ Set.Icc a b) :
    |f x| ≤ supOn f a b := by
  unfold supOn
  refine le_csSup ?_ ⟨x, hx, rfl⟩
  exact (isCompact_Icc.image (by fun_prop : Continuous fun x => |f x|)).bddAbove

lemma norm_fnCalc_le {A : Type*} [CStarAlgebra A] (T : A) {K : ℝ}
    (hK : ‖T‖ ≤ K) {f : ℝ → ℝ} (hf : Continuous f) :
    ‖fnCalc f T‖ ≤ supOn f (-K) K := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hS : 0 ≤ supOn f (-K) K :=
    (abs_nonneg _).trans (le_supOn hf (x := 0) ⟨by linarith, hK0⟩)
  unfold fnCalc
  rcases subsingleton_or_nontrivial A with hA | hA
  · rw [Subsingleton.elim (cfc _ T) 0]; simpa using hS
  refine norm_cfc_le hS ?_
  intro z hz
  have hzn : ‖z‖ ≤ K := (spectrum.norm_le_norm_of_mem hz).trans hK
  have : |z.re| ≤ K := by
    have := Complex.abs_re_le_norm z
    linarith
  have hmem : z.re ∈ Set.Icc (-K) K := abs_le.mp this |> fun h => ⟨h.1, h.2⟩
  simpa [Complex.norm_real] using le_supOn hf hmem

lemma abs_uniformExp_le {X : Type*} [Fintype X] [Nonempty X] (f : X → ℝ) (B : ℝ)
    (h : ∀ x, |f x| ≤ B) : |uniformExp f| ≤ B := by
  unfold uniformExp
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
  calc |∑ x, f x| ≤ ∑ x, |f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x : X, B := Finset.sum_le_sum fun x _ => h x
    _ = B * Fintype.card X := by simp [mul_comm]

lemma uniformExp_const {X : Type*} [Fintype X] [Nonempty X] (c : ℝ) :
    uniformExp (fun _ : X => c) = c := by
  unfold uniformExp
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem stable_bound (π : StableRep) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ {D d : ℕ} (P : NCPoly D d), P.IsSelfAdjoint →
      ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N → ∀ f : ℝ → ℝ, Continuous f →
        |stE π P N f| ≤ κ * D * supOn f (-P.fullNorm) P.fullNorm := by
  obtain ⟨κ, hκ0, hκ⟩ := dim_bound π
  refine ⟨κ, hκ0, fun {D d} P _hP N hN hN1 f hf => ?_⟩
  have hK0 := fullNorm_nonneg' P
  have hS : 0 ≤ supOn f (-P.fullNorm) P.fullNorm :=
    (abs_nonneg _).trans (le_supOn hf (x := 0) ⟨by linarith, hK0⟩)
  have hNpos : (0 : ℝ) < (N : ℝ) ^ π.alpha := by
    have : (0 : ℝ) < N := by exact_mod_cast hN1
    positivity
  unfold stE
  refine abs_uniformExp_le _ _ fun σ => ?_
  rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
  have h1 := norm_trace_le (fnCalc f (P.eval (π.model σ)))
  rw [finrank_pi] at h1
  have h2 := norm_fnCalc_le (P.eval (π.model σ)) (norm_eval_model_le π P σ) hf
  have h3 := hκ N hN hN1
  refine (Complex.abs_re_le_norm _).trans (h1.trans ?_)
  push_cast
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hdim : (0 : ℝ) ≤ π.dim N := Nat.cast_nonneg _
  calc (D : ℝ) * π.dim N * ‖fnCalc f (P.eval (π.model σ))‖
      ≤ D * π.dim N * supOn f (-P.fullNorm) P.fullNorm :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ D * (κ * (N : ℝ) ^ π.alpha) * supOn f (-P.fullNorm) P.fullNorm := by
        gcongr
    _ = κ * D * supOn f (-P.fullNorm) P.fullNorm * (N : ℝ) ^ π.alpha := by ring

end StrongConv.Q202L1.PartB
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L1
open StrongConv
/-! ## Part B: the bound, linearity, the constant function, the degenerate case -/
alias stable_bound := StrongConv.Q202L1.PartB.stable_bound

end StrongConv.Q202L1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartB
open StrongConv StrongConv.Q202L1 Matrix
lemma fnCalc_add_smul {A : Type*} [CStarAlgebra A] (T : A) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (c : ℝ) :
    fnCalc (fun x => f x + c * g x) T = fnCalc f T + (c : ℂ) • fnCalc g T := by
  unfold fnCalc
  have hf' : Continuous fun z : ℂ => ((f z.re : ℝ) : ℂ) := by fun_prop
  have hg' : Continuous fun z : ℂ => ((g z.re : ℝ) : ℂ) := by fun_prop
  have : (fun z : ℂ => (((f z.re + c * g z.re : ℝ)) : ℂ)) =
      fun z : ℂ => ((f z.re : ℝ) : ℂ) + (c : ℂ) * ((g z.re : ℝ) : ℂ) := by
    funext z; push_cast; ring
  rw [this, cfc_add _ _ _ hf'.continuousOn (by fun_prop),
    cfc_const_mul _ _ _ hg'.continuousOn]

theorem stable_linear (π : StableRep) {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (N : ℕ) (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (c : ℝ) :
    stE π P N (fun x => f x + c * g x) = stE π P N f + c * stE π P N g := by
  unfold stE
  simp only [fnCalc_add_smul _ hf hg c, ContinuousLinearMap.toLinearMap_add,
    ContinuousLinearMap.toLinearMap_smul, map_add, map_smul, Complex.add_re, smul_eq_mul,
    Complex.re_ofReal_mul]
  unfold uniformExp
  rw [mul_div_assoc', Finset.mul_sum, ← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

end StrongConv.Q202L1.PartB
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L1
open StrongConv
alias stable_linear := StrongConv.Q202L1.PartB.stable_linear

end StrongConv.Q202L1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartB
open StrongConv StrongConv.Q202L1 Matrix
theorem stable_const (π : StableRep) {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint) :
    ∃ e : ℕ → ℝ, ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N →
      stE π P N (fun _ => 1) = ∑ i ∈ Finset.range (π.alpha + 1), e i / (N : ℝ) ^ i := by
  obtain ⟨e, he⟩ := dim_expansion π
  refine ⟨fun i => D * e i, fun N hN hN1 => ?_⟩
  have hone : ∀ σ : Fin d → Equiv.Perm (Fin N), fnCalc (fun _ => (1 : ℝ)) (P.eval (π.model σ)) = 1 := by
    intro σ
    have := (isSelfAdjoint_eval P hP (π.model σ)).isStarNormal
    unfold fnCalc
    simp only [Complex.ofReal_one]
    exact cfc_const_one ℂ _
  unfold stE
  simp only [hone, ContinuousLinearMap.coe_one, LinearMap.trace_one, finrank_pi]
  rw [uniformExp_const]
  rw [show (((D * π.dim N : ℕ) : ℂ)).re = (D : ℝ) * π.dim N by
    rw [← Complex.ofReal_natCast, Complex.ofReal_re]; push_cast; ring,
    mul_div_assoc, he N hN hN1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end StrongConv.Q202L1.PartB
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L1
open StrongConv
alias stable_const := StrongConv.Q202L1.PartB.stable_const

end StrongConv.Q202L1
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartB
open StrongConv StrongConv.Q202L1 Matrix
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-! ### The degenerate case: `P(Πᴺ) = A ⊗ 1` -/
/-- `M ↦ M ⊗ 1` as an algebra hom. -/
def tensorAlg (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (D : ℕ) : Matrix (Fin D) (Fin D) ℂ →ₐ[ℂ]
    (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) where
  toFun M := tensorOp M (1 : H →L[ℂ] H)
  map_one' := tensorOp_one
  map_mul' M M' := by rw [tensorOp_mul, mul_one]
  map_zero' := tensorOp_zero_left _
  map_add' M M' := tensorOp_add_left _ _ _
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [tensorOp_smul_left, tensorOp_one]

lemma tensorAlg_apply {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) :
    tensorAlg H D M = tensorOp M (1 : H →L[ℂ] H) := rfl

/-- The real parts of the eigenvalues of `A`. -/
def eigS {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) : Finset ℝ :=
  A.charpoly.roots.toFinset.image Complex.re

lemma mem_spec {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (hT : IsSelfAdjoint (tensorOp A (1 : H →L[ℂ] H))) {z : ℂ}
    (hz : z ∈ spectrum ℂ (tensorOp A (1 : H →L[ℂ] H))) : z = (z.re : ℂ) ∧ z.re ∈ eigS A := by
  refine ⟨hT.mem_spectrum_eq_re hz, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (tensorOp A (1 : H →L[ℂ] H)) A.charpoly ⟨z, hz, rfl⟩
  have h2 : aeval (tensorOp A (1 : H →L[ℂ] H)) A.charpoly = 0 := by
    rw [← tensorAlg_apply, Polynomial.aeval_algHom_apply, Matrix.aeval_self_charpoly, map_zero]
  rw [h2] at h1
  rcases subsingleton_or_nontrivial (PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H))
    with hs | hs
  · exfalso
    rw [spectrum.mem_iff] at hz
    exact hz (isUnit_of_subsingleton _)
  rw [spectrum.zero_eq, Set.mem_singleton_iff] at h1
  have hroot : z ∈ A.charpoly.roots := (mem_roots A.charpoly_monic.ne_zero).2 h1
  exact Finset.mem_image.2 ⟨z, Multiset.mem_toFinset.2 hroot, rfl⟩

/-- The weight of the node `x`: `Tr ℓ_x(A)` for the Lagrange basis polynomial `ℓ_x`. -/
def wt {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (x : ℝ) : ℂ :=
  (aeval A ((Lagrange.basis (eigS A) id x).map (algebraMap ℝ ℂ))).trace

lemma trace_fnCalc_tensor [FiniteDimensional ℂ H] {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (hT : IsSelfAdjoint (tensorOp A (1 : H →L[ℂ] H))) (h : ℝ → ℝ) :
    LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => H))
        ((fnCalc h (tensorOp A (1 : H →L[ℂ] H)) :
          PiLp 2 (fun _ : Fin D => H) →L[ℂ] PiLp 2 (fun _ : Fin D => H)) :
          PiLp 2 (fun _ : Fin D => H) →ₗ[ℂ] PiLp 2 (fun _ : Fin D => H)) =
      (∑ x ∈ eigS A, (h x : ℂ) * wt A x) * Module.finrank ℂ H := by
  set q : ℝ[X] := Lagrange.interpolate (eigS A) id h with hq
  have := hT.isStarNormal
  have h1 : fnCalc h (tensorOp A (1 : H →L[ℂ] H)) =
      aeval (tensorOp A (1 : H →L[ℂ] H)) (q.map (algebraMap ℝ ℂ)) := by
    unfold fnCalc
    rw [← cfc_polynomial (q.map (algebraMap ℝ ℂ)) (tensorOp A (1 : H →L[ℂ] H))]
    apply cfc_congr
    intro z hz
    obtain ⟨hz1, hz2⟩ := mem_spec A hT hz
    have hev : eval z.re q = h z.re := by
      have := Lagrange.eval_interpolate_at_node (s := eigS A) (v := id) h (Set.injOn_id _) hz2
      rw [hq]; simpa using this
    simp only
    conv_rhs => rw [hz1]
    rw [Polynomial.eval_map, ← Complex.coe_algebraMap, Polynomial.eval₂_at_apply, hev]
  rw [h1, ← tensorAlg_apply, Polynomial.aeval_algHom_apply, tensorAlg_apply, trace_tensorOp]
  rw [show ((1 : H →L[ℂ] H) : H →ₗ[ℂ] H) = 1 from rfl, LinearMap.trace_one]
  congr 1
  rw [hq, Lagrange.interpolate_apply, Polynomial.map_sum, map_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one,
    smul_mul_assoc, one_mul, Matrix.trace_smul, smul_eq_mul, wt]
  rfl

end StrongConv.Q202L1.PartB
end
end

section
open Polynomial Filter Topology
open Polynomial Filter Topology
open scoped Pointwise
open Polynomial Filter Topology
open Polynomial Filter Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StrongConv.Q202L1.PartB
open StrongConv StrongConv.Q202L1 Matrix
lemma eval_eq_tensor (π : StableRep) {D d : ℕ} (P : NCPoly D d)
    (hdeg : P.degree = 0 ∨ P.fullNorm = 0) :
    ∃ A : Matrix (Fin D) (Fin D) ℂ, ∀ (N : ℕ) (σ : Fin d → Equiv.Perm (Fin N)),
      P.eval (π.model σ) = tensorOp A (1 : EuclideanSpace ℂ (Fin (π.dim N)) →L[ℂ] _) := by
  rcases hdeg with h0 | h0
  · refine ⟨P 1, fun N σ => ?_⟩
    have hsub : P.support ⊆ {1} := by
      intro w hw
      have : w.length ≤ P.degree := Finset.le_sup (f := FreeMonoid.length) hw
      rw [h0, Nat.le_zero, FreeMonoid.length_eq_zero] at this
      simp [this]
    unfold NCPoly.eval
    rw [Finset.sum_subset hsub (fun w _ hw => by
      rw [Finsupp.notMem_support_iff.1 hw, tensorOp_zero_left]), Finset.sum_singleton, wordOp_one]
  · refine ⟨0, fun N σ => ?_⟩
    have := norm_eval_model_le π P σ
    rw [h0] at this
    rw [norm_le_zero_iff.1 this, tensorOp_zero_left]

/-- The functional `h ↦ ∑_x h(x) Re wt(x)`. -/
def evalL {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) : smoothFun →ₗ[ℝ] ℝ where
  toFun f := ∑ x ∈ eigS A, (f : ℝ → ℝ) x * (wt A x).re
  map_add' f g := by
    simp only [Submodule.coe_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
      mul_assoc]

lemma isCS_smul_evalL {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) (a : ℝ) :
    IsCSDistribution (a • evalL A) := by
  set W := ∑ x ∈ eigS A, |(wt A x).re|
  set K := (∑ x ∈ eigS A, |x|) + 1
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hK : 0 < K := by
    have : 0 ≤ ∑ x ∈ eigS A, |x| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  refine ⟨|a| * W + 1, K, 0, by positivity, hK, fun f => ?_⟩
  have hfc : Continuous (f : ℝ → ℝ) := (show ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℝ) from f.2).continuous
  have hc : cNorm 0 (f : ℝ → ℝ) (-K) K = supOn f (-K) K := by
    simp [cNorm, iteratedDeriv_zero]
  rw [hc]
  set M := supOn f (-K) K
  have hM : 0 ≤ M := (abs_nonneg _).trans (le_supOn hfc (x := 0) ⟨by linarith, hK.le⟩)
  have hx : ∀ x ∈ eigS A, |(f : ℝ → ℝ) x| ≤ M := by
    intro x hx
    refine le_supOn hfc ?_
    have : |x| ≤ ∑ y ∈ eigS A, |y| :=
      Finset.single_le_sum (f := fun y => |y|) (fun _ _ => abs_nonneg _) hx
    have : |x| ≤ K := by linarith
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  rw [LinearMap.smul_apply, smul_eq_mul, abs_mul]
  have hL : |evalL A f| ≤ W * M := by
    show |∑ x ∈ eigS A, (f : ℝ → ℝ) x * (wt A x).re| ≤ W * M
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun x hx' => ?_
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hx x hx') (abs_nonneg _)
  calc |a| * |evalL A f| ≤ |a| * (W * M) := mul_le_mul_of_nonneg_left hL (abs_nonneg _)
    _ ≤ (|a| * W + 1) * M := by nlinarith [abs_nonneg a]

theorem stable_degenerate (π : StableRep) {D d : ℕ} (P : NCPoly D d) (hP : P.IsSelfAdjoint)
    (hdeg : P.degree = 0 ∨ P.fullNorm = 0) :
    ∃ ν : ℕ → smoothFun →ₗ[ℝ] ℝ, (∀ i, IsCSDistribution (ν i)) ∧
      ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N → ∀ h : smoothFun,
        stE π P N (h : ℝ → ℝ) = ∑ i ∈ Finset.range (π.alpha + 1), ν i h / (N : ℝ) ^ i := by
  obtain ⟨A, hA⟩ := eval_eq_tensor π P hdeg
  obtain ⟨e, he⟩ := dim_expansion π
  refine ⟨fun i => e i • evalL A, fun i => isCS_smul_evalL A (e i), fun N hN hN1 h => ?_⟩
  have hT : IsSelfAdjoint (tensorOp A (1 : EuclideanSpace ℂ (Fin (π.dim N)) →L[ℂ] _)) := by
    rw [← hA N (fun _ => 1)]
    exact isSelfAdjoint_eval P hP _
  unfold stE
  simp only [hA, trace_fnCalc_tensor A hT, finrank_euclideanSpace_fin]
  rw [uniformExp_const]
  have hre : ((∑ x ∈ eigS A, ((h : ℝ → ℝ) x : ℂ) * wt A x) * (π.dim N : ℂ)).re =
      evalL A h * π.dim N := by
    rw [← Complex.ofReal_natCast, Complex.re_mul_ofReal, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.re_ofReal_mul]
  rw [hre, mul_div_assoc, he N hN hN1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.smul_apply, smul_eq_mul]
  ring

end StrongConv.Q202L1.PartB
end
end

section
open Polynomial Filter Topology
noncomputable section
namespace StrongConv.Q202L1
open StrongConv
alias stable_degenerate := StrongConv.Q202L1.PartB.stable_degenerate

alias fullNorm_nonneg' := StrongConv.Q202L1.PartB.fullNorm_nonneg'

theorem lpNormCircle_nonneg' (β : ℝ) (F : ℝ → ℝ) : 0 ≤ lpNormCircle β F :=
  ENNReal.toReal_nonneg

theorem conjExp_pos' (β : ℝ) (hβ : 1 < β) : 0 < conjExp β := by
  unfold conjExp
  have : 1 / β < 1 := by rw [div_lt_one (by linarith)]; exact hβ
  exact inv_pos.mpr (by linarith)

/-! ## Assembly -/
theorem exists_csDistribution_abs_stableExpTr_sub_le_dev (π : StableRep) :
    ∃ C : ℝ, ∀ {D d q₀ : ℕ}, 2 ≤ d → ∀ P : NCPoly D d, P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∃ ν : ℕ → smoothFun →ₗ[ℝ] ℝ, (∀ i, IsCSDistribution (ν i)) ∧
        ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
          |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
                ((fnCalc (h : ℝ → ℝ) (P.eval (π.model σ)) :
                  PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
                  PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
                (N : ℝ) ^ π.alpha) -
            ∑ i ∈ Finset.range (π.alpha + 1), ν i h / (N : ℝ) ^ i| ≤
          C * D * (q₀ * (1 + Real.log d)) ^ (4 * (π.alpha + 1)) / (N : ℝ) ^ (π.alpha + 1) *
            conjExp β * lpNormCircle β (iteratedDeriv (4 * (π.alpha + 1) + 1)
              (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := abstract_master
  obtain ⟨R, hR1, hRN, hrat⟩ := stable_rational π
  obtain ⟨κ, hκ0, hκ⟩ := stable_bound π
  refine ⟨C₁ * κ * (4 * (R : ℝ)) ^ (4 * (π.alpha + 1)), ?_⟩
  intro D d q₀ _hd P hP hq₀
  have hK0 := fullNorm_nonneg' P
  by_cases hdeg : q₀ = 0 ∨ P.fullNorm = 0
  · obtain ⟨ν, hν, hex⟩ := stable_degenerate π P hP (by
      rcases hdeg with h | h
      · exact Or.inl (Nat.le_zero.mp (h ▸ hq₀))
      · exact Or.inr h)
    refine ⟨ν, hν, fun N hN hN1 β hβ h => ?_⟩
    have := hex N hN hN1 h
    unfold stE at this
    rw [this, sub_self, abs_zero]
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have := conjExp_pos' β hβ
    have := lpNormCircle_nonneg' β (iteratedDeriv (4 * (π.alpha + 1) + 1)
      (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ)))
    have : (0 : ℝ) ≤ q₀ * (1 + Real.log d) := by
      have := Real.log_natCast_nonneg d; positivity
    positivity
  · push Not at hdeg
    obtain ⟨hq0, hKne⟩ := hdeg
    have hq₀1 : 1 ≤ q₀ := Nat.one_le_iff_ne_zero.mpr hq0
    have hKpos : 0 < P.fullNorm := lt_of_le_of_ne hK0 (Ne.symm hKne)
    have hQ1 : 1 ≤ R * q₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hNQ : π.N₀ ≤ R * q₀ := hRN.trans (Nat.le_mul_of_pos_right R (by omega))
    obtain ⟨e, he⟩ := stable_const π P hP
    obtain ⟨ν, hν, hb⟩ := hC₁ d (R * q₀) π.N₀ (π.alpha + 1) P.fullNorm (κ * D) (stE π P)
      (by omega) hQ1 hNQ hKpos (by positivity)
      (fun N _ _ f g hf hg c => stable_linear π P hP N f g hf hg c)
      (fun N hN hN1 f hf => hκ P hP N hN hN1 f hf)
      ⟨e, he⟩
      (fun q hq h hh => hrat P hP hq₀ hq₀1 q hq h hh)
    refine ⟨ν, hν, fun N hN hN1 β hβ h => ?_⟩
    have := hb N hN hN1 β hβ h
    unfold stE at this
    refine this.trans (le_of_eq ?_)
    push_cast
    rw [show (4 * ((R : ℝ) * q₀) * (1 + Real.log d)) = (4 * R) * (q₀ * (1 + Real.log d)) by ring,
      mul_pow]
    ring

end StrongConv.Q202L1
end
end


section
open Polynomial Filter Topology
open StrongConv
theorem solution (π : StableRep) :
    ∃ C : ℝ, ∀ {D d q₀ : ℕ}, 2 ≤ d → ∀ P : NCPoly D d, P.IsSelfAdjoint → P.degree ≤ q₀ →
      ∃ ν : ℕ → smoothFun →ₗ[ℝ] ℝ, (∀ i, IsCSDistribution (ν i)) ∧
        ∀ N : ℕ, π.N₀ ≤ N → 1 ≤ N → ∀ β : ℝ, 1 < β → ∀ h : smoothFun,
          |uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
              (LinearMap.trace ℂ (PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))
                ((fnCalc (h : ℝ → ℝ) (P.eval (π.model σ)) :
                  PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →L[ℂ]
                    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N)))) :
                  PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))) →ₗ[ℂ]
                    PiLp 2 (fun _ : Fin D => EuclideanSpace ℂ (Fin (π.dim N))))).re /
                (N : ℝ) ^ π.alpha) -
            ∑ i ∈ Finset.range (π.alpha + 1), ν i h / (N : ℝ) ^ i| ≤
          C * D * (q₀ * (1 + Real.log d)) ^ (4 * (π.alpha + 1)) / (N : ℝ) ^ (π.alpha + 1) *
            conjExp β * lpNormCircle β (iteratedDeriv (4 * (π.alpha + 1) + 1)
              (fun θ => (h : ℝ → ℝ) (P.fullNorm * Real.cos θ))) :=
  StrongConv.Q202L1.exists_csDistribution_abs_stableExpTr_sub_le_dev π
end
