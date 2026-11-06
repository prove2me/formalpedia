-- Prove2me | solution 2 for StrongConv.supp_subset_Icc_rhoStair_of_extends_nuAdj
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:35:13.119704+00:00
-- url     : https://prove2.me/submissions/090a663e-2edb-4c05-bf7a-fcaa4a295e84
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_tendsto_uniformExp_trN_wordEval
import Theorems.Thm_StrongConv_supp_subset_Icc_limsup
import Theorems.Thm_StrongConv_supp_subset_Icc_of_extends_nuAdj_one
import Theorems.Thm_StrongConv_norm_adjFree
import Theorems.Thm_StrongConv_limsup_abs_nuAdj_X_pow_le_rhoStair

section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5


end StrongConv.S5
end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartRoot

open FreeGroup FreeGroup.reduceCyclically

end StrongConv.S5.PartRoot

end
section

open Polynomial Filter Topology

noncomputable section

namespace StrongConv.S5.PartPerm

open scoped InnerProductSpace

/-! ### The left-regular representation -/

lemma leftReg_apply {d : ℕ} (g : FreeGroup (Fin d)) (f : L2Free d) (h : FreeGroup (Fin d)) :
    leftReg g f h = f (g⁻¹ * h) := rfl

lemma leftReg_mul {d : ℕ} (g g' : FreeGroup (Fin d)) :
    leftReg (g * g') = leftReg g * leftReg g' := by
  ext f h
  simp only [leftReg_apply, mul_apply_eq_comp, mul_inv_rev, mul_assoc]

lemma leftReg_one {d : ℕ} : leftReg (1 : FreeGroup (Fin d)) = 1 := by
  ext f h
  simp [leftReg_apply]

lemma star_leftReg {d : ℕ} (g : FreeGroup (Fin d)) : star (leftReg g) = leftReg g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [leftReg_apply, inv_inv]
  rw [← (Equiv.mulLeft g⁻¹).tsum_eq]
  simp

lemma wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    wordEval (sLimit d) w = leftReg (wordFree w) := by
  induction w with
  | nil => simp [wordEval, wordFree, leftReg_one]
  | cons a w ih =>
    simp only [wordEval, wordFree, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, leftReg_mul]
    congr 1
    rcases a with _ | (i | i)
    · simp [leftReg_one]
    · simp [letterOp, sLimit]
    · simp [letterOp, sLimit, star_leftReg]

theorem tau_wordEval_sLimit {d : ℕ} (w : List (Letter d)) :
    tau (wordEval (sLimit d) w) = if wordFree w = 1 then 1 else 0 := by
  classical
  rw [wordEval_sLimit, tau, delta, lp.inner_single_left, leftReg_apply]
  simp only [mul_one, lp.single_apply]
  by_cases h : wordFree w = 1
  · simp [h]
  · rw [if_neg h, Pi.single_apply, if_neg (by simpa [inv_eq_one] using h)]
    simp

end StrongConv.S5.PartPerm


open Polynomial Filter Topology

noncomputable section

namespace StrongConv.L86

open StrongConv

section Alg
variable {R ι : Type*} [Ring R] [Fintype ι]

lemma sum_pow_words (f : ι → R) (p : ℕ) :
    (∑ i, f i) ^ p = ∑ x : Fin p → ι, (List.ofFn fun j => f (x j)).prod := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum]
    symm
    rw [← (Fin.consEquiv (fun _ : Fin (p + 1) => ι)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun x _ => ?_))
    simp [Fin.consEquiv, List.ofFn_succ]

end Alg


section Op
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma adj_sum {d : ℕ} (u : Fin d → H →L[ℂ] H) :
    ∑ i, (u i + star (u i)) = ∑ l : Fin d ⊕ Fin d, letterOp u l := by
  rw [Fintype.sum_sum_type]; simp [letterOp, Finset.sum_add_distrib]

lemma wordEval_ofFn {d p : ℕ} (u : Fin d → H →L[ℂ] H) (x : Fin p → Fin d ⊕ Fin d) :
    wordEval u (List.ofFn fun j => some (x j)) = (List.ofFn fun j => letterOp u (x j)).prod := by
  simp [wordEval, List.map_ofFn, Function.comp_def]

lemma adj_pow {d : ℕ} (u : Fin d → H →L[ℂ] H) (p : ℕ) :
    (∑ i, (u i + star (u i))) ^ p =
      ∑ x : Fin p → Fin d ⊕ Fin d, wordEval u (List.ofFn fun j => some (x j)) := by
  rw [adj_sum, sum_pow_words]
  simp_rw [wordEval_ofFn]

lemma isSA_adj {d : ℕ} (u : Fin d → H →L[ℂ] H) : IsSelfAdjoint (∑ i, (u i + star (u i))) := by
  unfold IsSelfAdjoint
  rw [star_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [star_add, star_star, add_comm]

end Op

lemma fnCalc_pow {A : Type*} [CStarAlgebra A] (T : A) (hT : IsSelfAdjoint T) (p : ℕ) :
    fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) T = T ^ p := by
  unfold fnCalc
  rw [← cfc_pow_id (R := ℂ) T p]
  refine cfc_congr (fun z hz => ?_)
  have := hT.mem_spectrum_eq_re hz
  simp only [eval_pow, eval_X, Complex.ofReal_pow]
  rw [← this]


lemma trN_sum {N : ℕ} {ι : Type*} (s : Finset ι) (Y : ι → (OnesPerp N →L[ℂ] OnesPerp N)) :
    trN N (∑ x ∈ s, Y x) = ∑ x ∈ s, trN N (Y x) := by
  unfold trN
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum, Complex.re_sum, Finset.sum_div]

lemma uniformExp_sum {X : Type*} [Fintype X] {ι : Type*} (s : Finset ι) (f : ι → X → ℝ) :
    uniformExp (fun a => ∑ x ∈ s, f x a) = ∑ x ∈ s, uniformExp (f x) := by
  unfold uniformExp
  rw [Finset.sum_comm, Finset.sum_div]

/-- the word of letters `x` -/
def wd {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) : List (Letter d) := List.ofFn fun j => some (x j)

/-- the group element of the word -/
def gx {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) : FreeGroup (Fin d) := wordFree (wd x)

/-- `E tr_N` of the word -/
def aN {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) (N : ℕ) : ℝ :=
  uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) => trN N (wordEval (sModel σ) (wd x)))

lemma F_eq (d p N : ℕ) :
    uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ))) =
      ∑ x : Fin p → Fin d ⊕ Fin d, aN x N := by
  have h : ∀ σ : Fin d → Equiv.Perm (Fin N),
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ)) =
        ∑ x : Fin p → Fin d ⊕ Fin d, trN N (wordEval (sModel σ) (wd x)) := by
    intro σ
    unfold adjPerp
    rw [fnCalc_pow _ (isSA_adj (sModel σ)) p, adj_pow, trN_sum]
    rfl
  simp_rw [h]
  rw [uniformExp_sum]
  rfl

lemma tau_adj_pow (d p : ℕ) :
    tau (adjFree d ^ p) = ∑ x : Fin p → Fin d ⊕ Fin d, tau (wordEval (sLimit d) (wd x)) := by
  have : adjFree d ^ p = ∑ x : Fin p → Fin d ⊕ Fin d, wordEval (sLimit d) (wd x) :=
    adj_pow (sLimit d) p
  rw [this]
  unfold tau
  simp [inner_sum]



lemma tendsto_aN {d p : ℕ} (x : Fin p → Fin d ⊕ Fin d) :
    Tendsto (aN x) atTop (𝓝 (if gx x = 1 then 1 else 0)) := by
  have h := tendsto_uniformExp_trN_wordEval d (wd x)
  have h2 := (Complex.continuous_re.tendsto _).comp h
  rw [S5.PartPerm.tau_wordEval_sLimit] at h2
  have e : (if wordFree (wd x) = 1 then (1 : ℂ) else 0).re = if gx x = 1 then 1 else 0 := by
    unfold gx; split_ifs <;> simp
  rw [Function.comp_def, e] at h2
  exact h2

/-- `ν₀(xᵖ) = τ(A_Fᵖ)`. -/
theorem nuAdj_zero_pow_eq (d p : ℕ) : nuAdj d 0 (X ^ p) = (tau (adjFree d ^ p)).re := by
  set F : ℕ → ℝ := fun N => uniformExp (fun σ : Fin d → Equiv.Perm (Fin N) =>
      trN N (fnCalc (fun x => ((X : ℝ[X]) ^ p).eval x) (adjPerp σ))) with hFdef
  have hF : ∀ N, F N = ∑ x : Fin p → Fin d ⊕ Fin d, aN x N := fun N => F_eq d p N
  set c0 : ℝ := ∑ x : Fin p → Fin d ⊕ Fin d, (if gx x = 1 then (1 : ℝ) else 0) with hc0def
  have hlim : Tendsto F atTop (𝓝 c0) := by
    have : F = fun N => ∑ x : Fin p → Fin d ⊕ Fin d, aN x N := funext hF
    rw [this]
    exact tendsto_finsetSum _ (fun x _ => tendsto_aN x)
  have hc0 : asympCoeff F 0 = c0 := by
    rw [asympCoeff]
    have : (fun N : ℕ => (N : ℝ) ^ 0 * (F N - ∑ i : Fin 0, asympCoeff F i / (N : ℝ) ^ (i : ℕ))) = F := by
      funext N; simp
    rw [this]
    exact hlim.limUnder_eq
  have h2 : (tau (adjFree d ^ p)).re = c0 := by
    rw [tau_adj_pow, Complex.re_sum, hc0def]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [S5.PartPerm.tau_wordEval_sLimit]
    unfold gx
    split_ifs <;> simp
  show asympCoeff F 0 = _
  rw [hc0, h2]

lemma norm_delta_one (d : ℕ) : ‖delta (1 : FreeGroup (Fin d))‖ = 1 := by
  unfold delta
  rw [lp.norm_single (by norm_num)]
  simp

lemma abs_re_tau_le (d : ℕ) (a : L2Free d →L[ℂ] L2Free d) : |(tau a).re| ≤ ‖a‖ := by
  calc |(tau a).re| ≤ ‖tau a‖ := Complex.abs_re_le_norm _
    _ ≤ ‖delta (1 : FreeGroup (Fin d))‖ * ‖a (delta 1)‖ := norm_inner_le_norm _ _
    _ ≤ ‖delta (1 : FreeGroup (Fin d))‖ * (‖a‖ * ‖delta (1 : FreeGroup (Fin d))‖) := by
        gcongr; exact a.le_opNorm _
    _ = ‖a‖ := by rw [norm_delta_one]; ring

/-- `limsup |ν₀(xᵖ)|^{1/p} ≤ ‖A_F‖`. -/
lemma limsup_nuAdj_zero_le (d : ℕ) :
    limsup (fun p : ℕ => |nuAdj d 0 (X ^ p)| ^ (1 / (p : ℝ))) atTop ≤ ‖adjFree d‖ := by
  apply limsup_le_of_le
  · exact ⟨0, fun a ha => by
      obtain ⟨n, hn⟩ := (eventually_atTop.mp ha)
      exact le_trans (by positivity) (hn n le_rfl)⟩
  · filter_upwards [eventually_ge_atTop 1] with p hp
    rw [nuAdj_zero_pow_eq]
    have h1 : |(tau (adjFree d ^ p)).re| ≤ ‖adjFree d‖ ^ p :=
      (abs_re_tau_le d _).trans (norm_pow_le' _ (by omega))
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    calc |(tau (adjFree d ^ p)).re| ^ (1 / (p : ℝ))
        ≤ (‖adjFree d‖ ^ p) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow (abs_nonneg _) h1 (by positivity)
      _ = ‖adjFree d‖ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), mul_one_div_cancel hp'.ne',
            Real.rpow_one]

end StrongConv.L86

namespace StrongConv

theorem supp_subset_Icc_rhoStair_of_extends_nuAdj_dev (d : ℕ) (hd : 2 ≤ d) (m : ℕ) (hm : m ≤ d)
    (μ : smoothFun →ₗ[ℝ] ℝ) (hμ : IsCSDistribution μ)
    (hext : ∀ h : ℝ[X], μ (polyFun h) = nuAdj d m h) :
    supp μ ⊆ Set.Icc (-rhoStair d m) (rhoStair d m) := by
  have hsq : (1 : ℝ) ≤ Real.sqrt (2 * d - 1) := by
    rw [Real.one_le_sqrt]
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hK : ‖adjFree d‖ = 2 * Real.sqrt (2 * d - 1) := norm_adjFree d (by omega)
  -- the limsup form of Lemma 4.9, with `μ(xᵖ)` replaced by `νₘ(xᵖ)`
  have h49 := supp_subset_Icc_limsup μ hμ
  simp_rw [hext] at h49
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · have hρ : rhoStair d 0 = ‖adjFree d‖ := by
        rw [hK, rhoStair, if_pos (by push_cast; linarith)]
      refine h49.trans (Set.Icc_subset_Icc ?_ ?_)
      · rw [hρ]; exact neg_le_neg (L86.limsup_nuAdj_zero_le d)
      · rw [hρ]; exact L86.limsup_nuAdj_zero_le d
    · have hρ : rhoStair d 1 = ‖adjFree d‖ := by
        rw [hK, rhoStair, if_pos (by push_cast; linarith)]
      rw [hρ]
      exact supp_subset_Icc_of_extends_nuAdj_one d μ hμ hext
  · obtain ⟨-, hL⟩ := limsup_abs_nuAdj_X_pow_le_rhoStair d m hm2 hm
    exact h49.trans (Set.Icc_subset_Icc (neg_le_neg hL) hL)

end StrongConv

end

theorem solution : type_of% @StrongConv.supp_subset_Icc_rhoStair_of_extends_nuAdj_dev :=
  @StrongConv.supp_subset_Icc_rhoStair_of_extends_nuAdj_dev

