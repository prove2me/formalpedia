-- Prove2me | solution 1 for SWPort.Davenport.siegel_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:33:43.932567+00:00
-- url     : https://prove2.me/submissions/65e29b83-d7b9-466d-8a52-9bab89bd3b95

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001
import Theorems.Thm_SWPort_Davenport_estermann_lemma

section
-- module Solutions.Artin.SW.Thm.Davenport_LFunction_ofReal_im_eq_zero
namespace SWPort
/-! Ported from prove2.me: `Davenport.LFunction_ofReal_im_eq_zero` (c14e3b6d-6df0-431c-9a31-1ad96a07d1e0, statement by alya); proof = accepted direct submission b7c4f87e-bea2-4e11-a595-a188a44e7e9d by alya. -/













open Finset DirichletCharacter
open ComplexConjugate

namespace SolDavImZero

/-- Values of a quadratic character are fixed by complex conjugation. -/
private lemma conj_apply_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (a : ZMod q) :
    conj (χ a) = χ a := by
  rcases hχ a with h | h | h <;> simp [h]

/-- Conjugating an `LSeries.term` of a quadratic character corresponds to conjugating `s`. -/
private lemma conj_term {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (s : ℂ) (n : ℕ) :
    conj (LSeries.term (χ ·) s n) = LSeries.term (χ ·) (conj s) n := by
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs with hn
  · simp
  · rw [map_div₀, conj_apply_eq χ hχ, Complex.cpow_conj _ _ (by
      rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), Complex.conj_natCast]

/-- The conjugated L-function agrees with the L-function on the half-plane `1 < re s`. -/
private lemma conj_LFunction_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    {s : ℂ} (hs : 1 < s.re) :
    conj (LFunction χ (conj s)) = LFunction χ s := by
  have hs' : 1 < (conj s).re := by simpa using hs
  rw [LFunction_eq_LSeries χ hs, LFunction_eq_LSeries χ hs', LSeries, LSeries, Complex.conj_tsum]
  congr 1
  ext n
  rw [conj_term χ hχ, Complex.conj_conj]

/-- For a nontrivial quadratic character, the L-function commutes with conjugation everywhere. -/
private lemma conj_LFunction_conj_all {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic)
    (hχ₁ : χ ≠ 1) (s : ℂ) :
    conj (LFunction χ (conj s)) = LFunction χ s := by
  set f : ℂ → ℂ := LFunction χ with hf
  set g : ℂ → ℂ := conj ∘ f ∘ conj with hg
  have hfd : Differentiable ℂ f := differentiable_LFunction hχ₁
  have hgd : Differentiable ℂ g := by
    intro z
    have := (hfd (conj z)).conj_conj
    simpa [hg] using this
  have hfa : AnalyticOnNhd ℂ f Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hfd
  have hga : AnalyticOnNhd ℂ g Set.univ := Complex.analyticOnNhd_univ_iff_differentiable.mpr hgd
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp [Set.mem_setOf_eq]
  have hev : g =ᶠ[nhds (2 : ℂ)] f := by
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact conj_LFunction_conj χ hχ hz
  have := AnalyticOnNhd.eq_of_eventuallyEq hga hfa hev
  have h := congrFun this s
  simpa [hg, hf] using h

end SolDavImZero

theorem _root_.SWPort.Davenport.LFunction_ofReal_im_eq_zero (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) (σ : ℝ) :
    (DirichletCharacter.LFunction χ σ).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  have := SolDavImZero.conj_LFunction_conj_all χ hχ hχ₁ σ
  rwa [Complex.conj_ofReal] at this

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_LFunction_one_pos
namespace SWPort
/-! Ported from prove2.me: `Davenport.LFunction_one_pos` (cf55de32-9ee2-47ac-ad9c-c634a527ef4d, statement by alya); proof = accepted direct submission 5c7ce1ca-7198-435f-9fb9-77917580ea1d by alya. -/










open Finset DirichletCharacter

namespace SolDavOnePos

open Complex Topology Filter
open ArithmeticFunction hiding log
open scoped ComplexOrder

/-- `ζ(s) L(s,χ) = L(zetaMul χ, s)` for `1 < re s`. -/
private lemma zeta_mul_LFunction_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) :
    riemannZeta s * LFunction χ s = LSeries (χ.zetaMul ·) s := by
  rw [zetaMul, ← ArithmeticFunction.coe_mul, LSeries_convolution']
  · simp only [χ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact LSeries_congr χ.apply_eq_toArithmeticFunction_apply s
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs

/-- The abscissa of absolute convergence of `zetaMul χ` is at most `1`. -/
private lemma abscissa_zetaMul_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    LSeries.abscissaOfAbsConv (χ.zetaMul ·) ≤ (1 : ℝ) :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦
    LSeriesSummable_zetaMul χ (by simpa using hy)

/-- For real `x > 1`, `L(zetaMul χ, x)` is a positive real (in the complex order). -/
private lemma LSeries_zetaMul_pos {q : ℕ} (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) {x : ℝ}
    (hx : 1 < x) :
    0 < LSeries (χ.zetaMul ·) x := by
  refine ArithmeticFunction.LSeries_positive (fun n ↦ zetaMul_nonneg hχ.sq_eq_one n) ?_ ?_
  · have h1 : χ.zetaMul 1 = 1 := χ.isMultiplicative_zetaMul.map_one
    rw [h1]; exact zero_lt_one
  · exact lt_of_le_of_lt (abscissa_zetaMul_le χ) (by exact_mod_cast hx)

/-- For real `x > 1`, `L(x, χ)` is a positive real (in the complex order). -/
private lemma LFunction_pos_of_one_lt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) {x : ℝ} (hx : 1 < x) :
    0 < LFunction χ x := by
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have hprod := LSeries_zetaMul_pos χ hχ hx
  rw [← zeta_mul_LFunction_eq χ hx'] at hprod
  have hζ := riemannZeta_pos_of_one_lt hx
  rw [Complex.pos_iff] at hprod hζ ⊢
  obtain ⟨hζre, hζim⟩ := hζ
  obtain ⟨hpre, hpim⟩ := hprod
  rw [Complex.mul_re, ← hζim] at hpre
  rw [Complex.mul_im, ← hζim] at hpim
  simp only [zero_mul, sub_zero, add_zero] at hpre hpim
  constructor
  · exact pos_of_mul_pos_right hpre hζre.le
  · have := (mul_eq_zero.mp hpim.symm).resolve_left hζre.ne'
    exact this.symm

end SolDavOnePos

theorem _root_.SWPort.Davenport.LFunction_one_pos (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) (hχ₁ : χ ≠ 1) :
    0 < (DirichletCharacter.LFunction χ 1).re := by
  open Topology Filter in
  have hcont : Filter.Tendsto (fun x : ℝ ↦ LFunction χ (x : ℂ)) (𝓝[>] (1 : ℝ))
      (𝓝 (LFunction χ 1)) := by
    have h1 : Filter.Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 ((1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 := (differentiable_LFunction hχ₁ ((1 : ℝ) : ℂ)).continuousAt.tendsto
    exact h2.comp h1
  have hre : 0 ≤ (LFunction χ 1).re := by
    refine ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hcont) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Complex.pos_iff.mp (SolDavOnePos.LFunction_pos_of_one_lt χ hχ hx)).1.le
  have him : (LFunction χ 1).im = 0 := by
    refine tendsto_nhds_unique (Complex.continuous_im.continuousAt.tendsto.comp hcont) ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (Complex.pos_iff.mp (SolDavOnePos.LFunction_pos_of_one_lt χ hχ hx)).2
  have hne := DirichletCharacter.LFunction_apply_one_ne_zero hχ₁
  rcases hre.lt_or_eq with h | h
  · exact h
  · exact absurd (Complex.ext (by simpa using h.symm) (by simpa using him)) hne

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_deriv_LFunction_bound
namespace SWPort
/-! Ported from prove2.me: `Davenport.deriv_LFunction_bound` (4593099f-60e7-4438-b99c-61d859e045c6, statement by alya); proof = accepted direct submission e970c8ab-fee0-47c1-9a42-03c5c9556b34 by alya. -/












open Finset MeasureTheory Set Complex Filter Topology Asymptotics

namespace DLFB

/-! ### Partial sums of a Dirichlet character -/

variable {q : ℕ} [NeZero q]

/-- Reindexing a sum over `range q` as a sum over `ZMod q`. -/
private lemma sum_range_eq_sum_zmod_p0 (f : ZMod q → ℂ) :
    ∑ j ∈ Finset.range q, f (j : ZMod q) = ∑ a : ZMod q, f a := by
  refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod q)) (j := fun a => a.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro a _; rfl

/-- A complete block of `q` consecutive values of a non-principal character sums to zero. -/
private lemma sum_block_eq_zero_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q) = 0 := by
  calc ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q)
      = ∑ j ∈ Finset.range q, (fun a : ZMod q => χ ((m : ZMod q) + a)) (j : ZMod q) :=
        Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    _ = ∑ a : ZMod q, χ ((m : ZMod q) + a) :=
        sum_range_eq_sum_zmod_p0 (fun a : ZMod q => χ ((m : ZMod q) + a))
    _ = ∑ a : ZMod q, χ a :=
        Fintype.sum_equiv (Equiv.addLeft ((m : ZMod q))) _ _ (fun a => rfl)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- `‖∑_{k < n} χ(k)‖ ≤ q`. -/
private lemma norm_sum_range_le_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖ ≤ q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n q with hn | hn
    · calc ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖
          ≤ ∑ k ∈ Finset.range n, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
        _ = n := by simp
        _ ≤ q := by exact_mod_cast hn
    · have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      set m := n - q with hm
      have hmn : m < n := by omega
      have hnm : n = m + q := by omega
      have hsplit : ∑ k ∈ Finset.range m, χ (k : ZMod q)
          + ∑ k ∈ Finset.Ico m n, χ (k : ZMod q) = ∑ k ∈ Finset.range n, χ (k : ZMod q) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
        exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) hmn.le
      have hzero : ∑ k ∈ Finset.Ico m n, χ (k : ZMod q) = 0 := by
        rw [Finset.sum_Ico_eq_sum_range]
        have : n - m = q := by omega
        rw [this]
        exact sum_block_eq_zero_p0 χ hχ m
      rw [← hsplit, hzero, add_zero]
      exact ih m hmn

/-- `‖G χ t‖ ≤ q` for a non-principal character. -/
private lemma norm_G_le_q_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) (t : ℝ) :
    ‖G_p0 χ t‖ ≤ q := by
  have hnt : Nontrivial (ZMod q) := by
    haveI : Fact (1 < q) := ⟨by omega⟩
    infer_instance
  have hz : χ (0 : ZMod q) = 0 := MulChar.map_zero χ
  have : G_p0 χ t = ∑ k ∈ Finset.range (⌊t⌋₊ + 1), χ (k : ZMod q) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      exact Finset.mem_range.mpr (by omega)
    · intro x hx hx'
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Icc, not_and, not_le] at hx'
      have : x = 0 := by omega
      subst this
      simpa using hz
  rw [this]
  exact norm_sum_range_le_p0 χ hχ _

/-- `‖G χ t‖ ≤ t` for `0 ≤ t`. -/
private lemma norm_G_le_self_p0 (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 0 ≤ t) :
    ‖G_p0 χ t‖ ≤ t := by
  calc ‖G_p0 χ t‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
    _ = (⌊t⌋₊ : ℝ) := by simp
    _ ≤ t := Nat.floor_le ht

/-- `G χ` vanishes below `1`. -/
private lemma G_eq_zero_p0 (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : t < 1) : G_p0 χ t = 0 := by
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [G_p0, this]

/-! ### The Mellin representation -/

private lemma locallyIntegrable_G_p0 (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn (G_p0 χ) (Ioi (0 : ℝ)) := by
  have h1 : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ici (0 : ℝ)) :=
    (continuous_const.continuousOn).locallyIntegrableOn measurableSet_Ici
  have h2 := locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) (fun k : ℕ => (χ k : ℂ)) (m := 1) (a := 0)
    le_rfl h1
  simp only [one_mul] at h2
  exact h2.mono_set Ioi_subset_Ici_self

private lemma isBigO_G_top_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) :
    (G_p0 χ) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun t => ?_))
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_G_le_q_p0 χ hχ hq t

private lemma isBigO_G_bot_p0 (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (G_p0 χ) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  simp [G_eq_zero_p0 χ ht.2]

private lemma mellinConv_G_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (G_p0 χ) (-s) := by
  refine mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G_p0 χ) (isBigO_G_top_p0 χ hχ hq) ?_ (isBigO_G_bot_p0 χ _) ?_
  · simpa using hs
  · simp

private lemma mellin_hasDeriv_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    MellinConvergent (fun t => Real.log t • G_p0 χ t) (-s) ∧
      HasDerivAt (mellin (G_p0 χ)) (mellin (fun t => Real.log t • G_p0 χ t) (-s)) (-s) := by
  refine mellin_hasDerivAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G_p0 χ) (isBigO_G_top_p0 χ hχ hq) ?_ (isBigO_G_bot_p0 χ _) ?_
  · simpa using hs
  · simp

private lemma hasDerivAt_F_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    HasDerivAt (F_p0 χ)
      (mellin (G_p0 χ) (-s) - s * mellin (fun t => Real.log t • G_p0 χ t) (-s)) s := by
  have h := (mellin_hasDeriv_p0 χ hχ hq hs).2
  have h2 : HasDerivAt (fun z : ℂ => mellin (G_p0 χ) (-z))
      (mellin (fun t => Real.log t • G_p0 χ t) (-s) * (-1)) s :=
    h.comp s ((hasDerivAt_id s).neg)
  have h4 := (hasDerivAt_id s).mul h2
  have heq : (1 : ℂ) * mellin (G_p0 χ) (-s)
      + s * (mellin (fun t => Real.log t • G_p0 χ t) (-s) * (-1))
      = mellin (G_p0 χ) (-s) - s * mellin (fun t => Real.log t • G_p0 χ t) (-s) := by ring
  simp only [id] at h4
  rw [heq] at h4
  exact h4

/-- Restricting a Mellin integral to `Ioi 1`, using that `G χ` vanishes below `1`. -/
private lemma mellin_eq_integral_Ioi_one_p0 (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : MellinConvergent (G_p0 χ) s) :
    mellin (G_p0 χ) s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p0 χ t := by
  have hz : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G_p0 χ t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    rw [G_eq_zero_p0 χ ht.2, smul_zero]
  calc mellin (G_p0 χ) s = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • G_p0 χ t := rfl
    _ = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G_p0 χ t)
          + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p0 χ t := by
        rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
        exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (h.mono_set Ioc_subset_Ioi_self) (h.mono_set (Ioi_subset_Ioi zero_le_one))
    _ = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p0 χ t := by rw [hz, zero_add]

private lemma LFunction_eq_F_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s = F_p0 χ s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun n => ?_))
    simp only [Real.rpow_zero, norm_one, mul_one]
    have : (∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) = G_p0 χ (n : ℝ) := by
      simp [G_p0, Nat.floor_natCast]
    rw [this]
    exact norm_G_le_q_p0 χ hχ hq _
  have hmain := LSeries_eq_mul_integral (fun n : ℕ => (χ n : ℂ)) (r := 0) le_rfl
    (by linarith : (0 : ℝ) < s.re) (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) hO
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, hmain]
  have hconv : MellinConvergent (G_p0 χ) (-s) := mellinConv_G_p0 χ hχ hq (by linarith)
  rw [F_p0, mellin_eq_integral_Ioi_one_p0 χ hconv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [smul_eq_mul, G_p0]
  rw [mul_comm]
  congr 2
  ring

/-! ### Analytic continuation via the identity theorem -/

private lemma deriv_LFunction_eq_deriv_F (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q)
    {s : ℂ} (hs : 0 < s.re) :
    deriv (DirichletCharacter.LFunction χ) s = deriv (F_p0 χ) s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUopen
  have hFan : AnalyticOnNhd ℂ (F_p0 χ) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact ((hasDerivAt_F_p0 χ hχ hq hz).differentiableAt).differentiableWithinAt
  have hmem : (2 : ℂ) ∈ U := by simp [hU]
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] F_p0 χ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_F_p0 χ hχ hq hz
  have heqOn : EqOn (DirichletCharacter.LFunction χ) (F_p0 χ) U :=
    hLan.eqOn_of_preconnected_of_eventuallyEq hFan hUconn hmem hev
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hUopen.mem_nhds hs] with z hz using heqOn hz

/-! ### Elementary real estimates -/

private lemma rpow_sub_one_mul_self_p0 {σ t : ℝ} (ht0 : 0 < t) : t ^ (-σ - 1) * t = t ^ (-σ) := by
  have h : t ^ (-σ - 1) * t ^ (1 : ℝ) = t ^ (-σ - 1 + 1) := (Real.rpow_add ht0 _ _).symm
  rw [Real.rpow_one] at h
  rw [h]
  congr 1
  ring

private lemma rpow_neg_sigma_le_p0 {σ Q t : ℝ} (hQ0 : 0 < Q) (hqexp : Q ^ (1 - σ) ≤ Real.exp 1)
    (ht1 : 1 ≤ t) (htq : t ≤ Q) (hσ2 : σ ≤ 1) :
    t ^ (-σ) ≤ Real.exp 1 / t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  rw [le_div_iff₀ ht0]
  have h1 : t ^ (-σ) * t = t ^ (1 - σ) := by
    have h : t ^ (-σ) * t ^ (1 : ℝ) = t ^ (-σ + 1) := (Real.rpow_add ht0 _ _).symm
    rw [Real.rpow_one] at h
    rw [h]
    congr 1
    ring
  rw [h1]
  exact le_trans (Real.rpow_le_rpow ht0.le htq (by linarith)) hqexp

private lemma integral_Ioc_const_div_p0 (c : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    ∫ t in Ioc (1 : ℝ) b, c / t = c * Real.log b := by
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) b := by
    rw [Set.uIcc_of_le hb]
    intro hmem
    exact absurd hmem.1 (by norm_num)
  rw [← intervalIntegral.integral_of_le hb]
  have hrw : ∀ t : ℝ, c / t = c * (1 / t) := fun t => by ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul, integral_one_div h0, div_one]

private lemma log_le_shift {σ : ℝ} (hσ : 0 < σ) {c t : ℝ} (hc : 0 < c) (ht : c ≤ t) :
    Real.log t ≤ Real.log c + 2 / σ * t ^ (σ / 2) * c ^ (-(σ / 2)) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hc ht
  have h1 : Real.log (t / c) ≤ (t / c) ^ (σ / 2) / (σ / 2) :=
    Real.log_le_rpow_div (by positivity) (by linarith)
  rw [Real.log_div ht0.ne' hc.ne'] at h1
  have h2 : (t / c) ^ (σ / 2) = t ^ (σ / 2) * c ^ (-(σ / 2)) := by
    rw [Real.div_rpow ht0.le hc.le, Real.rpow_neg hc.le]
    ring
  rw [h2] at h1
  have h3 : t ^ (σ / 2) * c ^ (-(σ / 2)) / (σ / 2) = 2 / σ * t ^ (σ / 2) * c ^ (-(σ / 2)) := by
    field_simp
  rw [h3] at h1
  linarith

private lemma norm_mellin_le_p0 (f : ℝ → ℂ) (x : ℂ) :
    ‖mellin f x‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (x.re - 1) * ‖f t‖ := by
  rw [mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

private lemma rpow_mul_half {σ t : ℝ} (ht0 : 0 < t) :
    t ^ (-σ - 1) * t ^ (σ / 2) = t ^ (-(σ / 2) - 1) := by
  rw [← Real.rpow_add ht0]
  congr 1
  ring

private lemma integral_Ioi_zero_split_p0 {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi (0 : ℝ)))
    {b : ℝ} (hb : 1 ≤ b) :
    ∫ t in Ioi (0 : ℝ), w t
      = (∫ t in Ioc (0 : ℝ) 1, w t) + (∫ t in Ioc (1 : ℝ) b, w t) + ∫ t in Ioi b, w t := by
  have hw1 : IntegrableOn w (Ioi (1 : ℝ)) := hw.mono_set (Ioi_subset_Ioi zero_le_one)
  have h1 : ∫ t in Ioi (0 : ℝ), w t = (∫ t in Ioc (0 : ℝ) 1, w t) + ∫ t in Ioi (1 : ℝ), w t := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hw.mono_set Ioc_subset_Ioi_self) hw1
  have h2 : ∫ t in Ioi (1 : ℝ), w t = (∫ t in Ioc (1 : ℝ) b, w t) + ∫ t in Ioi b, w t := by
    rw [← Ioc_union_Ioi_eq_Ioi hb]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hw1.mono_set Ioc_subset_Ioi_self) (hw1.mono_set (Ioi_subset_Ioi hb))
  rw [h1, h2, ← add_assoc]

/-! ### Bounding the two Mellin integrals -/

private lemma bound_A_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 3 ≤ q) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ2 : σ ≤ 1) (hqexp : (q : ℝ) ^ (1 - σ) ≤ Real.exp 1) :
    ‖mellin (G_p0 χ) (-(σ : ℂ))‖ ≤ Real.exp 1 * Real.log q + Real.exp 1 / σ := by
  have hq2 : 2 ≤ q := by omega
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlt : (-σ - 1 : ℝ) < -1 := by linarith
  set u : ℝ → ℝ := fun t => t ^ (-σ - 1) * ‖G_p0 χ t‖ with hu
  have hconv : MellinConvergent (G_p0 χ) (-(σ : ℂ)) :=
    mellinConv_G_p0 χ hχ hq2 (by simpa using hσ0)
  have hIA : IntegrableOn u (Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm hconv)
      (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hu]
  -- step 1: the norm of the Mellin integral is at most the integral of `u`
  have hstep1 : ‖mellin (G_p0 χ) (-(σ : ℂ))‖ ≤ ∫ t in Ioi (0 : ℝ), u t := by
    have := norm_mellin_le_p0 (G_p0 χ) (-(σ : ℂ))
    simpa [hu] using this
  -- step 2: split the integral
  have hp1 : ∫ t in Ioc (0 : ℝ) 1, u t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    simp [hu, G_eq_zero_p0 χ ht.2]
  have hp2 : ∫ t in Ioc (1 : ℝ) (q : ℝ), u t ≤ Real.exp 1 * Real.log q := by
    have hmaj : IntegrableOn (fun t : ℝ => Real.exp 1 / t) (Ioc (1 : ℝ) (q : ℝ)) := by
      refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
      refine ContinuousOn.integrableOn_Icc ?_
      exact continuousOn_const.div continuousOn_id
        (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
    have hsub : Ioc (1 : ℝ) (q : ℝ) ⊆ Ioi (0 : ℝ) :=
      Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)
    calc ∫ t in Ioc (1 : ℝ) (q : ℝ), u t
        ≤ ∫ t in Ioc (1 : ℝ) (q : ℝ), Real.exp 1 / t := by
          refine setIntegral_mono_on (hIA.mono_set hsub) hmaj measurableSet_Ioc (fun t ht => ?_)
          have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
          have hG : ‖G_p0 χ t‖ ≤ t := norm_G_le_self_p0 χ ht0.le
          calc u t ≤ t ^ (-σ - 1) * t :=
                mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg ht0.le _)
            _ = t ^ (-σ) := rpow_sub_one_mul_self_p0 ht0
            _ ≤ Real.exp 1 / t := rpow_neg_sigma_le_p0 hq0 hqexp ht.1.le ht.2 hσ2
      _ = Real.exp 1 * Real.log q := integral_Ioc_const_div_p0 _ hq1
  have hp3 : ∫ t in Ioi (q : ℝ), u t ≤ Real.exp 1 / σ := by
    have hmaj : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-σ - 1)) (Ioi (q : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hlt hq0).const_mul _
    have hstep : ∫ t in Ioi (q : ℝ), u t ≤ ∫ t in Ioi (q : ℝ), (q : ℝ) * t ^ (-σ - 1) := by
      refine setIntegral_mono_on (hIA.mono_set (Ioi_subset_Ioi hq0.le)) hmaj measurableSet_Ioi
        (fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := lt_trans hq0 ht
      have hG : ‖G_p0 χ t‖ ≤ (q : ℝ) := norm_G_le_q_p0 χ hχ hq2 t
      calc u t ≤ t ^ (-σ - 1) * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg ht0.le _)
        _ = (q : ℝ) * t ^ (-σ - 1) := by ring
    have hqq : (q : ℝ) ^ (1 - σ) = (q : ℝ) * (q : ℝ) ^ (-σ) := by
      rw [show (1 - σ : ℝ) = 1 + -σ by ring, Real.rpow_add hq0, Real.rpow_one]
    have hval : ∫ t in Ioi (q : ℝ), (q : ℝ) * t ^ (-σ - 1) = (q : ℝ) ^ (1 - σ) / σ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt hq0,
        show (-σ - 1 + 1 : ℝ) = -σ by ring, hqq]
      field_simp
    rw [hval] at hstep
    refine le_trans hstep ?_
    gcongr
  rw [integral_Ioi_zero_split_p0 hIA hq1, hp1, zero_add] at hstep1
  linarith

private lemma bound_B (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 3 ≤ q) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ2 : σ ≤ 1) (hqexp : (q : ℝ) ^ (1 - σ) ≤ Real.exp 1) :
    ‖mellin (fun t => Real.log t • G_p0 χ t) (-(σ : ℂ))‖
      ≤ Real.exp 1 * Real.log q ^ 2 + Real.exp 1 * Real.log q / σ + 4 * Real.exp 1 / σ ^ 2 := by
  have hq2 : 2 ≤ q := by omega
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hlt : (-σ - 1 : ℝ) < -1 := by linarith
  have hlt2 : (-(σ / 2) - 1 : ℝ) < -1 := by linarith
  set v : ℝ → ℝ := fun t => t ^ (-σ - 1) * ‖Real.log t • G_p0 χ t‖ with hv
  have hconv : MellinConvergent (fun t => Real.log t • G_p0 χ t) (-(σ : ℂ)) :=
    (mellin_hasDeriv_p0 χ hχ hq2 (by simpa using hσ0)).1
  have hIB : IntegrableOn v (Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm hconv)
      (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hv]
  have hstep1 : ‖mellin (fun t => Real.log t • G_p0 χ t) (-(σ : ℂ))‖ ≤ ∫ t in Ioi (0 : ℝ), v t := by
    have := norm_mellin_le_p0 (fun t => Real.log t • G_p0 χ t) (-(σ : ℂ))
    simpa [hv] using this
  have hp1 : ∫ t in Ioc (0 : ℝ) 1, v t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    simp [hv, G_eq_zero_p0 χ ht.2]
  have hp2 : ∫ t in Ioc (1 : ℝ) (q : ℝ), v t ≤ Real.exp 1 * Real.log q ^ 2 := by
    have hmaj : IntegrableOn (fun t : ℝ => Real.exp 1 * Real.log q / t) (Ioc (1 : ℝ) (q : ℝ)) := by
      refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
      refine ContinuousOn.integrableOn_Icc ?_
      exact continuousOn_const.div continuousOn_id
        (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
    have hsub : Ioc (1 : ℝ) (q : ℝ) ⊆ Ioi (0 : ℝ) :=
      Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)
    calc ∫ t in Ioc (1 : ℝ) (q : ℝ), v t
        ≤ ∫ t in Ioc (1 : ℝ) (q : ℝ), Real.exp 1 * Real.log q / t := by
          refine setIntegral_mono_on (hIB.mono_set hsub) hmaj measurableSet_Ioc (fun t ht => ?_)
          have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
          have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht.1.le
          have hG : ‖G_p0 χ t‖ ≤ t := norm_G_le_self_p0 χ ht0.le
          have hlt' : Real.log t ≤ Real.log q := Real.log_le_log ht0 ht.2
          have hrp : (0 : ℝ) ≤ t ^ (-σ - 1) := Real.rpow_nonneg ht0.le _
          have h1 : ‖Real.log t • G_p0 χ t‖ ≤ Real.log q * t := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlogt]
            exact mul_le_mul hlt' hG (norm_nonneg _) hlogq
          calc v t ≤ t ^ (-σ - 1) * (Real.log q * t) :=
                mul_le_mul_of_nonneg_left h1 hrp
            _ = Real.log q * (t ^ (-σ - 1) * t) := by ring
            _ = Real.log q * t ^ (-σ) := by rw [rpow_sub_one_mul_self_p0 ht0]
            _ ≤ Real.log q * (Real.exp 1 / t) := by
                exact mul_le_mul_of_nonneg_left
                  (rpow_neg_sigma_le_p0 hq0 hqexp ht.1.le ht.2 hσ2) hlogq
            _ = Real.exp 1 * Real.log q / t := by ring
      _ = Real.exp 1 * Real.log q * Real.log q := integral_Ioc_const_div_p0 _ hq1
      _ = Real.exp 1 * Real.log q ^ 2 := by ring
  have hp3 : ∫ t in Ioi (q : ℝ), v t
      ≤ Real.exp 1 * Real.log q / σ + 4 * Real.exp 1 / σ ^ 2 := by
    set c₁ : ℝ := (q : ℝ) * Real.log q with hc₁
    set c₂ : ℝ := 2 * (q : ℝ) * (q : ℝ) ^ (-(σ / 2)) / σ with hc₂
    have hmaj : IntegrableOn
        (fun t : ℝ => c₁ * t ^ (-σ - 1) + c₂ * t ^ (-(σ / 2) - 1)) (Ioi (q : ℝ)) :=
      ((integrableOn_Ioi_rpow_of_lt hlt hq0).const_mul _).add
        ((integrableOn_Ioi_rpow_of_lt hlt2 hq0).const_mul _)
    have hstep : ∫ t in Ioi (q : ℝ), v t
        ≤ ∫ t in Ioi (q : ℝ), (c₁ * t ^ (-σ - 1) + c₂ * t ^ (-(σ / 2) - 1)) := by
      refine setIntegral_mono_on (hIB.mono_set (Ioi_subset_Ioi hq0.le)) hmaj measurableSet_Ioi
        (fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := lt_trans hq0 ht
      have htq : (q : ℝ) ≤ t := ht.le
      have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
      have hG : ‖G_p0 χ t‖ ≤ (q : ℝ) := norm_G_le_q_p0 χ hχ hq2 t
      have hrp : (0 : ℝ) ≤ t ^ (-σ - 1) := Real.rpow_nonneg ht0.le _
      have hlog : Real.log t ≤ Real.log q + 2 / σ * t ^ (σ / 2) * (q : ℝ) ^ (-(σ / 2)) :=
        log_le_shift hσ0 hq0 htq
      have h1 : ‖Real.log t • G_p0 χ t‖ ≤ Real.log t * (q : ℝ) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlogt]
        exact mul_le_mul_of_nonneg_left hG hlogt
      have h2 : Real.log t * (q : ℝ)
          ≤ (Real.log q + 2 / σ * t ^ (σ / 2) * (q : ℝ) ^ (-(σ / 2))) * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hlog hq0.le
      have h3 : t ^ (-(σ / 2) - 1) = t ^ (-σ - 1) * t ^ (σ / 2) := (rpow_mul_half ht0).symm
      calc v t ≤ t ^ (-σ - 1) * (Real.log t * (q : ℝ)) := mul_le_mul_of_nonneg_left h1 hrp
        _ ≤ t ^ (-σ - 1) * ((Real.log q + 2 / σ * t ^ (σ / 2) * (q : ℝ) ^ (-(σ / 2))) * (q : ℝ)) :=
            mul_le_mul_of_nonneg_left h2 hrp
        _ = c₁ * t ^ (-σ - 1) + c₂ * t ^ (-(σ / 2) - 1) := by
            rw [h3, hc₁, hc₂]; ring
    have hval : ∫ t in Ioi (q : ℝ), (c₁ * t ^ (-σ - 1) + c₂ * t ^ (-(σ / 2) - 1))
        = c₁ * (-(q : ℝ) ^ (-σ) / (-σ)) + c₂ * (-(q : ℝ) ^ (-(σ / 2)) / (-(σ / 2))) := by
      rw [integral_add ((integrableOn_Ioi_rpow_of_lt hlt hq0).const_mul _)
        ((integrableOn_Ioi_rpow_of_lt hlt2 hq0).const_mul _), integral_const_mul,
        integral_const_mul, integral_Ioi_rpow_of_lt hlt hq0, integral_Ioi_rpow_of_lt hlt2 hq0,
        show (-σ - 1 + 1 : ℝ) = -σ by ring, show (-(σ / 2) - 1 + 1 : ℝ) = -(σ / 2) by ring]
    have hqq : (q : ℝ) ^ (1 - σ) = (q : ℝ) * (q : ℝ) ^ (-σ) := by
      rw [show (1 - σ : ℝ) = 1 + -σ by ring, Real.rpow_add hq0, Real.rpow_one]
    have hhalf : (q : ℝ) ^ (-(σ / 2)) * (q : ℝ) ^ (-(σ / 2)) = (q : ℝ) ^ (-σ) := by
      rw [← Real.rpow_add hq0]
      congr 1
      ring
    have hfin : c₁ * (-(q : ℝ) ^ (-σ) / (-σ)) + c₂ * (-(q : ℝ) ^ (-(σ / 2)) / (-(σ / 2)))
        = (q : ℝ) ^ (1 - σ) * Real.log q / σ + 4 * (q : ℝ) ^ (1 - σ) / σ ^ 2 := by
      rw [hc₁, hc₂, hqq]
      field_simp
      nlinarith [hhalf, sq_nonneg σ]
    rw [hval, hfin] at hstep
    refine le_trans hstep ?_
    have e1 : (q : ℝ) ^ (1 - σ) * Real.log q / σ ≤ Real.exp 1 * Real.log q / σ := by
      gcongr
    have e2 : 4 * (q : ℝ) ^ (1 - σ) / σ ^ 2 ≤ 4 * Real.exp 1 / σ ^ 2 := by
      gcongr
    linarith
  rw [integral_Ioi_zero_split_p0 hIB hq1, hp1, zero_add] at hstep1
  linarith

/-! ### A numerical lower bound for `log 3` -/

private lemma log_three_gt_p0 : (13 : ℝ) / 12 < Real.log 3 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h : Real.log ((2 : ℝ) ^ (11 : ℕ)) < Real.log ((3 : ℝ) ^ (7 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

end DLFB

/-- **Davenport, §14.** For a non-principal Dirichlet character `χ` modulo `q ≥ 3` one has
`L'(σ, χ) ≪ (log q)^2` uniformly for `1 - 1 / log q ≤ σ ≤ 1`. -/
theorem _root_.SWPort.Davenport.deriv_LFunction_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → 3 ≤ q →
        ∀ σ : ℝ, 1 - 1 / Real.log q ≤ σ → σ ≤ 1 →
          ‖deriv (DirichletCharacter.LFunction χ) (σ : ℂ)‖ ≤ K * Real.log q ^ 2 := by
  refine ⟨10000, by norm_num, ?_⟩
  intro q _ χ hχ hq3 σ hσ1 hσ2
  have hq2 : 2 ≤ q := by omega
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hL : (13 : ℝ) / 12 < Real.log q :=
    lt_of_lt_of_le DLFB.log_three_gt_p0 (Real.log_le_log (by norm_num) hqR)
  have hLpos : (0 : ℝ) < Real.log q := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log q := by linarith
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  -- lower bound for `σ`
  have hinv : 1 / Real.log q < 12 / 13 := by
    rw [div_lt_div_iff₀ hLpos (by norm_num)]
    linarith
  have hσ13 : (1 : ℝ) / 13 < σ := by linarith
  have hσpos : (0 : ℝ) < σ := by linarith
  have h13 : (1 : ℝ) ≤ 13 * σ := by linarith
  have h169 : (1 : ℝ) ≤ 169 * σ ^ 2 := by nlinarith
  -- the key bound `q ^ (1 - σ) ≤ e`
  have hqexp : (q : ℝ) ^ (1 - σ) ≤ Real.exp 1 := by
    rw [Real.rpow_def_of_pos hq0]
    refine Real.exp_le_exp.mpr ?_
    have h1 : 1 - σ ≤ 1 / Real.log q := by linarith
    calc Real.log q * (1 - σ) ≤ Real.log q * (1 / Real.log q) :=
          mul_le_mul_of_nonneg_left h1 hLpos.le
      _ = 1 := by field_simp
  -- rewrite the derivative
  have hs : (0 : ℝ) < ((σ : ℂ)).re := by simpa using hσpos
  rw [DLFB.deriv_LFunction_eq_deriv_F χ hχ hq2 hs, (DLFB.hasDerivAt_F_p0 χ hχ hq2 hs).deriv]
  -- reduce to the two Mellin integrals
  have hnormσ : ‖(σ : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hσpos]
    exact hσ2
  have hsplit : ‖mellin (DLFB.G_p0 χ) (-(σ : ℂ))
        - (σ : ℂ) * mellin (fun t => Real.log t • DLFB.G_p0 χ t) (-(σ : ℂ))‖
      ≤ ‖mellin (DLFB.G_p0 χ) (-(σ : ℂ))‖
        + ‖mellin (fun t => Real.log t • DLFB.G_p0 χ t) (-(σ : ℂ))‖ := by
    calc ‖mellin (DLFB.G_p0 χ) (-(σ : ℂ))
          - (σ : ℂ) * mellin (fun t => Real.log t • DLFB.G_p0 χ t) (-(σ : ℂ))‖
        ≤ ‖mellin (DLFB.G_p0 χ) (-(σ : ℂ))‖
            + ‖(σ : ℂ) * mellin (fun t => Real.log t • DLFB.G_p0 χ t) (-(σ : ℂ))‖ :=
          norm_sub_le _ _
      _ = ‖mellin (DLFB.G_p0 χ) (-(σ : ℂ))‖
            + ‖(σ : ℂ)‖ * ‖mellin (fun t => Real.log t • DLFB.G_p0 χ t) (-(σ : ℂ))‖ := by
          rw [norm_mul]
      _ ≤ ‖mellin (DLFB.G_p0 χ) (-(σ : ℂ))‖
            + 1 * ‖mellin (fun t => Real.log t • DLFB.G_p0 χ t) (-(σ : ℂ))‖ := by
          gcongr
      _ = ‖mellin (DLFB.G_p0 χ) (-(σ : ℂ))‖
            + ‖mellin (fun t => Real.log t • DLFB.G_p0 χ t) (-(σ : ℂ))‖ := by ring
  have hA := DLFB.bound_A_p0 χ hχ hq3 hσpos hσ2 hqexp
  have hB := DLFB.bound_B χ hχ hq3 hσpos hσ2 hqexp
  -- numerical estimates
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hs1 : Real.exp 1 / σ ≤ 13 * Real.exp 1 := by
    rw [div_le_iff₀ hσpos]
    linarith [mul_le_mul_of_nonneg_left h13 hepos.le]
  have hs2 : Real.exp 1 * Real.log q / σ ≤ 13 * (Real.exp 1 * Real.log q) := by
    rw [div_le_iff₀ hσpos]
    linarith [mul_le_mul_of_nonneg_left h13 (mul_nonneg hepos.le hLpos.le)]
  have hs3 : 4 * Real.exp 1 / σ ^ 2 ≤ 676 * Real.exp 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_left h169 hepos.le]
  have hLL : Real.log q ≤ Real.log q ^ 2 := by nlinarith
  have h1L : (1 : ℝ) ≤ Real.log q ^ 2 := by nlinarith
  have hXY : Real.exp 1 * Real.log q ≤ Real.exp 1 * Real.log q ^ 2 :=
    mul_le_mul_of_nonneg_left hLL hepos.le
  have hX : Real.exp 1 ≤ Real.exp 1 * Real.log q ^ 2 := by
    linarith [mul_le_mul_of_nonneg_left h1L hepos.le]
  have hfinal : 704 * (Real.exp 1 * Real.log q ^ 2) ≤ 10000 * Real.log q ^ 2 := by
    have hc : (0 : ℝ) ≤ 10000 - 704 * Real.exp 1 := by linarith
    linarith [mul_nonneg hc (sq_nonneg (Real.log q))]
  linarith

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_norm_LFunction_le_of_re_pos
namespace SWPort
/-! Ported from prove2.me: `Davenport.norm_LFunction_le_of_re_pos` (1b12ac8c-53f5-4d66-b458-e6adf912aa70, statement by alya); proof = accepted direct submission 2b67b00d-6837-4ca2-b83d-7017bd5b5e4a by alya. -/


















open Finset DirichletCharacter

namespace DLFB

open MeasureTheory Set Complex Filter Topology Asymptotics

/-! ### Partial sums of a Dirichlet character -/

variable {q : ℕ} [NeZero q]

/-- Reindexing a sum over `range q` as a sum over `ZMod q`. -/
private lemma sum_range_eq_sum_zmod_p1 (f : ZMod q → ℂ) :
    ∑ j ∈ Finset.range q, f (j : ZMod q) = ∑ a : ZMod q, f a := by
  refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod q)) (j := fun a => a.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro a _; rfl

/-- A complete block of `q` consecutive values of a non-principal character sums to zero. -/
private lemma sum_block_eq_zero_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q) = 0 := by
  calc ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q)
      = ∑ j ∈ Finset.range q, (fun a : ZMod q => χ ((m : ZMod q) + a)) (j : ZMod q) :=
        Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    _ = ∑ a : ZMod q, χ ((m : ZMod q) + a) :=
        sum_range_eq_sum_zmod_p1 (fun a : ZMod q => χ ((m : ZMod q) + a))
    _ = ∑ a : ZMod q, χ a :=
        Fintype.sum_equiv (Equiv.addLeft ((m : ZMod q))) _ _ (fun a => rfl)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- `‖∑_{k < n} χ(k)‖ ≤ q`. -/
private lemma norm_sum_range_le_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖ ≤ q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n q with hn | hn
    · calc ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖
          ≤ ∑ k ∈ Finset.range n, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
        _ = n := by simp
        _ ≤ q := by exact_mod_cast hn
    · have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      set m := n - q with hm
      have hmn : m < n := by omega
      have hnm : n = m + q := by omega
      have hsplit : ∑ k ∈ Finset.range m, χ (k : ZMod q)
          + ∑ k ∈ Finset.Ico m n, χ (k : ZMod q) = ∑ k ∈ Finset.range n, χ (k : ZMod q) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
        exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) hmn.le
      have hzero : ∑ k ∈ Finset.Ico m n, χ (k : ZMod q) = 0 := by
        rw [Finset.sum_Ico_eq_sum_range]
        have : n - m = q := by omega
        rw [this]
        exact sum_block_eq_zero_p1 χ hχ m
      rw [← hsplit, hzero, add_zero]
      exact ih m hmn

/-- `‖G χ t‖ ≤ q` for a non-principal character. -/
private lemma norm_G_le_q_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) (t : ℝ) :
    ‖G_p1 χ t‖ ≤ q := by
  have hnt : Nontrivial (ZMod q) := by
    haveI : Fact (1 < q) := ⟨by omega⟩
    infer_instance
  have hz : χ (0 : ZMod q) = 0 := MulChar.map_zero χ
  have : G_p1 χ t = ∑ k ∈ Finset.range (⌊t⌋₊ + 1), χ (k : ZMod q) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      exact Finset.mem_range.mpr (by omega)
    · intro x hx hx'
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Icc, not_and, not_le] at hx'
      have : x = 0 := by omega
      subst this
      simpa using hz
  rw [this]
  exact norm_sum_range_le_p1 χ hχ _

omit [NeZero q] in
/-- `G χ` vanishes below `1`. -/
private lemma G_eq_zero_p1 (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : t < 1) : G_p1 χ t = 0 := by
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [G_p1, this]

/-! ### The Mellin representation -/

omit [NeZero q] in
private lemma locallyIntegrable_G_p1 (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn (G_p1 χ) (Ioi (0 : ℝ)) := by
  have h1 : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ici (0 : ℝ)) :=
    (continuous_const.continuousOn).locallyIntegrableOn measurableSet_Ici
  have h2 := locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) (fun k : ℕ => (χ k : ℂ)) (m := 1) (a := 0)
    le_rfl h1
  simp only [one_mul] at h2
  exact h2.mono_set Ioi_subset_Ici_self

private lemma isBigO_G_top_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) :
    (G_p1 χ) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun t => ?_))
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_G_le_q_p1 χ hχ hq t

omit [NeZero q] in
private lemma isBigO_G_bot_p1 (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (G_p1 χ) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  simp [G_eq_zero_p1 χ ht.2]

private lemma mellinConv_G_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (G_p1 χ) (-s) := by
  refine mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G_p1 χ) (isBigO_G_top_p1 χ hχ hq) ?_ (isBigO_G_bot_p1 χ _) ?_
  · simpa using hs
  · simp

private lemma mellin_hasDeriv_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    MellinConvergent (fun t => Real.log t • G_p1 χ t) (-s) ∧
      HasDerivAt (mellin (G_p1 χ)) (mellin (fun t => Real.log t • G_p1 χ t) (-s)) (-s) := by
  refine mellin_hasDerivAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G_p1 χ) (isBigO_G_top_p1 χ hχ hq) ?_ (isBigO_G_bot_p1 χ _) ?_
  · simpa using hs
  · simp

private lemma hasDerivAt_F_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    HasDerivAt (F_p1 χ)
      (mellin (G_p1 χ) (-s) - s * mellin (fun t => Real.log t • G_p1 χ t) (-s)) s := by
  have h := (mellin_hasDeriv_p1 χ hχ hq hs).2
  have h2 : HasDerivAt (fun z : ℂ => mellin (G_p1 χ) (-z))
      (mellin (fun t => Real.log t • G_p1 χ t) (-s) * (-1)) s :=
    h.comp s ((hasDerivAt_id s).neg)
  have h4 := (hasDerivAt_id s).mul h2
  have heq : (1 : ℂ) * mellin (G_p1 χ) (-s)
      + s * (mellin (fun t => Real.log t • G_p1 χ t) (-s) * (-1))
      = mellin (G_p1 χ) (-s) - s * mellin (fun t => Real.log t • G_p1 χ t) (-s) := by ring
  simp only [id] at h4
  rw [heq] at h4
  exact h4

omit [NeZero q] in
/-- Restricting a Mellin integral to `Ioi 1`, using that `G χ` vanishes below `1`. -/
private lemma mellin_eq_integral_Ioi_one_p1 (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : MellinConvergent (G_p1 χ) s) :
    mellin (G_p1 χ) s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p1 χ t := by
  have hz : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G_p1 χ t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    rw [G_eq_zero_p1 χ ht.2, smul_zero]
  calc mellin (G_p1 χ) s = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • G_p1 χ t := rfl
    _ = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G_p1 χ t)
          + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p1 χ t := by
        rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
        exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (h.mono_set Ioc_subset_Ioi_self) (h.mono_set (Ioi_subset_Ioi zero_le_one))
    _ = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p1 χ t := by rw [hz, zero_add]

private lemma LFunction_eq_F_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s = F_p1 χ s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun n => ?_))
    simp only [Real.rpow_zero, norm_one, mul_one]
    have : (∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) = G_p1 χ (n : ℝ) := by
      simp [G_p1, Nat.floor_natCast]
    rw [this]
    exact norm_G_le_q_p1 χ hχ hq _
  have hmain := LSeries_eq_mul_integral (fun n : ℕ => (χ n : ℂ)) (r := 0) le_rfl
    (by linarith : (0 : ℝ) < s.re) (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) hO
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, hmain]
  have hconv : MellinConvergent (G_p1 χ) (-s) := mellinConv_G_p1 χ hχ hq (by linarith)
  rw [F_p1, mellin_eq_integral_Ioi_one_p1 χ hconv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [smul_eq_mul, G_p1]
  rw [mul_comm]
  congr 2
  ring

/-! ### Analytic continuation via the identity theorem -/

private lemma LFunction_eq_F_of_re_pos_p0 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = F_p1 χ s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUopen
  have hFan : AnalyticOnNhd ℂ (F_p1 χ) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact ((hasDerivAt_F_p1 χ hχ hq hz).differentiableAt).differentiableWithinAt
  have hmem : (2 : ℂ) ∈ U := by simp [hU]
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] F_p1 χ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_F_p1 χ hχ hq hz
  have heqOn : EqOn (DirichletCharacter.LFunction χ) (F_p1 χ) U :=
    hLan.eqOn_of_preconnected_of_eventuallyEq hFan hUconn hmem hev
  exact heqOn (show s ∈ U from hs)

/-! ### Bounding the Mellin integral -/

private lemma norm_mellin_le_p1 (f : ℝ → ℂ) (x : ℂ) :
    ‖mellin f x‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (x.re - 1) * ‖f t‖ := by
  rw [mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

private lemma integral_Ioi_one_split {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi (0 : ℝ))) :
    ∫ t in Ioi (0 : ℝ), w t = (∫ t in Ioc (0 : ℝ) 1, w t) + ∫ t in Ioi (1 : ℝ), w t := by
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
  exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hw.mono_set Ioc_subset_Ioi_self) (hw.mono_set (Ioi_subset_Ioi zero_le_one))

/-- The main estimate: `‖∫₁^∞ t^{-s-1} G(t) dt‖ ≤ q / Re s`. -/
private lemma norm_mellin_G_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : ‖mellin (G_p1 χ) (-s)‖ ≤ (q : ℝ) / s.re := by
  have hlt : (-s.re - 1 : ℝ) < -1 := by linarith
  set u : ℝ → ℝ := fun t => t ^ (-s.re - 1) * ‖G_p1 χ t‖ with hu
  have hconv : MellinConvergent (G_p1 χ) (-s) := mellinConv_G_p1 χ hχ hq hs
  have hIA : IntegrableOn u (Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm hconv)
      (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hu]
  have hstep1 : ‖mellin (G_p1 χ) (-s)‖ ≤ ∫ t in Ioi (0 : ℝ), u t := by
    have := norm_mellin_le_p1 (G_p1 χ) (-s)
    simpa [hu] using this
  have hp1 : ∫ t in Ioc (0 : ℝ) 1, u t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    simp [hu, G_eq_zero_p1 χ ht.2]
  have hp2 : ∫ t in Ioi (1 : ℝ), u t ≤ (q : ℝ) / s.re := by
    have hmaj : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hlt one_pos).const_mul _
    have hstep : ∫ t in Ioi (1 : ℝ), u t ≤ ∫ t in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
      refine setIntegral_mono_on (hIA.mono_set (Ioi_subset_Ioi zero_le_one)) hmaj
        measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      have hG : ‖G_p1 χ t‖ ≤ (q : ℝ) := norm_G_le_q_p1 χ hχ hq t
      calc u t ≤ t ^ (-s.re - 1) * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg ht0.le _)
        _ = (q : ℝ) * t ^ (-s.re - 1) := by ring
    have hval : ∫ t in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt one_pos,
        show (-s.re - 1 + 1 : ℝ) = -s.re by ring, Real.one_rpow, neg_div_neg_eq, mul_one_div]
    rw [hval] at hstep
    exact hstep
  rw [integral_Ioi_one_split hIA, hp1, zero_add] at hstep1
  linarith

end DLFB

/-- **Davenport, §14.** For a non-principal Dirichlet character `χ` mod `q` and `Re s > 0`,
`‖L(s, χ)‖ ≤ ‖s‖ q / Re s`. -/
theorem _root_.SWPort.Davenport.norm_LFunction_le_of_re_pos (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * q / s.re := by
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : q ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  have hq2 : 2 ≤ q := by omega
  rw [DLFB.LFunction_eq_F_of_re_pos_p0 χ hχ hq2 hs, DLFB.F_p1, norm_mul]
  calc ‖s‖ * ‖mellin (DLFB.G_p1 χ) (-s)‖ ≤ ‖s‖ * ((q : ℝ) / s.re) :=
        mul_le_mul_of_nonneg_left (DLFB.norm_mellin_G_le χ hχ hq2 hs) (norm_nonneg s)
    _ = ‖s‖ * q / s.re := by ring

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_norm_LFunction_one_le
namespace SWPort
/-! Ported from prove2.me: `Davenport.norm_LFunction_one_le` (cfc76098-940a-4ab6-8f3b-192632471888, statement by alya); proof = accepted direct submission 3e67778d-9ba0-46d2-a507-5b30264ec2f9 by alya. -/


















open Finset DirichletCharacter

namespace DLFB

open MeasureTheory Set Complex Filter Topology Asymptotics

/-! ### Partial sums of a Dirichlet character -/

variable {q : ℕ} [NeZero q]

/-- Reindexing a sum over `range q` as a sum over `ZMod q`. -/
private lemma sum_range_eq_sum_zmod_p2 (f : ZMod q → ℂ) :
    ∑ j ∈ Finset.range q, f (j : ZMod q) = ∑ a : ZMod q, f a := by
  refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod q)) (j := fun a => a.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro a _; rfl

/-- A complete block of `q` consecutive values of a non-principal character sums to zero. -/
private lemma sum_block_eq_zero_p2 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q) = 0 := by
  calc ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q)
      = ∑ j ∈ Finset.range q, (fun a : ZMod q => χ ((m : ZMod q) + a)) (j : ZMod q) :=
        Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    _ = ∑ a : ZMod q, χ ((m : ZMod q) + a) :=
        sum_range_eq_sum_zmod_p2 (fun a : ZMod q => χ ((m : ZMod q) + a))
    _ = ∑ a : ZMod q, χ a :=
        Fintype.sum_equiv (Equiv.addLeft ((m : ZMod q))) _ _ (fun a => rfl)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

/-- `‖∑_{k < n} χ(k)‖ ≤ q`. -/
private lemma norm_sum_range_le_p2 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖ ≤ q := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n q with hn | hn
    · calc ‖∑ k ∈ Finset.range n, χ (k : ZMod q)‖
          ≤ ∑ k ∈ Finset.range n, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ Finset.range n, (1 : ℝ) :=
            Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
        _ = n := by simp
        _ ≤ q := by exact_mod_cast hn
    · have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
      set m := n - q with hm
      have hmn : m < n := by omega
      have hnm : n = m + q := by omega
      have hsplit : ∑ k ∈ Finset.range m, χ (k : ZMod q)
          + ∑ k ∈ Finset.Ico m n, χ (k : ZMod q) = ∑ k ∈ Finset.range n, χ (k : ZMod q) := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
        exact Finset.sum_Ico_consecutive _ (Nat.zero_le _) hmn.le
      have hzero : ∑ k ∈ Finset.Ico m n, χ (k : ZMod q) = 0 := by
        rw [Finset.sum_Ico_eq_sum_range]
        have : n - m = q := by omega
        rw [this]
        exact sum_block_eq_zero_p2 χ hχ m
      rw [← hsplit, hzero, add_zero]
      exact ih m hmn

/-- `‖G χ t‖ ≤ q` for a non-principal character. -/
private lemma norm_G_le_q_p2 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) (t : ℝ) :
    ‖G_p2 χ t‖ ≤ q := by
  have hnt : Nontrivial (ZMod q) := by
    haveI : Fact (1 < q) := ⟨by omega⟩
    infer_instance
  have hz : χ (0 : ZMod q) = 0 := MulChar.map_zero χ
  have : G_p2 χ t = ∑ k ∈ Finset.range (⌊t⌋₊ + 1), χ (k : ZMod q) := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      exact Finset.mem_range.mpr (by omega)
    · intro x hx hx'
      simp only [Finset.mem_range] at hx
      simp only [Finset.mem_Icc, not_and, not_le] at hx'
      have : x = 0 := by omega
      subst this
      simpa using hz
  rw [this]
  exact norm_sum_range_le_p2 χ hχ _

omit [NeZero q] in
/-- `‖G χ t‖ ≤ t` for `0 ≤ t`. -/
private lemma norm_G_le_self_p2 (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 0 ≤ t) :
    ‖G_p2 χ t‖ ≤ t := by
  calc ‖G_p2 χ t‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => DirichletCharacter.norm_le_one χ _)
    _ = (⌊t⌋₊ : ℝ) := by simp
    _ ≤ t := Nat.floor_le ht

omit [NeZero q] in
/-- `G χ` vanishes below `1`. -/
private lemma G_eq_zero_p2 (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : t < 1) : G_p2 χ t = 0 := by
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [G_p2, this]

/-! ### The Mellin representation -/

omit [NeZero q] in
private lemma locallyIntegrable_G_p2 (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn (G_p2 χ) (Ioi (0 : ℝ)) := by
  have h1 : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ici (0 : ℝ)) :=
    (continuous_const.continuousOn).locallyIntegrableOn measurableSet_Ici
  have h2 := locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) (fun k : ℕ => (χ k : ℂ)) (m := 1) (a := 0)
    le_rfl h1
  simp only [one_mul] at h2
  exact h2.mono_set Ioi_subset_Ici_self

private lemma isBigO_G_top_p2 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) :
    (G_p2 χ) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun t => ?_))
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_G_le_q_p2 χ hχ hq t

omit [NeZero q] in
private lemma isBigO_G_bot_p2 (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (G_p2 χ) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  simp [G_eq_zero_p2 χ ht.2]

private lemma mellinConv_G_p2 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (G_p2 χ) (-s) := by
  refine mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G_p2 χ) (isBigO_G_top_p2 χ hχ hq) ?_ (isBigO_G_bot_p2 χ _) ?_
  · simpa using hs
  · simp

private lemma mellin_hasDeriv_p2 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    MellinConvergent (fun t => Real.log t • G_p2 χ t) (-s) ∧
      HasDerivAt (mellin (G_p2 χ)) (mellin (fun t => Real.log t • G_p2 χ t) (-s)) (-s) := by
  refine mellin_hasDerivAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G_p2 χ) (isBigO_G_top_p2 χ hχ hq) ?_ (isBigO_G_bot_p2 χ _) ?_
  · simpa using hs
  · simp

private lemma hasDerivAt_F_p2 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    HasDerivAt (F_p2 χ)
      (mellin (G_p2 χ) (-s) - s * mellin (fun t => Real.log t • G_p2 χ t) (-s)) s := by
  have h := (mellin_hasDeriv_p2 χ hχ hq hs).2
  have h2 : HasDerivAt (fun z : ℂ => mellin (G_p2 χ) (-z))
      (mellin (fun t => Real.log t • G_p2 χ t) (-s) * (-1)) s :=
    h.comp s ((hasDerivAt_id s).neg)
  have h4 := (hasDerivAt_id s).mul h2
  have heq : (1 : ℂ) * mellin (G_p2 χ) (-s)
      + s * (mellin (fun t => Real.log t • G_p2 χ t) (-s) * (-1))
      = mellin (G_p2 χ) (-s) - s * mellin (fun t => Real.log t • G_p2 χ t) (-s) := by ring
  simp only [id] at h4
  rw [heq] at h4
  exact h4

omit [NeZero q] in
/-- Restricting a Mellin integral to `Ioi 1`, using that `G χ` vanishes below `1`. -/
private lemma mellin_eq_integral_Ioi_one_p2 (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : MellinConvergent (G_p2 χ) s) :
    mellin (G_p2 χ) s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p2 χ t := by
  have hz : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G_p2 χ t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    rw [G_eq_zero_p2 χ ht.2, smul_zero]
  calc mellin (G_p2 χ) s = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • G_p2 χ t := rfl
    _ = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G_p2 χ t)
          + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p2 χ t := by
        rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
        exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (h.mono_set Ioc_subset_Ioi_self) (h.mono_set (Ioi_subset_Ioi zero_le_one))
    _ = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G_p2 χ t := by rw [hz, zero_add]

private lemma LFunction_eq_F_p2 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s = F_p2 χ s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun n => ?_))
    simp only [Real.rpow_zero, norm_one, mul_one]
    have : (∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) = G_p2 χ (n : ℝ) := by
      simp [G_p2, Nat.floor_natCast]
    rw [this]
    exact norm_G_le_q_p2 χ hχ hq _
  have hmain := LSeries_eq_mul_integral (fun n : ℕ => (χ n : ℂ)) (r := 0) le_rfl
    (by linarith : (0 : ℝ) < s.re) (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) hO
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, hmain]
  have hconv : MellinConvergent (G_p2 χ) (-s) := mellinConv_G_p2 χ hχ hq (by linarith)
  rw [F_p2, mellin_eq_integral_Ioi_one_p2 χ hconv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [smul_eq_mul, G_p2]
  rw [mul_comm]
  congr 2
  ring

/-! ### Analytic continuation via the identity theorem -/

private lemma LFunction_eq_F_of_re_pos_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q)
    {s : ℂ} (hs : 0 < s.re) : DirichletCharacter.LFunction χ s = F_p2 χ s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUopen
  have hFan : AnalyticOnNhd ℂ (F_p2 χ) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact ((hasDerivAt_F_p2 χ hχ hq hz).differentiableAt).differentiableWithinAt
  have hmem : (2 : ℂ) ∈ U := by simp [hU]
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] F_p2 χ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_F_p2 χ hχ hq hz
  have heqOn : EqOn (DirichletCharacter.LFunction χ) (F_p2 χ) U :=
    hLan.eqOn_of_preconnected_of_eventuallyEq hFan hUconn hmem hev
  exact heqOn (show s ∈ U from hs)

/-! ### Elementary real estimates -/

private lemma rpow_sub_one_mul_self_p1 {σ t : ℝ} (ht0 : 0 < t) : t ^ (-σ - 1) * t = t ^ (-σ) := by
  have h : t ^ (-σ - 1) * t ^ (1 : ℝ) = t ^ (-σ - 1 + 1) := (Real.rpow_add ht0 _ _).symm
  rw [Real.rpow_one] at h
  rw [h]
  congr 1
  ring

private lemma rpow_neg_sigma_le_p1 {σ Q t : ℝ} (_hQ0 : 0 < Q) (hqexp : Q ^ (1 - σ) ≤ Real.exp 1)
    (ht1 : 1 ≤ t) (htq : t ≤ Q) (hσ2 : σ ≤ 1) :
    t ^ (-σ) ≤ Real.exp 1 / t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  rw [le_div_iff₀ ht0]
  have h1 : t ^ (-σ) * t = t ^ (1 - σ) := by
    have h : t ^ (-σ) * t ^ (1 : ℝ) = t ^ (-σ + 1) := (Real.rpow_add ht0 _ _).symm
    rw [Real.rpow_one] at h
    rw [h]
    congr 1
    ring
  rw [h1]
  exact le_trans (Real.rpow_le_rpow ht0.le htq (by linarith)) hqexp

private lemma integral_Ioc_const_div_p1 (c : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    ∫ t in Ioc (1 : ℝ) b, c / t = c * Real.log b := by
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) b := by
    rw [Set.uIcc_of_le hb]
    intro hmem
    exact absurd hmem.1 (by norm_num)
  rw [← intervalIntegral.integral_of_le hb]
  have hrw : ∀ t : ℝ, c / t = c * (1 / t) := fun t => by ring
  simp_rw [hrw]
  rw [intervalIntegral.integral_const_mul, integral_one_div h0, div_one]

private lemma norm_mellin_le_p2 (f : ℝ → ℂ) (x : ℂ) :
    ‖mellin f x‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (x.re - 1) * ‖f t‖ := by
  rw [mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

private lemma integral_Ioi_zero_split_p1 {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi (0 : ℝ)))
    {b : ℝ} (hb : 1 ≤ b) :
    ∫ t in Ioi (0 : ℝ), w t
      = (∫ t in Ioc (0 : ℝ) 1, w t) + (∫ t in Ioc (1 : ℝ) b, w t) + ∫ t in Ioi b, w t := by
  have hw1 : IntegrableOn w (Ioi (1 : ℝ)) := hw.mono_set (Ioi_subset_Ioi zero_le_one)
  have h1 : ∫ t in Ioi (0 : ℝ), w t = (∫ t in Ioc (0 : ℝ) 1, w t) + ∫ t in Ioi (1 : ℝ), w t := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hw.mono_set Ioc_subset_Ioi_self) hw1
  have h2 : ∫ t in Ioi (1 : ℝ), w t = (∫ t in Ioc (1 : ℝ) b, w t) + ∫ t in Ioi b, w t := by
    rw [← Ioc_union_Ioi_eq_Ioi hb]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hw1.mono_set Ioc_subset_Ioi_self) (hw1.mono_set (Ioi_subset_Ioi hb))
  rw [h1, h2, ← add_assoc]

/-! ### Bounding the Mellin integral -/

private lemma bound_A_p1 (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 3 ≤ q) {σ : ℝ}
    (hσ0 : 0 < σ) (hσ2 : σ ≤ 1) (hqexp : (q : ℝ) ^ (1 - σ) ≤ Real.exp 1) :
    ‖mellin (G_p2 χ) (-(σ : ℂ))‖ ≤ Real.exp 1 * Real.log q + Real.exp 1 / σ := by
  have hq2 : 2 ≤ q := by omega
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlt : (-σ - 1 : ℝ) < -1 := by linarith
  set u : ℝ → ℝ := fun t => t ^ (-σ - 1) * ‖G_p2 χ t‖ with hu
  have hconv : MellinConvergent (G_p2 χ) (-(σ : ℂ)) :=
    mellinConv_G_p2 χ hχ hq2 (by simpa using hσ0)
  have hIA : IntegrableOn u (Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm hconv)
      (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hu]
  have hstep1 : ‖mellin (G_p2 χ) (-(σ : ℂ))‖ ≤ ∫ t in Ioi (0 : ℝ), u t := by
    have := norm_mellin_le_p2 (G_p2 χ) (-(σ : ℂ))
    simpa [hu] using this
  have hp1 : ∫ t in Ioc (0 : ℝ) 1, u t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    simp [hu, G_eq_zero_p2 χ ht.2]
  have hp2 : ∫ t in Ioc (1 : ℝ) (q : ℝ), u t ≤ Real.exp 1 * Real.log q := by
    have hmaj : IntegrableOn (fun t : ℝ => Real.exp 1 / t) (Ioc (1 : ℝ) (q : ℝ)) := by
      refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
      refine ContinuousOn.integrableOn_Icc ?_
      exact continuousOn_const.div continuousOn_id
        (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))
    have hsub : Ioc (1 : ℝ) (q : ℝ) ⊆ Ioi (0 : ℝ) :=
      Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi zero_le_one)
    calc ∫ t in Ioc (1 : ℝ) (q : ℝ), u t
        ≤ ∫ t in Ioc (1 : ℝ) (q : ℝ), Real.exp 1 / t := by
          refine setIntegral_mono_on (hIA.mono_set hsub) hmaj measurableSet_Ioc (fun t ht => ?_)
          have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht.1
          have hG : ‖G_p2 χ t‖ ≤ t := norm_G_le_self_p2 χ ht0.le
          calc u t ≤ t ^ (-σ - 1) * t :=
                mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg ht0.le _)
            _ = t ^ (-σ) := rpow_sub_one_mul_self_p1 ht0
            _ ≤ Real.exp 1 / t := rpow_neg_sigma_le_p1 hq0 hqexp ht.1.le ht.2 hσ2
      _ = Real.exp 1 * Real.log q := integral_Ioc_const_div_p1 _ hq1
  have hp3 : ∫ t in Ioi (q : ℝ), u t ≤ Real.exp 1 / σ := by
    have hmaj : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-σ - 1)) (Ioi (q : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hlt hq0).const_mul _
    have hstep : ∫ t in Ioi (q : ℝ), u t ≤ ∫ t in Ioi (q : ℝ), (q : ℝ) * t ^ (-σ - 1) := by
      refine setIntegral_mono_on (hIA.mono_set (Ioi_subset_Ioi hq0.le)) hmaj measurableSet_Ioi
        (fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := lt_trans hq0 ht
      have hG : ‖G_p2 χ t‖ ≤ (q : ℝ) := norm_G_le_q_p2 χ hχ hq2 t
      calc u t ≤ t ^ (-σ - 1) * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg ht0.le _)
        _ = (q : ℝ) * t ^ (-σ - 1) := by ring
    have hqq : (q : ℝ) ^ (1 - σ) = (q : ℝ) * (q : ℝ) ^ (-σ) := by
      rw [show (1 - σ : ℝ) = 1 + -σ by ring, Real.rpow_add hq0, Real.rpow_one]
    have hval : ∫ t in Ioi (q : ℝ), (q : ℝ) * t ^ (-σ - 1) = (q : ℝ) ^ (1 - σ) / σ := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt hq0,
        show (-σ - 1 + 1 : ℝ) = -σ by ring, hqq]
      field_simp
    rw [hval] at hstep
    refine le_trans hstep ?_
    gcongr
  rw [integral_Ioi_zero_split_p1 hIA hq1, hp1, zero_add] at hstep1
  linarith

/-! ### A numerical lower bound for `log 3` -/

private lemma log_three_gt_p1 : (13 : ℝ) / 12 < Real.log 3 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h : Real.log ((2 : ℝ) ^ (11 : ℕ)) < Real.log ((3 : ℝ) ^ (7 : ℕ)) :=
    Real.log_lt_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

end DLFB

/-- **Davenport, §14.** For a non-principal Dirichlet character `χ` modulo `q` one has
`‖L(1, χ)‖ ≤ 6 log q`. -/
theorem _root_.SWPort.Davenport.norm_LFunction_one_le (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction χ 1‖ ≤ 6 * Real.log q := by
  -- `q ≥ 3`, since every character modulo `1` or `2` is trivial
  have hq0 : q ≠ 0 := NeZero.ne q
  have hq1 : q ≠ 1 := fun h => hχ (DirichletCharacter.level_one' χ h)
  have hq2 : q ≠ 2 := by
    rintro rfl
    refine hχ (MulChar.ext (fun a => ?_))
    have ha : ∀ b : (ZMod 2)ˣ, b = 1 := by decide
    rw [ha a]
    simp
  have hq3 : 3 ≤ q := by omega
  have hs : (0 : ℝ) < (1 : ℂ).re := by norm_num
  -- the Mellin bound at `σ = 1`
  have hqexp : (q : ℝ) ^ (1 - (1 : ℝ)) ≤ Real.exp 1 := by
    rw [sub_self, Real.rpow_zero]
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hA := DLFB.bound_A_p1 χ hχ hq3 (by norm_num : (0 : ℝ) < 1) (le_refl (1 : ℝ)) hqexp
  simp only [Complex.ofReal_one, div_one] at hA
  rw [DLFB.LFunction_eq_F_of_re_pos_p1 χ hχ (by omega : 2 ≤ q) hs, DLFB.F_p2, one_mul]
  -- numerical estimates
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
  have hL : (13 : ℝ) / 12 < Real.log q :=
    lt_of_lt_of_le DLFB.log_three_gt_p1 (Real.log_le_log (by norm_num) hqR)
  have hLpos : (0 : ℝ) < Real.log q := by linarith
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h1 : Real.exp 1 * 1 ≤ Real.exp 1 * (12 / 13 * Real.log q) :=
    mul_le_mul_of_nonneg_left (by linarith) hepos.le
  have hc : (0 : ℝ) ≤ 6 - 25 / 13 * Real.exp 1 := by linarith
  have h2 := mul_nonneg hc hLpos.le
  linarith

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_zeta_LFunction_prod_LSeries_nonneg
namespace SWPort
/-! Ported from prove2.me: `Davenport.zeta_LFunction_prod_LSeries_nonneg` (fd51d778-daa3-4513-8499-35a38fc55cf5, statement by alya); proof = accepted direct submission 8f853a15-8a1d-42f6-ae30-cdcff559f8c8 by alya. -/










open Finset DirichletCharacter

namespace SolDavenportProd

open ArithmeticFunction hiding log
open scoped ComplexOrder LSeries.notation

/-- Partial geometric sums of a value in `{0, 1, -1}` are nonnegative. -/
private lemma geom_nonneg {a : ℂ} (ha : a = 0 ∨ a = 1 ∨ a = -1) (n : ℕ) :
    0 ≤ ∑ i ∈ range n, a ^ i := by
  rcases ha with h | h | h
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, le_refl, pow_nonneg]
  · refine Finset.sum_nonneg fun i _ ↦ ?_
    simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]
    split_ifs
    exacts [le_rfl, zero_le_one]

/-- The local factor `(χ' ⋆ χ₁₂)(p^j)` is nonnegative unless `b = -1` and `a ≠ -1`. -/
private lemma D_nonneg {a b : ℂ} (ha : a = 0 ∨ a = 1 ∨ a = -1) (hb : b = 0 ∨ b = 1 ∨ b = -1)
    (hab : b = -1 → a = -1) (j : ℕ) :
    0 ≤ ∑ l ∈ range (j + 1), b ^ l * (a * b) ^ (j - l) := by
  rcases hb with hb | hb | hb
  · subst hb
    rcases j with _ | j
    · simp
    · rw [Finset.sum_eq_zero]
      intro l hl
      rcases Nat.eq_zero_or_pos l with rfl | hl'
      · simp
      · simp [zero_pow hl'.ne']
  · subst hb
    simp only [one_pow, one_mul, mul_one]
    have := Finset.sum_range_reflect (fun l ↦ a ^ l) (j + 1)
    simp only [Nat.add_sub_cancel] at this
    rw [this]
    exact geom_nonneg ha _
  · have ha' := hab hb
    subst hb ha'
    simp only [neg_mul_neg, mul_one, one_pow]
    exact geom_nonneg (Or.inr (Or.inr rfl)) _

private lemma toArith_mul_prime_pow {M K : ℕ} (ψ' : DirichletCharacter ℂ M) (ψ₁₂ : DirichletCharacter ℂ K)
    {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (toArithmeticFunction (ψ' ·) * toArithmeticFunction (ψ₁₂ ·)) (p ^ j) =
      ∑ l ∈ range (j + 1), ψ' p ^ l * ψ₁₂ p ^ (j - l) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal
    (fun x y ↦ toArithmeticFunction (ψ' ·) x * toArithmeticFunction (ψ₁₂ ·) y),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun l hl ↦ ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)) hp.pos]
  simp only [toArithmeticFunction, coe_mk, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and,
    ↓reduceIte, Nat.cast_pow, map_pow]

/-- Nonnegativity of `zetaMul ψ * (ψ' ⋆ ψ₁₂)` at prime powers, under a side condition. -/
private lemma zetaMul_mul_prime_pow_nonneg {N M K : ℕ} (ψ : DirichletCharacter ℂ N)
    (ψ' : DirichletCharacter ℂ M) (ψ₁₂ : DirichletCharacter ℂ K)
    (hψ : ψ ^ 2 = 1) (hψ' : ψ' ^ 2 = 1) (h12 : ∀ n : ℕ, ψ₁₂ n = ψ n * ψ' n)
    {p : ℕ} (hp : p.Prime) (hcond : ψ' p = -1 → ψ p = -1) (k : ℕ) :
    0 ≤ (zetaMul ψ * (toArithmeticFunction (ψ' ·) * toArithmeticFunction (ψ₁₂ ·))) (p ^ k) := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal
    (fun x y ↦ zetaMul ψ x * (toArithmeticFunction (ψ' ·) * toArithmeticFunction (ψ₁₂ ·)) y),
    Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_nonneg fun i hi ↦ ?_
  refine mul_nonneg (zetaMul_prime_pow_nonneg hψ hp i) ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp.pos,
    toArith_mul_prime_pow ψ' ψ₁₂ hp, h12 p]
  exact D_nonneg (MulChar.isQuadratic_iff_sq_eq_one.mpr hψ p)
    (MulChar.isQuadratic_iff_sq_eq_one.mpr hψ' p) hcond _

private lemma isMultiplicative_A {N M K : ℕ} (ψ : DirichletCharacter ℂ N) (ψ' : DirichletCharacter ℂ M)
    (ψ₁₂ : DirichletCharacter ℂ K) : (A ψ ψ' ψ₁₂).IsMultiplicative :=
  ((isMultiplicative_zetaMul ψ).mul (isMultiplicative_toArithmeticFunction ψ')).mul
    (isMultiplicative_toArithmeticFunction ψ₁₂)

private lemma A_prime_pow_nonneg {N M K : ℕ} (ψ : DirichletCharacter ℂ N) (ψ' : DirichletCharacter ℂ M)
    (ψ₁₂ : DirichletCharacter ℂ K) (hψ : ψ ^ 2 = 1) (hψ' : ψ' ^ 2 = 1)
    (h12 : ∀ n : ℕ, ψ₁₂ n = ψ n * ψ' n) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ A ψ ψ' ψ₁₂ (p ^ k) := by
  by_cases hc : ψ' p = -1 ∧ ψ p ≠ -1
  · have hA : A ψ ψ' ψ₁₂ =
        zetaMul ψ' * (toArithmeticFunction (ψ ·) * toArithmeticFunction (ψ₁₂ ·)) := by
      simp only [A, zetaMul]; ring
    rw [hA]
    exact zetaMul_mul_prime_pow_nonneg ψ' ψ ψ₁₂ hψ' hψ (fun n ↦ by rw [h12 n, mul_comm]) hp
      (fun h ↦ (hc.2 h).elim) k
  · have hA : A ψ ψ' ψ₁₂ =
        zetaMul ψ * (toArithmeticFunction (ψ' ·) * toArithmeticFunction (ψ₁₂ ·)) := by
      simp only [A, zetaMul]; ring
    rw [hA]
    refine zetaMul_mul_prime_pow_nonneg ψ ψ' ψ₁₂ hψ hψ' h12 hp (fun h ↦ ?_) k
    by_contra h'
    exact hc ⟨h, h'⟩

private lemma A_nonneg {N M K : ℕ} (ψ : DirichletCharacter ℂ N) (ψ' : DirichletCharacter ℂ M)
    (ψ₁₂ : DirichletCharacter ℂ K) (hψ : ψ ^ 2 = 1) (hψ' : ψ' ^ 2 = 1)
    (h12 : ∀ n : ℕ, ψ₁₂ n = ψ n * ψ' n) (n : ℕ) :
    0 ≤ A ψ ψ' ψ₁₂ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [ArithmeticFunction.map_zero, le_refl]
  · rw [(isMultiplicative_A ψ ψ' ψ₁₂).multiplicative_factorization _ hn, Finsupp.prod,
      Nat.support_factorization]
    exact Finset.prod_nonneg
      fun p hp ↦ A_prime_pow_nonneg ψ ψ' ψ₁₂ hψ hψ' h12 (Nat.prime_of_mem_primeFactors hp) _

private lemma LSeriesSummable_toArith {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗(toArithmeticFunction (ψ ·)) s :=
  (LSeriesSummable_congr _ fun h ↦ (ψ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
      ZMod.LSeriesSummable_of_one_lt_re ψ hs

private lemma LSeriesSummable_A {N M K : ℕ} [NeZero N] [NeZero M] [NeZero K] (ψ : DirichletCharacter ℂ N)
    (ψ' : DirichletCharacter ℂ M) (ψ₁₂ : DirichletCharacter ℂ K) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable ↗(A ψ ψ' ψ₁₂) s :=
  ArithmeticFunction.LSeriesSummable_mul
    (ArithmeticFunction.LSeriesSummable_mul (LSeriesSummable_zetaMul ψ hs)
      (LSeriesSummable_toArith ψ' hs)) (LSeriesSummable_toArith ψ₁₂ hs)

private lemma LSeries_zetaMul_eq {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(zetaMul ψ) s = riemannZeta s * ψ.LFunction s := by
  rw [zetaMul, ← ArithmeticFunction.coe_mul, LSeries_convolution']
  · rw [ψ.LFunction_eq_LSeries hs]
    congr 1
    · simp_rw [← LSeries_zeta_eq_riemannZeta hs, ← natCoe_apply]
    · exact (LSeries_congr ψ.apply_eq_toArithmeticFunction_apply s).symm
  · exact LSeriesSummable_zeta_iff.mpr hs
  · exact LSeriesSummable_toArith ψ hs

private lemma LSeries_toArith_eq {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(toArithmeticFunction (ψ ·)) s = ψ.LFunction s := by
  rw [ψ.LFunction_eq_LSeries hs]
  exact (LSeries_congr ψ.apply_eq_toArithmeticFunction_apply s).symm

private lemma LSeries_A_eq {N M K : ℕ} [NeZero N] [NeZero M] [NeZero K] (ψ : DirichletCharacter ℂ N)
    (ψ' : DirichletCharacter ℂ M) (ψ₁₂ : DirichletCharacter ℂ K) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(A ψ ψ' ψ₁₂) s =
      riemannZeta s * ψ.LFunction s * ψ'.LFunction s * ψ₁₂.LFunction s := by
  rw [A, ArithmeticFunction.LSeries_mul' (ArithmeticFunction.LSeriesSummable_mul
      (LSeriesSummable_zetaMul ψ hs) (LSeriesSummable_toArith ψ' hs))
      (LSeriesSummable_toArith ψ₁₂ hs),
    ArithmeticFunction.LSeries_mul' (LSeriesSummable_zetaMul ψ hs) (LSeriesSummable_toArith ψ' hs),
    LSeries_zetaMul_eq ψ hs, LSeries_toArith_eq ψ' hs, LSeries_toArith_eq ψ₁₂ hs]

/-- Evaluating a level-changed character at a natural number which is a unit. -/
private lemma changeLevel_natCast_of_isUnit {n m : ℕ} (hm : n ∣ m) (ψ : DirichletCharacter ℂ n) (k : ℕ)
    (hk : IsUnit (k : ZMod m)) :
    changeLevel hm ψ (k : ZMod m) = ψ (k : ZMod n) := by
  obtain ⟨u, hu⟩ := hk
  rw [← hu, changeLevel_eq_cast_of_dvd, hu, ZMod.cast_natCast hm]

private lemma mul_changeLevel_natCast (q₁ q₂ : ℕ) (χ₁ : DirichletCharacter ℂ q₁)
    (χ₂ : DirichletCharacter ℂ q₂) (n : ℕ) :
    (changeLevel (Nat.dvd_mul_right q₁ q₂) χ₁ * changeLevel (Nat.dvd_mul_left q₂ q₁) χ₂)
      (n : ZMod (q₁ * q₂)) = χ₁ n * χ₂ n := by
  rw [MulChar.mul_apply]
  by_cases hn : IsUnit (n : ZMod (q₁ * q₂))
  · rw [changeLevel_natCast_of_isUnit _ _ _ hn, changeLevel_natCast_of_isUnit _ _ _ hn]
  · rw [MulChar.map_nonunit _ hn, zero_mul]
    rw [ZMod.isUnit_iff_coprime] at hn
    by_cases h1 : IsUnit (n : ZMod q₁)
    · by_cases h2 : IsUnit (n : ZMod q₂)
      · rw [ZMod.isUnit_iff_coprime] at h1 h2
        exact (hn (Nat.Coprime.mul_right h1 h2)).elim
      · rw [MulChar.map_nonunit _ h2, mul_zero]
    · rw [MulChar.map_nonunit _ h1, zero_mul]

end SolDavenportProd

open SolDavenportProd in
theorem _root_.SWPort.Davenport.zeta_LFunction_prod_LSeries_nonneg (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂)
    (h₁ : χ₁.IsQuadratic) (h₂ : χ₂.IsQuadratic) :
    ∃ a : ℕ → ℝ, a 1 = 1 ∧ (∀ n, 0 ≤ a n) ∧
      (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (a n : ℂ)) s) ∧
      ∀ s : ℂ, 1 < s.re →
        riemannZeta s * DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ₂ s *
          DirichletCharacter.LFunction
            (changeLevel (Nat.dvd_mul_right q₁ q₂) χ₁ * changeLevel (Nat.dvd_mul_left q₂ q₁) χ₂) s
          = LSeries (fun n => (a n : ℂ)) s := by
  open scoped ComplexOrder in
  set χ₁₂ := changeLevel (Nat.dvd_mul_right q₁ q₂) χ₁ * changeLevel (Nat.dvd_mul_left q₂ q₁) χ₂
    with hχ₁₂
  have h12 : ∀ n : ℕ, χ₁₂ n = χ₁ n * χ₂ n := mul_changeLevel_natCast q₁ q₂ χ₁ χ₂
  have hsq₁ : χ₁ ^ 2 = 1 := MulChar.isQuadratic_iff_sq_eq_one.mp h₁
  have hsq₂ : χ₂ ^ 2 = 1 := MulChar.isQuadratic_iff_sq_eq_one.mp h₂
  have hA := A_nonneg χ₁ χ₂ χ₁₂ hsq₁ hsq₂ h12
  have hre : ∀ n, ((A χ₁ χ₂ χ₁₂ n).re : ℂ) = A χ₁ χ₂ χ₁₂ n := fun n ↦ by
    obtain ⟨_, him⟩ := Complex.nonneg_iff.mp (hA n)
    exact Complex.ext (by simp) (by simpa using him)
  refine ⟨fun n ↦ (A χ₁ χ₂ χ₁₂ n).re, ?_, fun n ↦ (Complex.nonneg_iff.mp (hA n)).1, ?_, ?_⟩
  · show (A χ₁ χ₂ χ₁₂ 1).re = 1
    rw [(isMultiplicative_A χ₁ χ₂ χ₁₂).map_one, Complex.one_re]
  · intro s hs
    simpa only [hre] using LSeriesSummable_A χ₁ χ₂ χ₁₂ hs
  · intro s hs
    simp only [hre]
    exact (LSeries_A_eq χ₁ χ₂ χ₁₂ hs).symm

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_siegel_of_exceptional
namespace SWPort
/-! Ported from prove2.me: `Davenport.siegel_of_exceptional` (abd68937-3a2c-4c76-a736-b2e2d9b7c599, statement by tianyipeng); proof = accepted sketch submission 4890dffc-72e8-46d5-ad38-731390c3f8fa by tianyipeng. -/








open Complex ComplexOrder DirichletCharacter

set_option maxHeartbeats 1000000

/-- On the disc `|s - 2| ≤ 3/2` every Dirichlet `L`-function of a non-principal character
modulo `N` is bounded by `7N`. -/
private lemma ball_bound (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    (s : ℂ) (hs : s ∈ Metric.closedBall (2 : ℂ) (3 / 2)) :
    ‖DirichletCharacter.LFunction ψ s‖ ≤ 7 * (N : ℝ) := by
  rw [mem_closedBall_iff_norm] at hs
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hre : (1 : ℝ) / 2 ≤ s.re := by
    have h := (abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs)).1
    simp only [Complex.sub_re, Complex.re_ofNat] at h
    linarith
  have hnorm : ‖s‖ ≤ 7 / 2 := by
    have h : ‖s‖ ≤ ‖s - 2‖ + ‖(2 : ℂ)‖ := by simpa using norm_add_le (s - 2) (2 : ℂ)
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2] at h
    linarith
  refine (Davenport.norm_LFunction_le_of_re_pos N ψ hψ s (by linarith)).trans ?_
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < s.re)]
  nlinarith [norm_nonneg s]

/-- `x ^ 2` raised to `-(δ/4)` is `x ^ (-(δ/2))`. -/
private lemma sq_rpow (δ : ℝ) (x : ℝ) (hx : 0 ≤ x) :
    (x ^ 2) ^ (-(δ / 4)) = x ^ (-(δ / 2)) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  congr 1
  push_cast
  ring

/-- `log x ≤ (2/δ) * x ^ (δ/2)` for `x ≥ 1` and `δ > 0`. -/
private lemma log_le_rpow (δ : ℝ) (hδ : 0 < δ) (x : ℝ) (hx : 0 < x) :
    Real.log x ≤ (2 / δ) * x ^ (δ / 2) := by
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx (δ / 2))
  rw [Real.log_rpow hx] at h
  have key : δ * Real.log x ≤ 2 * x ^ (δ / 2) := by
    have hp := Real.rpow_pos_of_pos hx (δ / 2)
    linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
  linarith

theorem _root_.SWPort.Davenport.siegel_of_exceptional (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 20)
    (q₁ : ℕ) [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁)
    (hq₁ : χ₁.IsQuadratic) (hn₁ : χ₁ ≠ 1) (hp₁ : χ₁.IsPrimitive)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ₁ : β < 1) (hzero : DirichletCharacter.LFunction χ₁ β = 0)
    (hclose : 1 - β ≤ δ / 12) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsQuadratic → χ ≠ 1 → χ.IsPrimitive →
          C * (q : ℝ) ^ (-δ) < (DirichletCharacter.LFunction χ 1).re := by
  classical
  have hq₁1 : (1 : ℝ) ≤ (q₁ : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q₁)
  have hq₁0 : (0 : ℝ) < (q₁ : ℝ) := by linarith
  set A : ℝ := (DirichletCharacter.LFunction χ₁ 1).re with hAdef
  have hApos : 0 < A := Davenport.LFunction_one_pos q₁ χ₁ hq₁ hn₁
  set LA : ℝ := Real.log (q₁ : ℝ) with hLAdef
  have hALA : A ≤ 6 * LA := by
    have h := Davenport.norm_LFunction_one_le q₁ χ₁ hn₁
    have h2 : A ≤ ‖DirichletCharacter.LFunction χ₁ 1‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    linarith
  have hLA : 0 < LA := by linarith
  have hβpos : 0 < 1 - β := by linarith
  have hδinv : (0 : ℝ) < 2 / δ := by positivity
  set K : ℝ := (343 : ℝ) ^ (-(δ / 4)) * (q₁ : ℝ) ^ (-(δ / 2)) with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hq₁0 _)
  set CA : ℝ := (1 - β) * K / (288 * LA * (LA + 2 / δ)) with hCAdef
  have hdenpos : (0 : ℝ) < 288 * LA * (LA + 2 / δ) :=
    mul_pos (by linarith) (by linarith)
  have hCApos : 0 < CA := by
    rw [hCAdef]; exact div_pos (mul_pos hβpos hKpos) hdenpos
  have hAqpos : 0 < A * (q₁ : ℝ) ^ δ / 2 :=
    div_pos (mul_pos hApos (Real.rpow_pos_of_pos hq₁0 δ)) two_pos
  refine ⟨min CA (A * (q₁ : ℝ) ^ δ / 2), lt_min hCApos hAqpos, ?_⟩
  intro q _ χ hquad hne hprim
  haveI : NeZero (q₁ * q) := ⟨Nat.mul_ne_zero (NeZero.ne q₁) (NeZero.ne q)⟩
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  by_cases hχ3 :
      changeLevel (Nat.dvd_mul_right q₁ q) χ₁ * changeLevel (Nat.dvd_mul_left q q₁) χ = 1
  · -- The two characters induce the same character; then `q = q₁` and `χ = χ₁`.
    have hsq2 : (changeLevel (Nat.dvd_mul_left q q₁) χ) ^ 2 = 1 := by
      rw [← map_pow, hquad.sq_eq_one, map_one]
    have hinv : changeLevel (Nat.dvd_mul_right q₁ q) χ₁
        = changeLevel (Nat.dvd_mul_left q q₁) χ := by
      calc changeLevel (Nat.dvd_mul_right q₁ q) χ₁
          = changeLevel (Nat.dvd_mul_right q₁ q) χ₁ *
              (changeLevel (Nat.dvd_mul_left q q₁) χ * changeLevel (Nat.dvd_mul_left q q₁) χ) := by
            rw [← sq, hsq2, mul_one]
        _ = (changeLevel (Nat.dvd_mul_right q₁ q) χ₁ * changeLevel (Nat.dvd_mul_left q q₁) χ) *
              changeLevel (Nat.dvd_mul_left q q₁) χ := (mul_assoc _ _ _).symm
        _ = changeLevel (Nat.dvd_mul_left q q₁) χ := by rw [hχ3, one_mul]
    have hft : χ₁.FactorsThrough (Nat.gcd q₁ q) := χ₁.factorsThrough_gcd χ hinv
    have hdvd1 : q₁ ∣ q := by
      have h := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ₁ hft
      rw [hp₁] at h
      exact h.trans (Nat.gcd_dvd_right q₁ q)
    have hEq : changeLevel hdvd1 χ₁ = χ := by
      refine changeLevel_injective (Nat.dvd_mul_left q q₁) ?_
      rw [← changeLevel_trans]
      exact hinv
    have hdvd2 : q ∣ q₁ := by
      have hmem : q₁ ∈ χ.conductorSet := ⟨hdvd1, χ₁, hEq.symm⟩
      have h := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hmem
      rwa [hprim] at h
    have hqq : q = q₁ := Nat.dvd_antisymm hdvd2 hdvd1
    subst hqq
    have hχeq : χ = χ₁ := by
      rw [← hEq, changeLevel_self]
    rw [hχeq]
    have hrp : (q : ℝ) ^ δ * (q : ℝ) ^ (-δ) = 1 := by
      rw [← Real.rpow_add hq0]; simp
    have hqneg : (0 : ℝ) < (q : ℝ) ^ (-δ) := Real.rpow_pos_of_pos hq0 _
    calc min CA (A * (q : ℝ) ^ δ / 2) * (q : ℝ) ^ (-δ)
        ≤ (A * (q : ℝ) ^ δ / 2) * (q : ℝ) ^ (-δ) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hqneg.le
      _ = A / 2 * ((q : ℝ) ^ δ * (q : ℝ) ^ (-δ)) := by ring
      _ = A / 2 := by rw [hrp, mul_one]
      _ < A := by linarith
  · -- The generic case: the product character is nontrivial.
    obtain ⟨a, ha1, hann, hasum, haid⟩ :=
      Davenport.zeta_LFunction_prod_LSeries_nonneg q₁ q χ₁ χ hq₁ hquad
    set χ₃ := changeLevel (Nat.dvd_mul_right q₁ q) χ₁ * changeLevel (Nat.dvd_mul_left q q₁) χ
      with hχ3def
    have hquad3 : χ₃.IsQuadratic := by
      refine MulChar.isQuadratic_iff_sq_eq_one.mpr ?_
      rw [hχ3def, mul_pow, ← map_pow, ← map_pow, hq₁.sq_eq_one, hquad.sq_eq_one, map_one, map_one,
        mul_one]
    set f : ℂ → ℂ := fun s => DirichletCharacter.LFunction χ₁ s * DirichletCharacter.LFunction χ s *
      DirichletCharacter.LFunction χ₃ s with hfdef
    have hM1 : (1 : ℝ) ≤ 343 * (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (q₁ : ℝ) ^ 2 := by nlinarith
      have h2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
      have h3 : (1 : ℝ) * 1 ≤ (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2 :=
        mul_le_mul h1 h2 zero_le_one (by linarith)
      linarith
    have hfM : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2),
        ‖f s‖ ≤ 343 * (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2 := by
      intro s hs
      have h1 := ball_bound q₁ χ₁ hn₁ s hs
      have h2 := ball_bound q χ hne s hs
      have h3 := ball_bound (q₁ * q) χ₃ hχ3 s hs
      rw [Nat.cast_mul] at h3
      have e : ‖f s‖ = ‖DirichletCharacter.LFunction χ₁ s‖ * ‖DirichletCharacter.LFunction χ s‖ *
          ‖DirichletCharacter.LFunction χ₃ s‖ := by
        simp only [hfdef, norm_mul]
      rw [e]
      calc ‖DirichletCharacter.LFunction χ₁ s‖ * ‖DirichletCharacter.LFunction χ s‖ *
            ‖DirichletCharacter.LFunction χ₃ s‖
          ≤ (7 * (q₁ : ℝ)) * (7 * (q : ℝ)) * (7 * ((q₁ : ℝ) * (q : ℝ))) := by
            refine mul_le_mul ?_ h3 (norm_nonneg _) (by positivity)
            exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = 343 * (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2 := by ring
    have hFid : ∀ s : ℂ, 1 < s.re → riemannZeta s * f s = LSeries (fun n => (a n : ℂ)) s := by
      intro s hs
      rw [← haid s hs]
      simp only [hfdef]
      ring
    have hdiff : DifferentiableOn ℂ f (Metric.closedBall (2 : ℂ) (3 / 2)) :=
      (((differentiable_LFunction hn₁).mul (differentiable_LFunction hne)).mul
        (differentiable_LFunction hχ3)).differentiableOn
    have hfβ : (0 : ℝ) ≤ (f (β : ℂ)).re := by
      simp only [hfdef, hzero, zero_mul, Complex.zero_re, le_refl]
    have hest := Davenport.estermann_lemma f (343 * (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2) a hM1 hdiff hfM
      hasum hFid ha1 hann β hβ hβ₁ hfβ
    have him₁ : (DirichletCharacter.LFunction χ₁ 1).im = 0 := by
      simpa using Davenport.LFunction_ofReal_im_eq_zero q₁ χ₁ hq₁ hn₁ 1
    have himχ : (DirichletCharacter.LFunction χ 1).im = 0 := by
      simpa using Davenport.LFunction_ofReal_im_eq_zero q χ hquad hne 1
    have him₃ : (DirichletCharacter.LFunction χ₃ 1).im = 0 := by
      simpa using Davenport.LFunction_ofReal_im_eq_zero (q₁ * q) χ₃ hquad3 hχ3 1
    set X : ℝ := (DirichletCharacter.LFunction χ 1).re with hXdef
    set B : ℝ := (DirichletCharacter.LFunction χ₃ 1).re with hBdef
    have hf1 : (f 1).re = A * X * B := by
      simp only [hfdef, Complex.mul_re, Complex.mul_im, him₁, himχ, him₃, hAdef, hXdef, hBdef]
      ring
    rw [hf1] at hest
    have hXpos : 0 < X := Davenport.LFunction_one_pos q χ hquad hne
    have hBpos : 0 < B := Davenport.LFunction_one_pos (q₁ * q) χ₃ hquad3 hχ3
    set LB : ℝ := Real.log ((q₁ : ℝ) * (q : ℝ)) with hLBdef
    have hBLB : B ≤ 6 * LB := by
      have h := Davenport.norm_LFunction_one_le (q₁ * q) χ₃ hχ3
      rw [Nat.cast_mul] at h
      have h2 : B ≤ ‖DirichletCharacter.LFunction χ₃ 1‖ :=
        le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
      linarith
    have hLBpos : 0 < LB := by linarith
    set u : ℝ := (q : ℝ) ^ (δ / 2) with hudef
    set v : ℝ := (q : ℝ) ^ (-δ) with hvdef
    have hvpos : 0 < v := Real.rpow_pos_of_pos hq0 _
    have hu1 : (1 : ℝ) ≤ u := by
      rw [hudef]
      simpa using Real.rpow_le_rpow_of_exponent_le hq1 (by linarith : (0 : ℝ) ≤ δ / 2)
    have huv : (q : ℝ) ^ (-(δ / 2)) = u * v := by
      rw [hudef, hvdef, ← Real.rpow_add hq0]
      congr 1
      ring
    have hMsplit : (343 * (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ (-(δ / 4)) = K * (u * v) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by norm_num) (by positivity),
        sq_rpow δ (q₁ : ℝ) hq₁0.le, sq_rpow δ (q : ℝ) hq0.le, hKdef, huv]
    have hMlow : (343 * (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ (-(δ / 4))
        ≤ (343 * (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ (-(3 * (1 - β))) :=
      Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
    have hABbound : A * B ≤ 36 * LA * LB := by
      calc A * B ≤ (6 * LA) * B := mul_le_mul_of_nonneg_right hALA hBpos.le
        _ ≤ (6 * LA) * (6 * LB) := mul_le_mul_of_nonneg_left hBLB (by linarith)
        _ = 36 * LA * LB := by ring
    have hlogq : Real.log (q : ℝ) ≤ (2 / δ) * u := by
      rw [hudef]; exact log_le_rpow δ hδ (q : ℝ) hq0
    have hLBsplit : LB = LA + Real.log (q : ℝ) := by
      rw [hLBdef, hLAdef, Real.log_mul (ne_of_gt hq₁0) (ne_of_gt hq0)]
    have hLBbound : LB ≤ (LA + 2 / δ) * u := by
      rw [hLBsplit]
      have h1 : LA ≤ LA * u := le_mul_of_one_le_right hLA.le hu1
      nlinarith [hlogq]
    set D : ℝ := 36 * LA * (LA + 2 / δ) * u with hDdef
    have hDpos : 0 < D := by
      rw [hDdef]
      exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    have hDge : 36 * LA * LB ≤ D := by
      rw [hDdef]
      nlinarith [hLBbound, hLA]
    have hchain : (2 * CA * v) * D ≤ X * D := by
      have hE : (2 * CA * v) * D = 1 / 4 * (1 - β) * (K * (u * v)) := by
        rw [hCAdef, hDdef]
        field_simp
        ring
      rw [hE]
      calc 1 / 4 * (1 - β) * (K * (u * v))
          ≤ 1 / 4 * (1 - β) * ((343 * (q₁ : ℝ) ^ 2 * (q : ℝ) ^ 2) ^ (-(3 * (1 - β)))) := by
            rw [← hMsplit]
            exact mul_le_mul_of_nonneg_left hMlow (by positivity)
        _ ≤ A * X * B := hest
        _ = (A * B) * X := by ring
        _ ≤ (36 * LA * LB) * X := mul_le_mul_of_nonneg_right hABbound hXpos.le
        _ ≤ D * X := mul_le_mul_of_nonneg_right hDge hXpos.le
        _ = X * D := by ring
    have h2CA : 2 * CA * v ≤ X := le_of_mul_le_mul_right hchain hDpos
    have hCv : 0 < CA * v := mul_pos hCApos hvpos
    calc min CA (A * (q₁ : ℝ) ^ δ / 2) * v ≤ CA * v :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hvpos.le
      _ < X := by linarith

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_siegel_of_no_exceptional
namespace SWPort
/-! Ported from prove2.me: `Davenport.siegel_of_no_exceptional` (6ffd846d-e7f8-4840-b219-0b6e509699d2, statement by tianyipeng); proof = accepted sketch submission f8e5bf79-0f89-431a-b1ab-b79e6f6272e8 by tianyipeng. -/





open Complex ComplexOrder DirichletCharacter ArithmeticFunction

set_option maxHeartbeats 1000000

/-- The Dirichlet coefficients of `ζ(s)L(s,χ)` for a quadratic character `χ` form a
nonnegative real sequence with first coefficient `1`. -/
private lemma zeta_mul_LFunction_coeffs {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsQuadratic) :
    ∃ r : ℕ → ℝ, r 1 = 1 ∧ (∀ n, 0 ≤ r n) ∧
      (∀ s : ℂ, 1 < s.re → LSeriesSummable (fun n => (r n : ℂ)) s) ∧
      ∀ s : ℂ, 1 < s.re →
        riemannZeta s * DirichletCharacter.LFunction χ s
          = LSeries (fun n => (r n : ℂ)) s := by
  have hsq : χ ^ 2 = 1 := hχ.sq_eq_one
  have hnn : ∀ n : ℕ, (0 : ℂ) ≤ χ.zetaMul n := zetaMul_nonneg hsq
  have hcast : ∀ n : ℕ, (((χ.zetaMul n).re : ℝ) : ℂ) = χ.zetaMul n := by
    intro n
    have h := hnn n
    rw [Complex.le_def] at h
    refine Complex.ext (by simp) ?_
    simpa using h.2
  refine ⟨fun n => (χ.zetaMul n).re, ?_, ?_, ?_, ?_⟩
  · show (χ.zetaMul 1).re = 1
    rw [χ.isMultiplicative_zetaMul.map_one]; simp
  · intro n
    have h := hnn n
    rw [Complex.le_def] at h
    simpa using h.1
  · intro s hs
    exact (LSeriesSummable_congr s (fun {n} _ => hcast n)).mpr (χ.LSeriesSummable_zetaMul hs)
  · intro s hs
    have hz : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)) s :=
      LSeriesSummable_zeta_iff.mpr hs
    have hc : LSeriesSummable
        (fun n => ((_root_.toArithmeticFunction (fun m => χ m)) n)) s :=
      (LSeriesSummable_congr _ fun h => (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr <|
        ZMod.LSeriesSummable_of_one_lt_re χ hs
    have hsplit : LSeries (fun n => (χ.zetaMul n)) s
        = LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)) s
          * LSeries (fun n => ((_root_.toArithmeticFunction (fun m => χ m)) n)) s :=
      ArithmeticFunction.LSeries_mul' hz hc
    have hzeta : LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) n)) s
        = riemannZeta s := LSeries_zeta_eq_riemannZeta hs
    have hL : LSeries (fun n => ((_root_.toArithmeticFunction (fun m => χ m)) n)) s
        = DirichletCharacter.LFunction χ s := by
      rw [χ.LFunction_eq_LSeries hs]
      exact LSeries_congr (fun {n} hn => (χ.apply_eq_toArithmeticFunction_apply hn).symm) s
    rw [← hzeta, ← hL, ← hsplit]
    exact LSeries_congr (fun {n} _ => (hcast n).symm) s

theorem _root_.SWPort.Davenport.siegel_of_no_exceptional (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 20)
    (hno : ∀ (q₁ : ℕ) [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁),
      χ₁.IsQuadratic → χ₁ ≠ 1 → χ₁.IsPrimitive →
        ∀ β : ℝ, 1 - δ / 12 ≤ β → β < 1 → DirichletCharacter.LFunction χ₁ β ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsQuadratic → χ ≠ 1 → χ.IsPrimitive →
          C * (q : ℝ) ^ (-δ) < (DirichletCharacter.LFunction χ 1).re := by
  have hσ1 : (1 : ℝ) - δ / 12 < 1 := by linarith
  have hσ19 : (19 : ℝ) / 20 ≤ 1 - δ / 12 := by linarith
  refine ⟨(δ / 48) * (7 : ℝ) ^ (-(δ / 4)) / 2, by positivity, ?_⟩
  intro q _ χ hquad hne hprim
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : (0 : ℝ) < (q : ℝ) := lt_of_lt_of_le zero_lt_one hq1
  have hL1 : 0 < (DirichletCharacter.LFunction χ 1).re :=
    Davenport.LFunction_one_pos q χ hquad hne
  have him : ∀ t : ℝ, (DirichletCharacter.LFunction χ (t : ℂ)).im = 0 :=
    fun t => Davenport.LFunction_ofReal_im_eq_zero q χ hquad hne t
  -- `L(σ, χ) > 0` at `σ = 1 - δ/12`, by the intermediate value theorem on `[σ, 1]`.
  have hgσ : 0 < (DirichletCharacter.LFunction χ ((1 - δ / 12 : ℝ) : ℂ)).re := by
    by_contra hcon
    push_neg at hcon
    have hcont : ContinuousOn (fun t : ℝ => (DirichletCharacter.LFunction χ (t : ℂ)).re)
        (Set.Icc (1 - δ / 12) 1) :=
      (Complex.continuous_re.comp
        ((differentiable_LFunction hne).continuous.comp Complex.continuous_ofReal)).continuousOn
    have hmem : (0 : ℝ) ∈
        Set.Icc ((fun t : ℝ => (DirichletCharacter.LFunction χ (t : ℂ)).re) (1 - δ / 12))
          ((fun t : ℝ => (DirichletCharacter.LFunction χ (t : ℂ)).re) 1) :=
      ⟨hcon, by simpa using hL1.le⟩
    obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hσ1.le hcont hmem
    have hzero : DirichletCharacter.LFunction χ (t : ℂ) = 0 :=
      Complex.ext (by simpa using hgt) (by simpa using him t)
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact hno q χ hquad hne hprim t ht.1 hlt hzero
    · rw [heq, Complex.ofReal_one] at hzero
      rw [hzero] at hL1
      simp at hL1
  obtain ⟨r, hr1, hrnn, hrsum, hrid⟩ := zeta_mul_LFunction_coeffs χ hquad
  have hM1 : (1 : ℝ) ≤ 7 * (q : ℝ) := by nlinarith
  have hball : ∀ s ∈ Metric.closedBall (2 : ℂ) (3 / 2),
      ‖DirichletCharacter.LFunction χ s‖ ≤ 7 * (q : ℝ) := by
    intro s hs
    rw [mem_closedBall_iff_norm] at hs
    have hre : (1 : ℝ) / 2 ≤ s.re := by
      have h := (abs_le.mp ((Complex.abs_re_le_norm (s - 2)).trans hs)).1
      simp only [Complex.sub_re, Complex.re_ofNat] at h
      linarith
    have hnorm : ‖s‖ ≤ 7 / 2 := by
      have : ‖s‖ ≤ ‖s - 2‖ + ‖(2 : ℂ)‖ := by
        simpa using norm_add_le (s - 2) (2 : ℂ)
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2] at this
      linarith
    have hb := Davenport.norm_LFunction_le_of_re_pos q χ hne s (by linarith)
    refine hb.trans ?_
    rw [div_le_iff₀ (by linarith : (0:ℝ) < s.re)]
    nlinarith [hq0.le, norm_nonneg s]
  have hest := Davenport.estermann_lemma (DirichletCharacter.LFunction χ) (7 * (q : ℝ)) r hM1
    ((differentiable_LFunction hne).differentiableOn) hball hrsum hrid hr1 hrnn
    (1 - δ / 12) hσ19 hσ1 hgσ.le
  have h1σ : (1 : ℝ) - (1 - δ / 12) = δ / 12 := by ring
  rw [h1σ] at hest
  have hMr : (7 * (q : ℝ)) ^ (-(3 * (δ / 12))) = (7 : ℝ) ^ (-(δ / 4)) * (q : ℝ) ^ (-(δ / 4)) := by
    rw [show -(3 * (δ / 12)) = -(δ / 4) by ring]
    exact Real.mul_rpow (by norm_num) hq0.le
  rw [hMr] at hest
  have hqq : (q : ℝ) ^ (-δ) ≤ (q : ℝ) ^ (-(δ / 4)) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  have hqpos : (0 : ℝ) < (q : ℝ) ^ (-δ) := Real.rpow_pos_of_pos hq0 _
  have hApos : (0 : ℝ) < (δ / 48) * (7 : ℝ) ^ (-(δ / 4)) := by positivity
  have key : (δ / 48) * (7 : ℝ) ^ (-(δ / 4)) * (q : ℝ) ^ (-δ)
      ≤ (DirichletCharacter.LFunction χ 1).re := by
    refine le_trans ?_ hest
    calc (δ / 48) * (7 : ℝ) ^ (-(δ / 4)) * (q : ℝ) ^ (-δ)
        ≤ (δ / 48) * (7 : ℝ) ^ (-(δ / 4)) * (q : ℝ) ^ (-(δ / 4)) :=
          mul_le_mul_of_nonneg_left hqq hApos.le
      _ = 1 / 4 * (δ / 12) * ((7 : ℝ) ^ (-(δ / 4)) * (q : ℝ) ^ (-(δ / 4))) := by ring
  have hstrict : (δ / 48) * (7 : ℝ) ^ (-(δ / 4)) / 2 * (q : ℝ) ^ (-δ)
      < (δ / 48) * (7 : ℝ) ^ (-(δ / 4)) * (q : ℝ) ^ (-δ) :=
    mul_lt_mul_of_pos_right (by linarith) hqpos
  linarith

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_siegel
namespace SWPort
/-! Ported from prove2.me: `Davenport.siegel` (822772bb-e8fb-4e21-83b1-3ecd7959a5ba, statement by alya); proof = accepted sketch submission 09175ffe-a224-4b95-a440-d08065e5a894 by tianyipeng. -/




open Davenport

theorem _root_.SWPort.Davenport.siegel (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsQuadratic → χ ≠ 1 → χ.IsPrimitive →
          C * (q : ℝ) ^ (-ε) < (DirichletCharacter.LFunction χ 1).re := by
  classical
  -- it suffices to prove the bound for the smaller exponent `δ = min ε (1/20)`
  set δ : ℝ := min ε (1 / 20) with hδdef
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδ' : δ ≤ 1 / 20 := min_le_right _ _
  have hδε : δ ≤ ε := min_le_left _ _
  have key : ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsQuadratic → χ ≠ 1 → χ.IsPrimitive →
          C * (q : ℝ) ^ (-δ) < (DirichletCharacter.LFunction χ 1).re := by
    by_cases hP : ∃ (q₁ : ℕ) (_ : NeZero q₁) (χ₁ : DirichletCharacter ℂ q₁),
        χ₁.IsQuadratic ∧ χ₁ ≠ 1 ∧ χ₁.IsPrimitive ∧
          ∃ β : ℝ, 19 / 20 ≤ β ∧ β < 1 ∧ DirichletCharacter.LFunction χ₁ β = 0 ∧
            1 - β ≤ δ / 12
    · obtain ⟨q₁, hq₁ne, χ₁, hq, hn, hp, β, hβ, hβ₁, hzero, hclose⟩ := hP
      exact siegel_of_exceptional δ hδ hδ' q₁ χ₁ hq hn hp β hβ hβ₁ hzero hclose
    · refine siegel_of_no_exceptional δ hδ hδ' ?_
      intro q₁ _ χ₁ hq hn hp β hβlow hβ₁ hzero
      exact hP ⟨q₁, ‹NeZero q₁›, χ₁, hq, hn, hp, β, by
        have : (1:ℝ) - δ / 12 ≤ β := hβlow
        have hd : δ / 12 ≤ 1 / 240 := by
          have : δ ≤ 1 / 20 := hδ'
          linarith
        linarith, hβ₁, hzero, by linarith⟩
  -- transfer from `δ` to `ε`
  obtain ⟨C, hC, hbound⟩ := key
  refine ⟨C, hC, ?_⟩
  intro q hq χ hquad hne hprim
  have hq1 : (1:ℝ) ≤ (q : ℝ) := by
    have : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    exact_mod_cast this
  have hmono : (q : ℝ) ^ (-ε) ≤ (q : ℝ) ^ (-δ) :=
    Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)
  calc C * (q : ℝ) ^ (-ε) ≤ C * (q : ℝ) ^ (-δ) := by
        exact mul_le_mul_of_nonneg_left hmono hC.le
    _ < (DirichletCharacter.LFunction χ 1).re := hbound q χ hquad hne hprim

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_siegel_zero
namespace SWPort
/-! Ported from prove2.me: `Davenport.siegel_zero` (93f232fb-3b80-4868-a4ce-95e1194e5e22, statement by alya); proof = accepted sketch submission d5e989ba-7e0e-4db1-b291-3d73dd5b9984 by alya. -/











open Finset DirichletCharacter Vino

/-- Modulo `q ≤ 2` the group of units of `ZMod q` is trivial, so the only Dirichlet
character is the principal one. -/
private lemma char_eq_one_of_le_two (q : ℕ) [NeZero q] (hq : q ≤ 2)
    (χ : DirichletCharacter ℂ q) : χ = 1 := by
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hcard : Fintype.card (ZMod q)ˣ = 1 := by
    rw [ZMod.card_units_eq_totient q]
    interval_cases q <;> decide
  have hsub : Subsingleton (ZMod q)ˣ := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  rw [MulChar.eq_one_iff]
  intro a
  rw [Subsingleton.elim a 1]
  simp

theorem _root_.SWPort.Davenport.siegel_zero_oai (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsQuadratic → χ ≠ 1 → χ.IsPrimitive →
          ∀ σ : ℝ, 1 - C * (q : ℝ) ^ (-ε) < σ →
            DirichletCharacter.LFunction χ (σ : ℂ) ≠ 0 := by
  obtain ⟨C₁, hC₁, hsieg⟩ := Davenport.siegel (ε / 2) (by linarith)
  obtain ⟨K, hK, hder⟩ := Davenport.deriv_LFunction_bound
  have hδ : (0 : ℝ) < ε / 4 := by linarith
  set C : ℝ := min ε (C₁ * (ε / 4) ^ 2 / K) with hCdef
  have hCpos : 0 < C := lt_min hε (by positivity)
  have hCε : C ≤ ε := min_le_left _ _
  have hCK : C * K ≤ C₁ * (ε / 4) ^ 2 := by
    have h : C ≤ C₁ * (ε / 4) ^ 2 / K := min_le_right _ _
    have := mul_le_mul_of_nonneg_right h hK.le
    calc C * K ≤ C₁ * (ε / 4) ^ 2 / K * K := this
      _ = C₁ * (ε / 4) ^ 2 := by field_simp
  refine ⟨C, hCpos, ?_⟩
  intro q _ χ hquad hne hprim σ hσ
  -- Small moduli: for `q ≤ 2` there is no non-principal character at all.
  rcases lt_or_ge q 3 with hq3 | hq3
  · exact absurd (char_eq_one_of_le_two q (by omega) χ) hne
  have hq1R : (1 : ℝ) < (q : ℝ) := by
    have : (3 : ℕ) ≤ q := hq3
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast this
    linarith
  have hq0R : (0 : ℝ) < (q : ℝ) := by linarith
  have hlog : 0 < Real.log q := Real.log_pos hq1R
  -- On the closed half plane `re s ≥ 1` the L-function of a non-principal character
  -- does not vanish (Mathlib).
  rcases le_or_gt 1 σ with hσ1 | hσ1
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) (by simpa using hσ1)
  -- The remaining case: a real zero `σ < 1` inside the interval.
  intro h0
  have hAf : (0 : ℝ) < (q : ℝ) ^ ε := Real.rpow_pos_of_pos hq0R ε
  have hnegeps : (q : ℝ) ^ (-ε) = ((q : ℝ) ^ ε)⁻¹ := Real.rpow_neg hq0R.le ε
  -- Step 1: `C * q ^ (-ε) ≤ 1 / log q`, so the zero lies in the range of the derivative bound.
  have hlogbnd : ε * Real.log q ≤ (q : ℝ) ^ ε := by
    have h := Real.log_natCast_le_rpow_div q hε
    rw [le_div_iff₀ hε] at h
    linarith
  have hrangeC : C * (q : ℝ) ^ (-ε) ≤ 1 / Real.log q := by
    rw [hnegeps, le_div_iff₀ hlog]
    have hrw : C * ((q : ℝ) ^ ε)⁻¹ * Real.log q = C * Real.log q / (q : ℝ) ^ ε := by
      field_simp
    rw [hrw, div_le_one hAf]
    nlinarith [mul_nonneg (sub_nonneg.mpr hCε) hlog.le]
  have hrange : 1 - 1 / Real.log q ≤ σ := by linarith
  -- Step 2: mean value theorem for the real function `x ↦ Re L(x, χ)` on `[σ, 1]`.
  have hderivat : ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => (DirichletCharacter.LFunction χ (y : ℂ)).re)
        ((deriv (DirichletCharacter.LFunction χ) (x : ℂ)).re) x := fun x =>
    ((DirichletCharacter.differentiable_LFunction hne (x : ℂ)).hasDerivAt).real_of_complex
  obtain ⟨c, hcmem, hcslope⟩ :=
    exists_hasDerivAt_eq_slope
      (fun x : ℝ => (DirichletCharacter.LFunction χ (x : ℂ)).re)
      (fun x : ℝ => (deriv (DirichletCharacter.LFunction χ) (x : ℂ)).re) hσ1
      (fun x _ => (hderivat x).continuousAt.continuousWithinAt)
      (fun x _ => hderivat x)
  simp only [Complex.ofReal_one, h0, Complex.zero_re, sub_zero] at hcslope
  have hσ1' : (0 : ℝ) < 1 - σ := by linarith
  have hL1 : (DirichletCharacter.LFunction χ 1).re
      = (1 - σ) * (deriv (DirichletCharacter.LFunction χ) (c : ℂ)).re := by
    rw [hcslope]
    field_simp
  -- Step 3: the derivative bound at the intermediate point.
  have hcrange1 : 1 - 1 / Real.log q ≤ c := le_trans hrange hcmem.1.le
  have hcrange2 : c ≤ 1 := hcmem.2.le
  have hdbound := hder q χ hne hq3 c hcrange1 hcrange2
  have hre : (deriv (DirichletCharacter.LFunction χ) (c : ℂ)).re ≤ K * Real.log q ^ 2 :=
    le_trans (Complex.re_le_norm _) hdbound
  have hupper : (DirichletCharacter.LFunction χ 1).re ≤ (1 - σ) * (K * Real.log q ^ 2) := by
    rw [hL1]
    exact mul_le_mul_of_nonneg_left hre hσ1'.le
  -- Step 4: turn the interval length into a power saving.
  have hKlog : (0 : ℝ) < K * Real.log q ^ 2 := by positivity
  have h1mσ : 1 - σ < C * (q : ℝ) ^ (-ε) := by linarith
  have hstep1 : (1 - σ) * (K * Real.log q ^ 2)
      < C * (q : ℝ) ^ (-ε) * (K * Real.log q ^ 2) := mul_lt_mul_of_pos_right h1mσ hKlog
  have hsq : ((q : ℝ) ^ (ε / 4)) ^ 2 = (q : ℝ) ^ (ε / 2) := by
    rw [sq, ← Real.rpow_add hq0R]
    congr 1
    ring
  have hlog2 : Real.log q ^ 2 ≤ (q : ℝ) ^ (ε / 2) / (ε / 4) ^ 2 := by
    have h := Real.log_natCast_le_rpow_div q hδ
    rw [le_div_iff₀ hδ] at h
    have h2 : Real.log q * (ε / 4) * (Real.log q * (ε / 4))
        ≤ (q : ℝ) ^ (ε / 4) * (q : ℝ) ^ (ε / 4) :=
      mul_self_le_mul_self (mul_nonneg hlog.le (by linarith)) h
    rw [le_div_iff₀ (by positivity), ← hsq]
    nlinarith [h2]
  have hpow : (q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2) = (q : ℝ) ^ (-(ε / 2)) := by
    rw [← Real.rpow_add hq0R]
    congr 1
    ring
  have hnegpos : (0 : ℝ) < (q : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hq0R _
  have hstep2 : C * (q : ℝ) ^ (-ε) * (K * Real.log q ^ 2) ≤ C₁ * (q : ℝ) ^ (-(ε / 2)) := by
    calc C * (q : ℝ) ^ (-ε) * (K * Real.log q ^ 2)
        ≤ C * (q : ℝ) ^ (-ε) * (K * ((q : ℝ) ^ (ε / 2) / (ε / 4) ^ 2)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog2 hK.le) (by positivity)
      _ = C * K / (ε / 4) ^ 2 * ((q : ℝ) ^ (-ε) * (q : ℝ) ^ (ε / 2)) := by ring
      _ = C * K / (ε / 4) ^ 2 * (q : ℝ) ^ (-(ε / 2)) := by rw [hpow]
      _ ≤ C₁ * (q : ℝ) ^ (-(ε / 2)) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_pos_of_pos hq0R _).le
          rw [div_le_iff₀ (by positivity)]
          linarith
  -- Step 5: contradiction with Siegel's lower bound for `L(1, χ)`.
  have hsiegq := hsieg q χ hquad hne hprim
  linarith

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.siegel_zero_oai := @SWPort.Davenport.siegel_zero_oai
