-- Prove2me | solution 1 for SWPort.Davenport.logDeriv_LFunction_partial_fraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:24:49.409683+00:00
-- url     : https://prove2.me/submissions/ba063564-f13a-4dfd-b3ff-ce452ed8dd4b

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001

section
-- module Solutions.Artin.SW.Thm.Zeta23_WeilEF_logDeriv_partial_fraction_disk
alias SWPort.Zeta23.WeilEF.logDeriv_partial_fraction_disk := SWPort.Z.Zeta23.WeilEF.logDeriv_partial_fraction_disk
end

section
-- module Solutions.Artin.SW.Thm.Davenport_logDeriv_LFunction_partial_fraction
namespace SWPort
/-! Ported from prove2.me: `Davenport.logDeriv_LFunction_partial_fraction` (4953c8b0-1e84-4fc0-bbdf-aa2bf1843a47, statement by alya); proof = accepted sketch submission 318189c3-ca52-46c8-9f38-395a68078ec1 by alya. -/
























open Finset MeasureTheory Set Complex Filter Topology Asymptotics

set_option linter.unusedSectionVars false

/-!
# Partial fractions for `L'/L(s, χ)` near the line `Re s = 2` (Davenport §16, local form)

For a non-principal character `χ (mod q)` and `1 < Re s ≤ 2` we prove
`-Re (L'/L)(s, χ) ≤ c log (q (|Im s| + 2)) - ∑_{ρ ∈ Z} Re 1/(s - ρ)`
for every multiset `Z` of zeros of `L(·, χ)` in the disc `|ρ - s| ≤ 1/2`, counted with at most
their multiplicity.

The proof is the local (Borel–Carathéodory) route: the platform theorem
`Zeta23.WeilEF.logDeriv_partial_fraction_disk` gives, for an analytic function `f` on a disc
`|z - s₀| ≤ R` with `f(s₀) ≠ 0` and `|f| ≤ B |f(s₀)|` on the disc of radius `(24/25) R`,
a partial-fraction expansion of `f'/f` on the disc of radius `(83/100) R` up to an error
`≪ (log B) / R`, the sum running over the zeros in the disc of radius `(22/25) R`.

We apply it with `f = L(·, χ)`, `s₀ = 2 + i t` (`t = Im s`), `R = 2`. The two analytic inputs are
* the growth bound `|L(z, χ)| ≤ q |z| / Re z` for `Re z > 0`, from the Abel-summation
  (Mellin) representation `L(z, χ) = z ∫_1^∞ S(x) x^{-z-1} dx` with `|S(x)| ≤ q`;
* the lower bound `|L(2 + i t, χ)| ≥ 1/3` from the Dirichlet series.
-/

namespace DavenportPF

/-! ### Partial sums of a Dirichlet character (from `Sol_Davenport_deriv_LFunction_bound`) -/

variable {q : ℕ} [NeZero q]

private lemma sum_range_eq_sum_zmod (f : ZMod q → ℂ) :
    ∑ j ∈ Finset.range q, f (j : ZMod q) = ∑ a : ZMod q, f a := by
  refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod q)) (j := fun a => a.val)
    ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
  · intro a _; exact ZMod.natCast_rightInverse a
  · intro a _; rfl

private lemma sum_block_eq_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q) = 0 := by
  calc ∑ j ∈ Finset.range q, χ ((m + j : ℕ) : ZMod q)
      = ∑ j ∈ Finset.range q, (fun a : ZMod q => χ ((m : ZMod q) + a)) (j : ZMod q) :=
        Finset.sum_congr rfl (fun j _ => by push_cast; rfl)
    _ = ∑ a : ZMod q, χ ((m : ZMod q) + a) :=
        sum_range_eq_sum_zmod (fun a : ZMod q => χ ((m : ZMod q) + a))
    _ = ∑ a : ZMod q, χ a :=
        Fintype.sum_equiv (Equiv.addLeft ((m : ZMod q))) _ _ (fun a => rfl)
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

private lemma norm_sum_range_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
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
        exact sum_block_eq_zero χ hχ m
      rw [← hsplit, hzero, add_zero]
      exact ih m hmn

private lemma norm_G_le_q (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) (t : ℝ) :
    ‖G χ t‖ ≤ q := by
  have hnt : Nontrivial (ZMod q) := by
    haveI : Fact (1 < q) := ⟨by omega⟩
    infer_instance
  have hz : χ (0 : ZMod q) = 0 := MulChar.map_zero χ
  have : G χ t = ∑ k ∈ Finset.range (⌊t⌋₊ + 1), χ (k : ZMod q) := by
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
  exact norm_sum_range_le χ hχ _

private lemma G_eq_zero (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : t < 1) : G χ t = 0 := by
  have : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr ht
  simp [G, this]

/-! ### The Mellin representation -/

private lemma locallyIntegrable_G (χ : DirichletCharacter ℂ q) :
    LocallyIntegrableOn (G χ) (Ioi (0 : ℝ)) := by
  have h1 : LocallyIntegrableOn (fun _ : ℝ => (1 : ℂ)) (Set.Ici (0 : ℝ)) :=
    (continuous_const.continuousOn).locallyIntegrableOn measurableSet_Ici
  have h2 := locallyIntegrableOn_mul_sum_Icc (𝕜 := ℂ) (fun k : ℕ => (χ k : ℂ)) (m := 1) (a := 0)
    le_rfl h1
  simp only [one_mul] at h2
  exact h2.mono_set Ioi_subset_Ici_self

private lemma isBigO_G_top (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) :
    (G χ) =O[atTop] (fun t : ℝ => t ^ (-(0 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun t => ?_))
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_G_le_q χ hχ hq t

private lemma isBigO_G_bot (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (G χ) =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ (-b)) := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  simp [G_eq_zero χ ht.2]

private lemma mellinConv_G (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : MellinConvergent (G χ) (-s) := by
  refine mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G χ) (isBigO_G_top χ hχ hq) ?_ (isBigO_G_bot χ _) ?_
  · simpa using hs
  · simp

private lemma mellin_hasDeriv (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    MellinConvergent (fun t => Real.log t • G χ t) (-s) ∧
      HasDerivAt (mellin (G χ)) (mellin (fun t => Real.log t • G χ t) (-s)) (-s) := by
  refine mellin_hasDerivAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    (locallyIntegrable_G χ) (isBigO_G_top χ hχ hq) ?_ (isBigO_G_bot χ _) ?_
  · simpa using hs
  · simp

private lemma hasDerivAt_F (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) :
    HasDerivAt (F χ)
      (mellin (G χ) (-s) - s * mellin (fun t => Real.log t • G χ t) (-s)) s := by
  have h := (mellin_hasDeriv χ hχ hq hs).2
  have h2 : HasDerivAt (fun z : ℂ => mellin (G χ) (-z))
      (mellin (fun t => Real.log t • G χ t) (-s) * (-1)) s :=
    h.comp s ((hasDerivAt_id s).neg)
  have h4 := (hasDerivAt_id s).mul h2
  have heq : (1 : ℂ) * mellin (G χ) (-s)
      + s * (mellin (fun t => Real.log t • G χ t) (-s) * (-1))
      = mellin (G χ) (-s) - s * mellin (fun t => Real.log t • G χ t) (-s) := by ring
  simp only [id] at h4
  rw [heq] at h4
  exact h4

private lemma mellin_eq_integral_Ioi_one (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h : MellinConvergent (G χ) s) :
    mellin (G χ) s = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G χ t := by
  have hz : ∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G χ t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    rw [G_eq_zero χ ht.2, smul_zero]
  calc mellin (G χ) s = ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • G χ t := rfl
    _ = (∫ t in Ioc (0 : ℝ) 1, (t : ℂ) ^ (s - 1) • G χ t)
          + ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G χ t := by
        rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
        exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (h.mono_set Ioc_subset_Ioi_self) (h.mono_set (Ioi_subset_Ioi zero_le_one))
    _ = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (s - 1) • G χ t := by rw [hz, zero_add]

private lemma LFunction_eq_F_of_one_lt (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 1 < s.re) : DirichletCharacter.LFunction χ s = F χ s := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (0 : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (q : ℝ) (Eventually.of_forall (fun n => ?_))
    simp only [Real.rpow_zero, norm_one, mul_one]
    have : (∑ k ∈ Finset.Icc 1 n, (χ k : ℂ)) = G χ (n : ℝ) := by
      simp [G, Nat.floor_natCast]
    rw [this]
    exact norm_G_le_q χ hχ hq _
  have hmain := LSeries_eq_mul_integral (fun n : ℕ => (χ n : ℂ)) (r := 0) le_rfl
    (by linarith : (0 : ℝ) < s.re) (DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs) hO
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, hmain]
  have hconv : MellinConvergent (G χ) (-s) := mellinConv_G χ hχ hq (by linarith)
  rw [F, mellin_eq_integral_Ioi_one χ hconv]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [smul_eq_mul, G]
  rw [mul_comm]
  congr 2
  ring

/-! ### Analytic continuation via the identity theorem -/

private lemma LFunction_eq_F (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q)
    {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.LFunction χ s = F χ s := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hUconn : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have hLan : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) U :=
    (DirichletCharacter.differentiable_LFunction hχ).differentiableOn.analyticOnNhd hUopen
  have hFan : AnalyticOnNhd ℂ (F χ) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact ((hasDerivAt_F χ hχ hq hz).differentiableAt).differentiableWithinAt
  have hmem : (2 : ℂ) ∈ U := by simp [hU]
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 (2 : ℂ)] F χ := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
    exact LFunction_eq_F_of_one_lt χ hχ hq hz
  have heqOn : EqOn (DirichletCharacter.LFunction χ) (F χ) U :=
    hLan.eqOn_of_preconnected_of_eventuallyEq hFan hUconn hmem hev
  exact heqOn hs

/-! ### The growth bound `‖L(z, χ)‖ ≤ q ‖z‖ / Re z` -/

private lemma norm_mellin_le (f : ℝ → ℂ) (x : ℂ) :
    ‖mellin f x‖ ≤ ∫ t in Ioi (0 : ℝ), t ^ (x.re - 1) * ‖f t‖ := by
  rw [mellin]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

private lemma norm_mellin_G_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : ‖mellin (G χ) (-s)‖ ≤ q / s.re := by
  have hlt : (-s.re - 1 : ℝ) < -1 := by linarith
  set u : ℝ → ℝ := fun t => t ^ (-s.re - 1) * ‖G χ t‖ with hu
  have hconv : MellinConvergent (G χ) (-s) := mellinConv_G χ hχ hq hs
  have hIA : IntegrableOn u (Ioi (0 : ℝ)) := by
    refine MeasureTheory.IntegrableOn.congr_fun (MeasureTheory.Integrable.norm hconv)
      (fun t ht => ?_) measurableSet_Ioi
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
    simp [hu]
  have hstep1 : ‖mellin (G χ) (-s)‖ ≤ ∫ t in Ioi (0 : ℝ), u t := by
    have := norm_mellin_le (G χ) (-s)
    simpa [hu] using this
  have hsplit : ∫ t in Ioi (0 : ℝ), u t
      = (∫ t in Ioc (0 : ℝ) 1, u t) + ∫ t in Ioi (1 : ℝ), u t := by
    rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hIA.mono_set Ioc_subset_Ioi_self) (hIA.mono_set (Ioi_subset_Ioi zero_le_one))
  have hp1 : ∫ t in Ioc (0 : ℝ) 1, u t = 0 := by
    rw [integral_Ioc_eq_integral_Ioo]
    refine setIntegral_eq_zero_of_forall_eq_zero (fun t ht => ?_)
    simp [hu, G_eq_zero χ ht.2]
  have hp2 : ∫ t in Ioi (1 : ℝ), u t ≤ q / s.re := by
    have hmaj : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_rpow_of_lt hlt one_pos).const_mul _
    have hstep : ∫ t in Ioi (1 : ℝ), u t ≤ ∫ t in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) := by
      refine setIntegral_mono_on (hIA.mono_set (Ioi_subset_Ioi zero_le_one)) hmaj
        measurableSet_Ioi (fun t ht => ?_)
      have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
      have hG : ‖G χ t‖ ≤ (q : ℝ) := norm_G_le_q χ hχ hq t
      calc u t ≤ t ^ (-s.re - 1) * (q : ℝ) :=
            mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg ht0.le _)
        _ = (q : ℝ) * t ^ (-s.re - 1) := by ring
    have hval : ∫ t in Ioi (1 : ℝ), (q : ℝ) * t ^ (-s.re - 1) = (q : ℝ) / s.re := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hlt one_pos,
        show (-s.re - 1 + 1 : ℝ) = -s.re by ring, Real.one_rpow]
      field_simp
    rw [hval] at hstep
    exact hstep
  rw [hsplit, hp1, zero_add] at hstep1
  linarith

/-- The growth bound: `‖L(z, χ)‖ ≤ q ‖z‖ / Re z` for `Re z > 0`. -/
private lemma norm_LFunction_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hq : 2 ≤ q) {s : ℂ}
    (hs : 0 < s.re) : ‖DirichletCharacter.LFunction χ s‖ ≤ ‖s‖ * q / s.re := by
  rw [LFunction_eq_F χ hχ hq hs, F, norm_mul]
  have := norm_mellin_G_le χ hχ hq hs
  calc ‖s‖ * ‖mellin (G χ) (-s)‖ ≤ ‖s‖ * (q / s.re) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ‖s‖ * q / s.re := by ring

/-! ### The lower bound `‖L(2 + i t, χ)‖ ≥ 1/3` -/

private lemma tsum_inv_sq_tail_le : ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 ≤ 2 / 3 := by
  have hs : HasSum (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 6) := hasSum_zeta_two
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hs.summable
  have h := hsum.sum_add_tsum_nat_add 2
  rw [hs.tsum_eq] at h
  have h2 : ∑ i ∈ Finset.range 2, (1 : ℝ) / (i : ℝ) ^ 2 = 1 := by
    simp [Finset.sum_range_succ]
  rw [h2] at h
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have : Real.pi ^ 2 < 3.15 ^ 2 := by nlinarith
  have hfin : ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 6 - 1 := by
    have : (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2)
        = fun n : ℕ => (1 : ℝ) / (((n + 2 : ℕ) : ℕ) : ℝ) ^ 2 := rfl
    linarith
  rw [hfin]
  nlinarith

private lemma norm_LFunction_two_ge (χ : DirichletCharacter ℂ q) (t : ℝ) :
    1 / 3 ≤ ‖DirichletCharacter.LFunction χ (2 + t * I)‖ := by
  set s₀ : ℂ := 2 + t * I with hs₀
  have hre : s₀.re = 2 := by simp [hs₀]
  have hs : 1 < s₀.re := by rw [hre]; norm_num
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  have hsum : LSeriesSummable (fun n : ℕ => (χ n : ℂ)) s₀ :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  -- split off the first two terms
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have h01 : ∑ i ∈ Finset.range 2, LSeries.term (fun n : ℕ => (χ n : ℂ)) s₀ i = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, LSeries.term_zero,
      LSeries.term_of_ne_zero one_ne_zero]
    simp
  rw [h01] at hsplit
  unfold LSeries
  rw [← hsplit]
  -- bound the tail
  have hnorm : ∀ n : ℕ, ‖LSeries.term (fun n : ℕ => (χ n : ℂ)) s₀ (n + 2)‖
      ≤ (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 := by
    intro n
    rw [LSeries.norm_term_eq, if_neg (by omega), hre]
    have hn : (0 : ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
    rw [show ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) = ((n + 2 : ℕ) : ℝ) ^ 2 by
      rw [← Real.rpow_natCast]; norm_num]
    gcongr
    exact DirichletCharacter.norm_le_one χ _
  have htail_summable : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n : ℕ => (χ n : ℂ)) s₀ (n + 2)‖) :=
    ((summable_nat_add_iff 2).mpr hsum).norm
  have hinv_summable : Summable (fun n : ℕ => (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) := by
    have := (summable_nat_add_iff 2).mpr hasSum_zeta_two.summable
    exact this
  have htail : ‖∑' n : ℕ, LSeries.term (fun n : ℕ => (χ n : ℂ)) s₀ (n + 2)‖ ≤ 2 / 3 := by
    calc ‖∑' n : ℕ, LSeries.term (fun n : ℕ => (χ n : ℂ)) s₀ (n + 2)‖
        ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (χ n : ℂ)) s₀ (n + 2)‖ :=
          norm_tsum_le_tsum_norm htail_summable
      _ ≤ ∑' n : ℕ, (1 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 :=
          htail_summable.tsum_le_tsum hnorm hinv_summable
      _ ≤ 2 / 3 := tsum_inv_sq_tail_le
  have := norm_sub_norm_le (1 : ℂ) (-(∑' n : ℕ, LSeries.term (fun n : ℕ => (χ n : ℂ)) s₀ (n + 2)))
  rw [sub_neg_eq_add, norm_neg, norm_one] at this
  linarith

/-! ### Facts about zeros of `L(·, χ)` -/


/-- The core application of `Zeta23.WeilEF.logDeriv_partial_fraction_disk` to `L(·, χ)` on the disc
`|z - (2 + i t)| ≤ 2`, with `B = 100 q (|t| + 2)`. -/
private lemma core (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    ∃ Zf : Finset ℂ,
      (↑Zf = {ρ ∈ Metric.closedBall (2 + t * I) (22 / 25 * 2) |
                DirichletCharacter.LFunction χ ρ = 0}) ∧
      ((∑ ρ ∈ Zf, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
          ≤ 1 / Real.log ((24 / 25) / (22 / 25)) * Real.log (100 * ((q : ℝ) * (|t| + 2)))) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (83 / 100 * 2), DirichletCharacter.LFunction χ s ≠ 0 →
        ‖logDeriv (DirichletCharacter.LFunction χ) s
            - ∑ ρ ∈ Zf, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
          ≤ 44795000 / 2 * Real.log (100 * ((q : ℝ) * (|t| + 2))) := by
  have hq : 2 ≤ q := by
    by_contra h
    push Not at h
    have hq1 : q = 1 := by
      have := NeZero.ne q
      omega
    subst hq1
    exact hχ (DirichletCharacter.level_one χ)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  set f := DirichletCharacter.LFunction χ with hf
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀norm : ‖s₀‖ ≤ |t| + 2 := by
    calc ‖s₀‖ = ‖(2 : ℂ) + t * I‖ := rfl
      _ ≤ ‖(2 : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |t| := by simp
      _ = |t| + 2 := by ring
  have hX2 : (2 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
    have : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall s₀ 2) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hf0' : 1 / 3 ≤ ‖f s₀‖ := norm_LFunction_two_ge χ t
  have hf0 : f s₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hf0'; norm_num at hf0'
  set B : ℝ := 100 * ((q : ℝ) * (|t| + 2)) with hB
  have hB2 : 2 ≤ B := by rw [hB]; linarith
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24 / 25 * 2), ‖f w‖ ≤ B * ‖f s₀‖ := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have hre : 2 / 25 ≤ w.re := by
      have h1 : |(w - s₀).re| ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re, hs₀re] at h1
      have := (abs_le.mp h1).1
      linarith
    have hwpos : 0 < w.re := by linarith
    have hwnorm : ‖w‖ ≤ 2 * (|t| + 2) := by
      calc ‖w‖ = ‖(w - s₀) + s₀‖ := by ring_nf
        _ ≤ ‖w - s₀‖ + ‖s₀‖ := norm_add_le _ _
        _ ≤ 24 / 25 * 2 + (|t| + 2) := by linarith
        _ ≤ 2 * (|t| + 2) := by linarith [abs_nonneg t]
    have hgrow : ‖f w‖ ≤ ‖w‖ * q / w.re := norm_LFunction_le χ hχ hq hwpos
    have hq0 : (0 : ℝ) < q := by linarith
    calc ‖f w‖ ≤ ‖w‖ * q / w.re := hgrow
      _ ≤ (2 * (|t| + 2)) * q / (2 / 25) := by
          gcongr
      _ = 25 * ((q : ℝ) * (|t| + 2)) := by ring
      _ = B * (1 / 3) * (3 / 4) := by rw [hB]; ring
      _ ≤ B * ‖f s₀‖ * (3 / 4) := by gcongr
      _ ≤ B * ‖f s₀‖ := by
          have : 0 ≤ B * ‖f s₀‖ := by positivity
          linarith
  exact Zeta23.WeilEF.logDeriv_partial_fraction_disk (by norm_num : (0 : ℝ) < 2) hfa hf0 hB2 hfB

private lemma log_B_le (q : ℕ) [NeZero q] (hq : 2 ≤ q) (t : ℝ) :
    Real.log (100 * ((q : ℝ) * (|t| + 2))) ≤ 8 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hX2 : (2 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by
    have : (1 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    nlinarith
  have hXpos : (0 : ℝ) < (q : ℝ) * (|t| + 2) := by linarith
  have hlogX : Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := Real.log_le_log (by norm_num) hX2
  have hlog100 : Real.log 100 ≤ 7 * Real.log 2 := by
    calc Real.log 100 ≤ Real.log ((2 : ℝ) ^ 7) := Real.log_le_log (by norm_num) (by norm_num)
      _ = 7 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [Real.log_mul (by norm_num) hXpos.ne']
  linarith

private lemma log_two_le_logX (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  refine Real.log_le_log (by norm_num) ?_
  have : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  nlinarith

private lemma inv_log_ratio_le : 1 / Real.log ((24 / 25 : ℝ) / (22 / 25)) ≤ 12 := by
  have h : (1 : ℝ) / 12 ≤ Real.log ((24 / 25 : ℝ) / (22 / 25)) := by
    have := Real.one_sub_inv_le_log_of_pos (x := (24 / 25 : ℝ) / (22 / 25)) (by norm_num)
    norm_num at this ⊢
    linarith
  have hpos : 0 < Real.log ((24 / 25 : ℝ) / (22 / 25)) := by linarith
  rw [div_le_iff₀ hpos]
  linarith

end DavenportPF

open DavenportPF in
theorem _root_.SWPort.Davenport.logDeriv_LFunction_partial_fraction_oai :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ t : ℝ,
        ∃ Z : Finset ℂ,
          (↑Z = {ρ ∈ Metric.closedBall (2 + t * Complex.I) (3 / 2) |
                  DirichletCharacter.LFunction χ ρ = 0}) ∧
          (∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
              ≤ C * Real.log ((q : ℝ) * (|t| + 2)) ∧
          ∀ s ∈ Metric.closedBall (2 + t * Complex.I) (7 / 5),
            DirichletCharacter.LFunction χ s ≠ 0 →
              ‖logDeriv (DirichletCharacter.LFunction χ) s
                  - ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
                ≤ C * Real.log ((q : ℝ) * (|t| + 2)) := by
  refine ⟨44795000 / 2 * 8 + 960, by norm_num, ?_⟩
  intro q _ χ hχ t
  have hq : 2 ≤ q := by
    by_contra h
    push Not at h
    have hq1 : q = 1 := by
      have := NeZero.ne q
      omega
    subst hq1
    exact hχ (DirichletCharacter.level_one χ)
  classical
  obtain ⟨Zf, hZf, hcount, hpf⟩ := core χ hχ t
  set f := DirichletCharacter.LFunction χ with hf
  set s₀ : ℂ := 2 + t * I with hs₀
  set X : ℝ := (q : ℝ) * (|t| + 2) with hX
  have hlogB : Real.log (100 * X) ≤ 8 * Real.log X := log_B_le q hq t
  have hlogX0 : 0 < Real.log X := lt_of_lt_of_le (Real.log_pos (by norm_num)) (log_two_le_logX q t)
  have hlogB0 : 0 ≤ Real.log (100 * X) := by
    apply Real.log_nonneg
    have := log_two_le_logX q t
    have hX2 : 2 ≤ X := by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
      have : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
      rw [hX]; nlinarith
    linarith
  -- the zero count
  have hcount' : (∑ ρ ∈ Zf, (analyticOrderNatAt f ρ : ℝ)) ≤ 96 * Real.log X := by
    calc (∑ ρ ∈ Zf, (analyticOrderNatAt f ρ : ℝ))
        ≤ 1 / Real.log ((24 / 25) / (22 / 25)) * Real.log (100 * X) := hcount
      _ ≤ 12 * Real.log (100 * X) := by gcongr; exact inv_log_ratio_le
      _ ≤ 12 * (8 * Real.log X) := by gcongr
      _ = 96 * Real.log X := by ring
  -- restrict to the disc of radius `3/2`
  refine ⟨Zf.filter (fun ρ => ρ ∈ Metric.closedBall s₀ (3 / 2)), ?_, ?_, ?_⟩
  · ext ρ
    simp only [Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hρ, hball⟩
      have : ρ ∈ (↑Zf : Set ℂ) := hρ
      rw [hZf] at this
      exact ⟨hball, this.2⟩
    · rintro ⟨hball, hz⟩
      refine ⟨?_, hball⟩
      have : ρ ∈ (↑Zf : Set ℂ) := by
        rw [hZf]
        refine ⟨?_, hz⟩
        rw [Metric.mem_closedBall] at hball ⊢
        linarith
      exact this
  · calc (∑ ρ ∈ Zf.filter (fun ρ => ρ ∈ Metric.closedBall s₀ (3 / 2)),
            (analyticOrderNatAt f ρ : ℝ))
        ≤ ∑ ρ ∈ Zf, (analyticOrderNatAt f ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => by positivity)
      _ ≤ 96 * Real.log X := hcount'
      _ ≤ (44795000 / 2 * 8 + 960) * Real.log X := by nlinarith
  · intro s hs hfs
    have hs' : s ∈ Metric.closedBall s₀ (83 / 100 * 2) := by
      rw [Metric.mem_closedBall] at hs ⊢; linarith
    have hmain := hpf s hs' hfs
    -- the terms dropped from `Zf`
    set Z := Zf.filter (fun ρ => ρ ∈ Metric.closedBall s₀ (3 / 2)) with hZ
    have hsplit : ∑ ρ ∈ Zf, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
        = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
          + ∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ ∈ Metric.closedBall s₀ (3 / 2)),
              (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by
      rw [hZ, Finset.sum_filter_add_sum_filter_not]
    have hrest : ‖∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ ∈ Metric.closedBall s₀ (3 / 2)),
        (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ 960 * Real.log X := by
      calc ‖∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ ∈ Metric.closedBall s₀ (3 / 2)),
            (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ ∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ ∈ Metric.closedBall s₀ (3 / 2)),
              ‖(analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ ∈ Metric.closedBall s₀ (3 / 2)),
              (analyticOrderNatAt f ρ : ℝ) * 10 := by
            refine Finset.sum_le_sum (fun ρ hρ => ?_)
            rw [Finset.mem_filter] at hρ
            have hfar : 3 / 2 < ‖ρ - s₀‖ := by
              have := hρ.2
              rw [Metric.mem_closedBall, dist_eq_norm] at this
              push Not at this
              exact this
            have hnear : ‖s - s₀‖ ≤ 7 / 5 := by
              rw [Metric.mem_closedBall, dist_eq_norm] at hs; exact hs
            have hdist : 1 / 10 ≤ ‖s - ρ‖ := by
              have h1 : ‖ρ - s₀‖ ≤ ‖ρ - s‖ + ‖s - s₀‖ := by
                calc ‖ρ - s₀‖ = ‖(ρ - s) + (s - s₀)‖ := by ring_nf
                  _ ≤ ‖ρ - s‖ + ‖s - s₀‖ := norm_add_le _ _
              have h2 : ‖ρ - s‖ = ‖s - ρ‖ := norm_sub_rev _ _
              linarith
            rw [norm_div, Complex.norm_natCast]
            have hpos : (0 : ℝ) < ‖s - ρ‖ := by linarith
            rw [div_le_iff₀ hpos]
            have : (0 : ℝ) ≤ (analyticOrderNatAt f ρ : ℝ) := by positivity
            nlinarith
        _ = 10 * ∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ ∈ Metric.closedBall s₀ (3 / 2)),
              (analyticOrderNatAt f ρ : ℝ) := by rw [Finset.mul_sum]; congr 1; ext; ring
        _ ≤ 10 * ∑ ρ ∈ Zf, (analyticOrderNatAt f ρ : ℝ) :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _) (fun _ _ _ => by positivity)) (by norm_num)
        _ ≤ 10 * (96 * Real.log X) := by gcongr
        _ = 960 * Real.log X := by ring
    calc ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
        = ‖(logDeriv f s - ∑ ρ ∈ Zf, (analyticOrderNatAt f ρ : ℂ) / (s - ρ))
            + ∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ ∈ Metric.closedBall s₀ (3 / 2)),
              (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := by
          rw [hsplit]; ring_nf
      _ ≤ ‖logDeriv f s - ∑ ρ ∈ Zf, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
            + ‖∑ ρ ∈ Zf.filter (fun ρ => ¬ ρ ∈ Metric.closedBall s₀ (3 / 2)),
              (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_add_le _ _
      _ ≤ 44795000 / 2 * Real.log (100 * X) + 960 * Real.log X := by
          linarith
      _ ≤ 44795000 / 2 * (8 * Real.log X) + 960 * Real.log X := by
          gcongr
      _ = (44795000 / 2 * 8 + 960) * Real.log X := by ring

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.logDeriv_LFunction_partial_fraction_oai := @SWPort.Davenport.logDeriv_LFunction_partial_fraction_oai
