-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_division_wp_identities
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T21:51:48.326913+00:00
-- url     : https://prove2.me/submissions/bb674038-e1db-44bd-99f1-7d630a273f63

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition
import Theorems.Thm_WeierstrassEllipticZeta_exists_elliptic_sigma_addition_data
import Theorems.Thm_WeierstrassEllipticZeta_hasDerivAt_weierstrassZeta
import Theorems.Thm_WeierstrassEllipticZeta_zeta_addition_formula
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

noncomputable section
open MvPolynomial Filter
open scoped Topology
namespace WeierstrassEllipticZeta

/-- The derivative of ℘ has isolated zeros on the complement of the lattice.
Its triple pole at zero rules out the identically zero alternative. -/
lemma derivWeierstrassP_eventually_ne_zero (L : PeriodPair) (v : ℂ)
    (hv : v ∉ L.lattice) :
    ∀ᶠ w in 𝓝[≠] v, L.derivWeierstrassP w ≠ 0 := by
  by_contra h
  have hf : ∃ᶠ w in 𝓝[≠] v, L.derivWeierstrassP w = 0 := by simpa using h
  have hconnected : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have heq : Set.EqOn L.derivWeierstrassP (fun _ ↦ 0) L.latticeᶜ :=
    L.analyticOnNhd_derivWeierstrassP.eqOn_of_preconnected_of_frequently_eq
      (fun _ _ ↦ analyticAt_const) hconnected hv hf
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    intro hwL
    exact hw ⟨hwL, hw0⟩
  have hnear : L.derivWeierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ ↦ 0) :=
    hregular.mono fun w hw ↦ heq hw
  have ho := meromorphicOrderAt_congr hnear
  have hpole : meromorphicOrderAt L.derivWeierstrassP 0 = ((-3 : ℤ) : WithTop ℤ) := by
    rw [← L.deriv_weierstrassP]
    exact meromorphicOrderAt_deriv (n := -3) (by norm_num)
      (by simpa using L.order_weierstrassP 0 L.lattice.zero_mem)
  rw [hpole, meromorphicOrderAt_const] at ho
  norm_num at ho

private lemma second_derivative_of_ne_zero (L : PeriodPair) (v : ℂ)
    (hv : v ∉ L.lattice) (hne : L.derivWeierstrassP v ≠ 0) :
    deriv L.derivWeierstrassP v = 6 * L.weierstrassP v ^ 2 - L.g₂ / 2 := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP v) v := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hv)).hasDerivAt
  have hD := (L.differentiableOn_derivWeierstrassP.differentiableAt
    (hopen.mem_nhds hv)).hasDerivAt
  have hnear : ∀ᶠ w in 𝓝 v, w ∉ L.lattice := hopen.mem_nhds hv
  have heq : (fun w ↦ L.derivWeierstrassP w ^ 2) =ᶠ[𝓝 v]
      (fun w ↦ 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) :=
    hnear.mono fun w hw ↦ L.derivWeierstrassP_sq w hw
  have hh := ((hD.pow 2).congr_of_eventuallyEq heq.symm).unique
    ((((hP.pow 3).const_mul 4).sub (hP.const_mul L.g₂)).sub_const L.g₃)
  have hprod : L.derivWeierstrassP v *
      (deriv L.derivWeierstrassP v - (6 * L.weierstrassP v ^ 2 - L.g₂ / 2)) = 0 := by
    linear_combination hh / 2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hne)

/-- The second-order differential equation holds at every regular point,
including zeros of ℘′. -/
theorem hasDerivAt_derivWeierstrassP (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt L.derivWeierstrassP (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hD := L.differentiableOn_derivWeierstrassP.differentiableAt (hopen.mem_nhds hz)
  have hleft : ContinuousAt (deriv L.derivWeierstrassP) z :=
    (L.analyticOnNhd_derivWeierstrassP z hz).deriv.continuousAt
  have hright : ContinuousAt (fun w ↦ 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) z :=
    ((L.analyticOnNhd_weierstrassP z hz).continuousAt.pow 2 |>.const_mul 6).sub
      continuousAt_const
  have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := hopen.mem_nhds hz
  have heq : deriv L.derivWeierstrassP =ᶠ[𝓝[≠] z]
      (fun w ↦ 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      derivWeierstrassP_eventually_ne_zero L z hz] with w hw hne
    exact second_derivative_of_ne_zero L w hw hne
  have hvalue := tendsto_nhds_unique (hleft.tendsto.mono_left nhdsWithin_le_nhds)
    ((hright.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)
  exact hD.hasDerivAt.congr_deriv hvalue


private def sigmaValue {L : PeriodPair} (S : EllipticSigmaData L) (z : ℂ) (n : ℕ) : ℂ :=
  -S.sigma ((n : ℂ) * z) / (-S.sigma z) ^ (n ^ 2)

private lemma sigmaValue_one {L : PeriodPair} (S : EllipticSigmaData L)
    (z : ℂ) (hz : z ∉ L.lattice) : sigmaValue S z 1 = 1 := by
  simp [sigmaValue, S.ne_zero z hz]

private lemma sigmaValue_addition {L : PeriodPair} (S : EllipticSigmaData L)
    (z : ℂ) (m n : ℕ) (hnm : n ≤ m)
    (hm : (m : ℂ) * z ∉ L.lattice) (hn : (n : ℂ) * z ∉ L.lattice) :
    sigmaValue S z (m + n) * sigmaValue S z (m - n) =
      (L.weierstrassP (n * z) - L.weierstrassP (m * z)) *
        sigmaValue S z m ^ 2 * sigmaValue S z n ^ 2 := by
  have hpow : (-S.sigma z) ^ ((m + n) ^ 2) * (-S.sigma z) ^ ((m - n) ^ 2) =
      ((-S.sigma z) ^ (m ^ 2)) ^ 2 * ((-S.sigma z) ^ (n ^ 2)) ^ 2 := by
    rw [← pow_add, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    have H := Nat.sub_add_cancel hnm
    nlinarith
  have ha := S.addition (m * z) (n * z) hm hn
  have hp : ((m + n : ℕ) : ℂ) * z = m * z + n * z := by push_cast; ring
  have hs : ((m - n : ℕ) : ℂ) * z = m * z - n * z := by
    rw [Nat.cast_sub hnm]
    ring
  simp only [sigmaValue, div_mul_div_comm, neg_mul_neg, div_pow, neg_sq,
    hpow, hp, hs, ha]
  ring

private lemma sigmaValue_odd {L : PeriodPair} (S : EllipticSigmaData L)
    (z : ℂ) (hreg : ∀ n : ℕ, 0 < n → (n : ℂ) * z ∉ L.lattice) (k : ℕ) :
    sigmaValue S z (2 * (k + 2) + 1) =
      sigmaValue S z (k + 4) * sigmaValue S z (k + 2) ^ 3 -
        sigmaValue S z (k + 1) * sigmaValue S z (k + 3) ^ 3 := by
  have hz : z ∉ L.lattice := by simpa using hreg 1 (by omega)
  have hA := sigmaValue_addition S z (k + 3) (k + 2) (by omega)
    (hreg _ (by omega)) (hreg _ (by omega))
  have hB := sigmaValue_addition S z (k + 3) 1 (by omega)
    (hreg _ (by omega)) (hreg _ (by omega))
  have hC := sigmaValue_addition S z (k + 2) 1 (by omega)
    (hreg _ (by omega)) (hreg _ (by omega))
  have hsum : k + 3 + (k + 2) = 2 * (k + 2) + 1 := by omega
  simp only [hsum, show k + 3 - (k + 2) = 1 by omega,
    sigmaValue_one S z hz, mul_one] at hA
  simp only [show k + 3 + 1 = k + 4 by omega, show k + 3 - 1 = k + 2 by omega,
    sigmaValue_one S z hz, one_pow, mul_one, Nat.cast_one, one_mul] at hB
  simp only [show k + 2 + 1 = k + 3 by omega, show k + 2 - 1 = k + 1 by omega,
    sigmaValue_one S z hz, one_pow, mul_one, Nat.cast_one, one_mul] at hC
  linear_combination hA - sigmaValue S z (k + 2) ^ 2 * hB +
    sigmaValue S z (k + 3) ^ 2 * hC

private lemma sigmaValue_even {L : PeriodPair} (S : EllipticSigmaData L)
    (z : ℂ) (hreg : ∀ n : ℕ, 0 < n → (n : ℂ) * z ∉ L.lattice) (k : ℕ) :
    sigmaValue S z (2 * (k + 3)) * sigmaValue S z 2 =
      sigmaValue S z (k + 2) ^ 2 * sigmaValue S z (k + 3) * sigmaValue S z (k + 5) -
        sigmaValue S z (k + 1) * sigmaValue S z (k + 3) * sigmaValue S z (k + 4) ^ 2 := by
  have hz : z ∉ L.lattice := by simpa using hreg 1 (by omega)
  have hA := sigmaValue_addition S z (k + 4) (k + 2) (by omega)
    (hreg _ (by omega)) (hreg _ (by omega))
  have hB := sigmaValue_addition S z (k + 4) 1 (by omega)
    (hreg _ (by omega)) (hreg _ (by omega))
  have hC := sigmaValue_addition S z (k + 2) 1 (by omega)
    (hreg _ (by omega)) (hreg _ (by omega))
  have hsum : k + 4 + (k + 2) = 2 * (k + 3) := by omega
  simp only [hsum, show k + 4 - (k + 2) = 2 by omega] at hA
  simp only [show k + 4 + 1 = k + 5 by omega, show k + 4 - 1 = k + 3 by omega,
    sigmaValue_one S z hz, one_pow, mul_one, Nat.cast_one, one_mul] at hB
  simp only [show k + 2 + 1 = k + 3 by omega, show k + 2 - 1 = k + 1 by omega,
    sigmaValue_one S z hz, one_pow, mul_one, Nat.cast_one, one_mul] at hC
  linear_combination hA - sigmaValue S z (k + 2) ^ 2 * hB +
    sigmaValue S z (k + 4) ^ 2 * hC

private lemma sigmaValue_eq_normEDS {L : PeriodPair} (S : EllipticSigmaData L)
    (z : ℂ) (hreg : ∀ n : ℕ, 0 < n → (n : ℂ) * z ∉ L.lattice)
    (b c d : ℂ) (h2 : sigmaValue S z 2 = b) (h3 : sigmaValue S z 3 = c)
    (h4 : sigmaValue S z 4 = d * b) (n : ℕ) :
    sigmaValue S z n = normEDS b c d n := by
  have hz : z ∉ L.lattice := by simpa using hreg 1 (by omega)
  have hb : b ≠ 0 := by
    rw [← h2, sigmaValue]
    exact div_ne_zero (neg_ne_zero.mpr (S.ne_zero _ (hreg 2 (by omega))))
      (pow_ne_zero _ (neg_ne_zero.mpr (S.ne_zero z hz)))
  induction n using normEDSRec with
  | zero => simp [sigmaValue, S.zero]
  | one => simpa using sigmaValue_one S z hz
  | two => simpa using h2
  | three => simpa using h3
  | four => simpa using h4
  | even k h1 h2' h3' h4' h5 =>
    apply mul_right_cancel₀ hb
    rw [← h2, sigmaValue_even S z hreg k, h1, h2', h3', h4', h5, h2]
    simpa [Nat.cast_add, Nat.cast_mul, add_assoc, add_sub_assoc] using
      (normEDS_even b c d ((k : ℤ) + 3)).symm
  | odd k h1 h2' h3' h4' =>
    rw [sigmaValue_odd S z hreg k, h1, h2', h3', h4']
    simpa [Nat.cast_add, Nat.cast_mul, add_assoc, add_sub_assoc] using
      (normEDS_odd b c d ((k : ℤ) + 2)).symm

private def ClearedWpAddition (L : PeriodPair) : Prop :=
  ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
    4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
      -4 * (L.weierstrassP z + L.weierstrassP v) *
        (L.weierstrassP v - L.weierstrassP z) ^ 2 +
      (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2

private lemma wp_double (L : PeriodPair) (hadd : ClearedWpAddition L)
    (z : ℂ) (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    4 * L.derivWeierstrassP z ^ 2 * L.weierstrassP (2 * z) =
      -8 * L.weierstrassP z * L.derivWeierstrassP z ^ 2 +
        (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 2 := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hz)).hasDerivAt
  have hq := hasDerivAt_derivWeierstrassP L z hz
  have hds := continuousAt_dslope_same.mpr hp.differentiableAt
  have hdt := continuousAt_dslope_same.mpr hq.differentiableAt
  have hshift : ContinuousAt (fun v ↦ L.weierstrassP (z + v)) z := by
    apply (L.analyticOnNhd_weierstrassP (z + z) (by simpa [two_mul] using h2z)).continuousAt.comp
    fun_prop
  let F : ℂ → ℂ := fun v ↦
    4 * dslope L.weierstrassP z v ^ 2 * L.weierstrassP (z + v) +
      4 * (L.weierstrassP z + L.weierstrassP v) * dslope L.weierstrassP z v ^ 2 -
      dslope L.derivWeierstrassP z v ^ 2
  have hF : ContinuousAt F z := by
    exact (((hds.pow 2).const_mul 4).mul hshift |>.add
      (((hp.continuousAt.const_add _).const_mul 4).mul (hds.pow 2))).sub (hdt.pow 2)
  have hplus : ∀ᶠ v in 𝓝 z, z + v ∉ L.lattice :=
    (continuousAt_id.const_add z).eventually (hopen.mem_nhds
      (by simpa [two_mul] using h2z))
  have hnear : ∀ᶠ v in 𝓝 z, v ∉ L.lattice := hopen.mem_nhds hz
  have hzero : F =ᶠ[𝓝[≠] z] (fun _ ↦ 0) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      hplus.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with v hv hvp hvne
    have hne : v - z ≠ 0 := sub_ne_zero.mpr hvne
    have ha := hadd z v hz hv hvp
    dsimp only [F]
    rw [dslope_of_ne _ hvne, dslope_of_ne _ hvne, slope_def_field, slope_def_field]
    field_simp
    linear_combination ha
  have hval := tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
    ((tendsto_const_nhds (x := (0 : ℂ))).congr' hzero.symm)
  dsimp only [F] at hval
  rw [dslope_same, dslope_same, hp.deriv, hq.deriv] at hval
  rw [← two_mul] at hval
  linear_combination hval

private lemma wp_prime_double (L : PeriodPair) (hadd : ClearedWpAddition L)
    (z : ℂ) (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    L.derivWeierstrassP z ^ 4 * L.derivWeierstrassP (2 * z) =
      L.derivWeierstrassP z *
        (-L.derivWeierstrassP z ^ 4 + 3 * L.weierstrassP z *
          (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) * L.derivWeierstrassP z ^ 2 -
          (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) ^ 3 / 4) := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hp (w : ℂ) (hw : w ∉ L.lattice) :
      HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hw)).hasDerivAt
  have hpz := hp z hz
  have hq := hasDerivAt_derivWeierstrassP L z hz
  have hqfun : HasDerivAt (fun w ↦ 6 * L.weierstrassP w ^ 2 - L.g₂ / 2)
      (12 * L.weierstrassP z * L.derivWeierstrassP z) z := by
    convert! ((hpz.pow 2).const_mul 6).sub_const (L.g₂ / 2) using 1
    ring
  have hp2 : HasDerivAt (fun w ↦ L.weierstrassP (2 * w))
      (2 * L.derivWeierstrassP (2 * z)) z := by
    simpa [Function.comp_def, mul_comm] using! (hp (2 * z) h2z).comp z ((hasDerivAt_id z).const_mul 2)
  have hleft := ((hq.pow 2).const_mul 4).mul hp2
  have hright := ((hpz.const_mul (-8)).mul (hq.pow 2)).add (hqfun.pow 2)
  have hnear : ∀ᶠ w in 𝓝 z, w ∉ L.lattice := hopen.mem_nhds hz
  have hnear2 : ∀ᶠ w in 𝓝 z, 2 * w ∉ L.lattice :=
    (continuousAt_id.const_mul (2 : ℂ)).eventually (hopen.mem_nhds h2z)
  have heq : (fun w ↦ 4 * L.derivWeierstrassP w ^ 2 * L.weierstrassP (2 * w)) =ᶠ[𝓝 z]
      (fun w ↦ -8 * L.weierstrassP w * L.derivWeierstrassP w ^ 2 +
        (6 * L.weierstrassP w ^ 2 - L.g₂ / 2) ^ 2) := by
    filter_upwards [hnear, hnear2] with w hw hw2
    exact wp_double L hadd w hw hw2
  have hh := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simp only [Pi.pow_apply] at hh
  linear_combination L.derivWeierstrassP z ^ 2 / 8 * hh -
    (L.derivWeierstrassP z * (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) / 4) *
      wp_double L hadd z hz h2z

private def divisionValue (L : PeriodPair) (z : ℂ) (n : ℕ) : ℂ :=
  eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z) (ellipticDivisionPolynomial n)

private lemma divisionValue_eq_normEDS (L : PeriodPair) (z : ℂ) (hz : z ∉ L.lattice) (n : ℕ) :
    divisionValue L z n = normEDS (L.derivWeierstrassP z)
      (eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z) ellipticDivisionC)
      (eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z) ellipticDivisionD) n := by
  let e := eval₂Hom (Int.castRingHom ℂ) (ellipticMultipleGenerators L z)
  have hB : e ellipticDivisionB = L.derivWeierstrassP z ^ 4 := by
    change eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z) ellipticDivisionB = _
    simp [ellipticDivisionB, ellipticMultipleGenerators]
    rw [show L.derivWeierstrassP z ^ 4 = (L.derivWeierstrassP z ^ 2) ^ 2 by ring,
      L.derivWeierstrassP_sq z hz]
    congr 1
    ring
  change e (preNormEDS' ellipticDivisionB ellipticDivisionC ellipticDivisionD n *
      if Even n then X 3 else 1) = _
  rw [map_mul, map_preNormEDS', hB, normEDS_ofNat]
  congr 1
  split_ifs <;> simp [e, ellipticMultipleGenerators]

private lemma sigma_double (L : PeriodPair) (S : EllipticSigmaData L)
    (z : ℂ) (hz : z ∉ L.lattice) (h2z : 2 * z ∉ L.lattice) :
    S.sigma (2 * z) = -S.sigma z ^ 4 * L.derivWeierstrassP z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hz)).hasDerivAt
  have hadd : HasDerivAt (fun v => S.sigma (z + v))
      (weierstrassZeta L (2 * z) * S.sigma (2 * z)) z := by
    have h := S.hasDerivAt (z + z) (by simpa [two_mul] using h2z)
    simpa [two_mul, Function.comp_def] using! h.comp z ((hasDerivAt_id z).const_add z)
  have hsub : HasDerivAt (fun v => S.sigma (z - v)) (-1) z := by
    have h : HasDerivAt S.sigma 1 (z - z) := by simpa using S.deriv_zero
    simpa [Function.comp_def] using! h.comp z ((hasDerivAt_id z).const_sub z)
  have hleft := hadd.mul hsub
  have hright := (((hP.sub_const (L.weierstrassP z)).mul_const (S.sigma z ^ 2)).mul
    ((S.hasDerivAt z hz).pow 2))
  have heq : (fun v => S.sigma (z + v) * S.sigma (z - v)) =ᶠ[𝓝 z]
      (fun v => (L.weierstrassP v - L.weierstrassP z) * S.sigma z ^ 2 *
        S.sigma v ^ 2) := by
    filter_upwards [hopen.mem_nhds hz] with v hv
    exact S.addition z v hz hv
  have hh := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simp only [sub_self, S.zero, mul_zero, zero_mul, zero_add, sub_self, add_zero,
    Pi.pow_apply, ← two_mul] at hh
  linear_combination -hh

private lemma sigmaValue_double {L : PeriodPair} (S : EllipticSigmaData L)
    (z : ℂ) (n : ℕ) (hn : (n : ℂ) * z ∉ L.lattice)
    (h2n : ((2 * n : ℕ) : ℂ) * z ∉ L.lattice) :
    sigmaValue S z (2 * n) = sigmaValue S z n ^ 4 * L.derivWeierstrassP (n * z) := by
  have harg : ((2 * n : ℕ) : ℂ) * z = 2 * ((n : ℂ) * z) := by push_cast; ring
  have hpow : (2 * n) ^ 2 = n ^ 2 * 4 := by ring
  simp only [sigmaValue, harg, sigma_double L S _ hn (harg ▸ h2n), neg_mul, neg_neg,
    div_pow, hpow, pow_mul]
  ring

private lemma sigmaValue_eq_divisionValue (L : PeriodPair) (S : EllipticSigmaData L)
    (hadd : ClearedWpAddition L) (z : ℂ)
    (hreg : ∀ n : ℕ, 0 < n → (n : ℂ) * z ∉ L.lattice) (n : ℕ) :
    sigmaValue S z n = divisionValue L z n := by
  have hz : z ∉ L.lattice := by simpa using hreg 1 (by omega)
  have hz2 : 2 * z ∉ L.lattice := by simpa using hreg 2 (by omega)
  let c := eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z) ellipticDivisionC
  let d := eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z) ellipticDivisionD
  have h2 : sigmaValue S z 2 = L.derivWeierstrassP z := by
    simpa [sigmaValue_one S z hz] using sigmaValue_double S z 1
      (by simpa using hz) (by simpa using hz2)
  have h3 : sigmaValue S z 3 = c := by
    have ha := sigmaValue_addition S z 2 1 (by omega) (by simpa using hz2)
      (by simpa using hz)
    have hc : (L.weierstrassP z - L.weierstrassP (2 * z)) * L.derivWeierstrassP z ^ 2 = c := by
      simp [c, ellipticDivisionC, ellipticMultipleGenerators]
      linear_combination -(wp_double L hadd z hz hz2) / 4 +
        3 * L.weierstrassP z * L.derivWeierstrassP_sq z hz
    simpa [sigmaValue_one S z hz, h2, hc] using ha
  have h4 : sigmaValue S z 4 = d * L.derivWeierstrassP z := by
    have ha := sigmaValue_double S z 2 (by simpa using hz2) (hreg 4 (by omega))
    have hd : L.derivWeierstrassP z ^ 4 * L.derivWeierstrassP (2 * z) =
        d * L.derivWeierstrassP z := by
      rw [wp_prime_double L hadd z hz hz2]
      simp only [show L.derivWeierstrassP z ^ 4 = (L.derivWeierstrassP z ^ 2) ^ 2 by ring,
        L.derivWeierstrassP_sq z hz]
      simp [d, ellipticDivisionD, ellipticMultipleGenerators]
      ring
    simpa [h2, hd] using ha
  rw [divisionValue_eq_normEDS L z hz]
  exact sigmaValue_eq_normEDS S z hreg _ c d h2 h3 h4 n

private lemma generic_wp_identities (L : PeriodPair) (S : EllipticSigmaData L)
    (hadd : ClearedWpAddition L) (z : ℂ)
    (hreg : ∀ n : ℕ, 0 < n → (n : ℂ) * z ∉ L.lattice) (n : ℕ) (hn : 0 < n) :
    divisionValue L z n ^ 2 * L.weierstrassP (n * z) =
      L.weierstrassP z * divisionValue L z n ^ 2 -
        divisionValue L z (n - 1) * divisionValue L z (n + 1) ∧
    divisionValue L z n ^ 4 * L.derivWeierstrassP (n * z) = divisionValue L z (2 * n) := by
  have hz : z ∉ L.lattice := by simpa using hreg 1 (by omega)
  have ha := sigmaValue_addition S z n 1 (by omega) (hreg n hn) (by simpa using hz)
  simp only [sigmaValue_one S z hz, one_pow, mul_one, Nat.cast_one, one_mul] at ha
  simp only [sigmaValue_eq_divisionValue L S hadd z hreg] at ha
  have hd := sigmaValue_double S z n (hreg n hn) (hreg (2 * n) (by omega))
  simp only [sigmaValue_eq_divisionValue L S hadd z hreg] at hd
  constructor
  · linear_combination ha
  · exact hd.symm

private lemma dense_regular_multiples (L : PeriodPair) :
    Dense {z : ℂ | ∀ n : ℕ, 0 < n → (n : ℂ) * z ∉ L.lattice} := by
  have hcount : (L.lattice : Set ℂ).Countable := countable_of_Lindelof_of_discrete (X := L.lattice)
  let B : Set ℂ := ⋃ n : ℕ, (fun z : ℂ ↦ ((n + 1 : ℕ) : ℂ) * z) ⁻¹' L.lattice
  have hB : B.Countable := Set.countable_iUnion fun n ↦ hcount.preimage (by
    intro x y h
    exact mul_left_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n) h)
  apply (hB.dense_compl ℝ).mono
  intro z hz n hn hlat
  apply hz
  exact Set.mem_iUnion.mpr ⟨n - 1, by
    change (((n - 1 + 1 : ℕ) : ℂ) * z) ∈ L.lattice
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hlat⟩

private lemma eval_continuousAt (L : PeriodPair)
    (hζ : ∀ z : ℂ, z ∉ L.lattice → HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (z : ℂ) (hz : z ∉ L.lattice) (p : MvPolynomial (Fin 5) ℤ) :
    ContinuousAt (fun w ↦ eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L w) p) z := by
  have hgen (i : Fin 5) : ContinuousAt (fun w ↦ ellipticMultipleGenerators L w i) z := by
    fin_cases i
    · exact continuousAt_const
    · exact continuousAt_const
    · exact (L.analyticOnNhd_weierstrassP z hz).continuousAt
    · exact (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt
    · exact (hζ z hz).continuousAt
  induction p using MvPolynomial.induction_on with
  | C a => simp only [eval₂_C]; exact continuousAt_const
  | add p q hp hq => simpa [Pi.add_apply] using! hp.add hq
  | mul_X p i hp => simpa [Pi.mul_apply] using! hp.mul (hgen i)

/-- Sigma recurrences give both cleared elliptic multiplication identities. -/
theorem division_wp_identities_from_sigma (L : PeriodPair) (S : EllipticSigmaData L)
    (hζ : ∀ z : ℂ, z ∉ L.lattice → HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hadd : ClearedWpAddition L) : EllipticDivisionWpIdentities L := by
  intro n hn z hz hnz
  dsimp only
  intro _
  have hfreq : ∃ᶠ w in 𝓝 z, ∀ k : ℕ, 0 < k → (k : ℂ) * w ∉ L.lattice :=
    mem_closure_iff_frequently.mp (dense_regular_multiples L z)
  have hd (k : ℕ) : ContinuousAt (fun w ↦ divisionValue L w k) z :=
    eval_continuousAt L hζ z hz _
  have hp := (L.analyticOnNhd_weierstrassP z hz).continuousAt
  have hpn : ContinuousAt (fun w : ℂ ↦ L.weierstrassP (n * w)) z :=
    (L.analyticOnNhd_weierstrassP (n * z) hnz).continuousAt.comp
      (continuousAt_id.const_mul (n : ℂ))
  have hqn : ContinuousAt (fun w : ℂ ↦ L.derivWeierstrassP (n * w)) z :=
    (L.analyticOnNhd_derivWeierstrassP (n * z) hnz).continuousAt.comp
      (continuousAt_id.const_mul (n : ℂ))
  constructor
  · exact tendsto_nhds_unique_of_frequently_eq (((hd n).pow 2).mul hpn).tendsto
      ((hp.mul ((hd n).pow 2)).sub ((hd (n - 1)).mul (hd (n + 1)))).tendsto
      (hfreq.mono fun w hw ↦ (generic_wp_identities L S hadd w hw n hn).1)
  · exact tendsto_nhds_unique_of_frequently_eq (((hd n).pow 4).mul hqn).tendsto
      (hd (2 * n)).tendsto
      (hfreq.mono fun w hw ↦ (generic_wp_identities L S hadd w hw n hn).2)

end WeierstrassEllipticZeta

open WeierstrassEllipticZeta

theorem solution
    (L : PeriodPair)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2) :
    EllipticDivisionWpIdentities L := by
  obtain ⟨S⟩ := exists_elliptic_sigma_addition_data L
    (hasDerivAt_weierstrassZeta L) (zeta_addition_formula L)
  exact division_wp_identities_from_sigma L S
    (hasDerivAt_weierstrassZeta L) h_wp_addition
