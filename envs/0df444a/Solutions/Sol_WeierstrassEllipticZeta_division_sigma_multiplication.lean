-- Prove2me | solution 1 for WeierstrassEllipticZeta.division_sigma_multiplication
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T19:34:16.18383+00:00
-- url     : https://prove2.me/submissions/deefdc79-6f29-418b-b51d-312dadeac44f

import Definitions.Def_WeierstrassEllipticZeta_SigmaAddition
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

noncomputable section

open Filter
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

end WeierstrassEllipticZeta

noncomputable section
open MvPolynomial Filter
open scoped Topology
open WeierstrassEllipticZeta

private def divisionValue (L : PeriodPair) (n : ℕ) (z : ℂ) : ℂ :=
  eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z)
    (ellipticDivisionPolynomial n)

private lemma divisionValue_one (L : PeriodPair) (z : ℂ) :
    divisionValue L 1 z = 1 := by
  simp [divisionValue, ellipticDivisionPolynomial]

private lemma divisionValue_two (L : PeriodPair) (z : ℂ) :
    divisionValue L 2 z = L.derivWeierstrassP z := by
  simp [divisionValue, ellipticDivisionPolynomial, ellipticMultipleGenerators]

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

private lemma sigma_induction_algebra (n : ℕ) (a fn fn1 fn2 sn sn1 sn2 x y : ℂ)
    (ha : a ≠ 0) (hf : fn ≠ 0)
    (hn : sn = (-1) ^ (n + 1) * a ^ (n ^ 2) * fn)
    (hn1 : sn1 = (-1) ^ (n + 2) * a ^ ((n + 1) ^ 2) * fn1)
    (hs : sn2 * sn = (x - y) * sn1 ^ 2 * a ^ 2)
    (hp : fn1 ^ 2 * y = x * fn1 ^ 2 - fn * fn2) :
    sn2 = (-1) ^ (n + 3) * a ^ ((n + 2) ^ 2) * fn2 := by
  have hsign (k : ℕ) : ((-1 : ℂ) ^ k) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    norm_num
  have hsign3 : (-1 : ℂ) ^ (n + 3) = (-1) ^ (n + 1) := by
    rw [show n + 3 = (n + 1) + 2 by omega, pow_add]
    norm_num
  have hpowers : a ^ ((n + 2) ^ 2) * a ^ (n ^ 2) =
      (a ^ ((n + 1) ^ 2)) ^ 2 * a ^ 2 := by
    rw [← pow_add, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hsn : sn ≠ 0 := by
    rw [hn]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ha)) hf
  apply mul_right_cancel₀ hsn
  rw [hs, hn1]
  calc
    (x - y) * ((-1) ^ (n + 2) * a ^ ((n + 1) ^ 2) * fn1) ^ 2 * a ^ 2 =
        (a ^ ((n + 1) ^ 2)) ^ 2 * a ^ 2 * (fn * fn2) := by
      rw [mul_pow, mul_pow, hsign]
      linear_combination -(a ^ ((n + 1) ^ 2)) ^ 2 * a ^ 2 * hp
    _ = (-1) ^ (n + 3) * a ^ ((n + 2) ^ 2) * fn2 * sn := by
      rw [hn, hsign3, ← hpowers]
      calc
        _ = ((-1 : ℂ) ^ (n + 1)) ^ 2 *
            (a ^ ((n + 2) ^ 2) * a ^ (n ^ 2) * (fn * fn2)) := by rw [hsign, one_mul]
        _ = _ := by ring

private lemma sigma_multiplication_aux (L : PeriodPair) (S : EllipticSigmaData L)
    (hwp : EllipticDivisionWpIdentities L) :
    ∀ n : ℕ, 0 < n → ∀ u : ℂ,
      (∀ k : ℕ, 0 < k → k ≤ n → (k : ℂ) * u ∉ L.lattice) →
      S.sigma ((n : ℂ) * u) =
          (-1) ^ (n + 1) * S.sigma u ^ (n ^ 2) * divisionValue L n u ∧
        divisionValue L n u ≠ 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn u hregular
    have hu : u ∉ L.lattice := by simpa using hregular 1 (by omega) (by omega)
    have hnonzero (hformula : S.sigma ((n : ℂ) * u) =
        (-1) ^ (n + 1) * S.sigma u ^ (n ^ 2) * divisionValue L n u) :
        divisionValue L n u ≠ 0 := by
      intro hzero
      apply S.ne_zero _ (hregular n hn le_rfl)
      rw [hformula, hzero, mul_zero]
    suffices hformula : S.sigma ((n : ℂ) * u) =
        (-1) ^ (n + 1) * S.sigma u ^ (n ^ 2) * divisionValue L n u from
      ⟨hformula, hnonzero hformula⟩
    rcases n with _ | _ | _ | n
    · omega
    · simp [divisionValue_one]
    · convert! sigma_double L S u hu (hregular 2 (by omega) le_rfl) using 1
      norm_num [divisionValue_two]
    · have hprev := ih (n + 1) (by omega) (by omega) u
        (fun k hk hkn => hregular k hk (by omega))
      have hmid := ih (n + 2) (by omega) (by omega) u
        (fun k hk hkn => hregular k hk (by omega))
      have hident := (hwp (n + 2) (by omega) u hu
        (hregular (n + 2) (by omega) (by omega)) hmid.2).1
      have hadd := S.addition (((n + 2 : ℕ) : ℂ) * u) u
        (hregular (n + 2) (by omega) (by omega)) hu
      have hplus : ((n + 2 : ℕ) : ℂ) * u + u = ((n + 3 : ℕ) : ℂ) * u := by
        push_cast
        ring
      have hminus : ((n + 2 : ℕ) : ℂ) * u - u = ((n + 1 : ℕ) : ℂ) * u := by
        push_cast
        ring
      rw [hplus, hminus] at hadd
      exact sigma_induction_algebra (n + 1) (S.sigma u)
        (divisionValue L (n + 1) u) (divisionValue L (n + 2) u)
        (divisionValue L (n + 3) u) _ _ _ _ _ (S.ne_zero u hu) hprev.2
        hprev.1 hmid.1 hadd hident

private lemma hasDerivAt_eval_ode {σ : Type}
    (D : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (f : σ → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i, HasDerivAt (f i)
      (eval₂ (Int.castRingHom ℂ) (fun i => f i z) (D (X i))) z)
    (p : MvPolynomial σ ℤ) :
    HasDerivAt (fun w => eval₂ (Int.castRingHom ℂ) (fun i => f i w) p)
      (eval₂ (Int.castRingHom ℂ) (fun i => f i z) (D p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [derivation_C, eval₂_C, eval₂_zero]
    exact hasDerivAt_const z (a : ℂ)
  | add p q hp hq => simpa [Pi.add_apply] using! hp.add hq
  | mul_X p i hp =>
    simpa [D.leibniz, smul_eq_mul, add_comm, mul_comm, Pi.mul_apply] using! hp.mul (hf i)

private lemma hasDerivAt_divisionValue (L : PeriodPair)
    (hζ : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (n : ℕ) (z : ℂ) (hz : z ∉ L.lattice) :
    HasDerivAt (divisionValue L n)
      (eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L z)
        (ellipticMultipleDerivation (ellipticDivisionPolynomial n))) z := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt
      (hopen.mem_nhds hz)).hasDerivAt
  apply hasDerivAt_eval_ode ellipticMultipleDerivation
    (fun i w => ellipticMultipleGenerators L w i) z _ (ellipticDivisionPolynomial n)
  intro i
  fin_cases i
  · simpa [ellipticMultipleGenerators, ellipticMultipleDerivation] using!
      hasDerivAt_const z (L.g₂ / 4)
  · simpa [ellipticMultipleGenerators, ellipticMultipleDerivation] using!
      hasDerivAt_const z (L.g₃ / 4)
  · simpa [ellipticMultipleGenerators, ellipticMultipleDerivation] using! hP
  · convert! hasDerivAt_derivWeierstrassP L z hz using 1
    simp [ellipticMultipleGenerators, ellipticMultipleDerivation]
    ring
  · simpa [ellipticMultipleGenerators, ellipticMultipleDerivation] using! hζ z hz

/-- Sigma addition propagates the division-polynomial identity and its
nonvanishing. Differentiation on a finite regularity neighborhood gives zeta. -/
theorem solution (L : PeriodPair) (S : EllipticSigmaData L)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_wp_division : EllipticDivisionWpIdentities L)
    (u : ℂ) (n : ℕ) (hn : 0 < n)
    (h_regular : ∀ k : ℕ, 0 < k → k ≤ n → (k : ℂ) * u ∉ L.lattice) :
    let e := eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
    let f := fun k => e (ellipticDivisionPolynomial k)
    S.sigma ((n : ℂ) * u) = (-1) ^ (n + 1) * S.sigma u ^ (n ^ 2) * f n ∧
      f n ≠ 0 ∧
      (n : ℂ) * f n * weierstrassZeta L (n * u) =
        (n : ℂ) ^ 2 * f n * weierstrassZeta L u +
          e (ellipticMultipleDerivation (ellipticDivisionPolynomial n)) := by
  have hu : u ∉ L.lattice := by simpa using h_regular 1 (by omega) (by omega)
  obtain ⟨hformula, hnonzero⟩ := sigma_multiplication_aux L S h_wp_division n hn u h_regular
  refine ⟨hformula, hnonzero, ?_⟩
  change (n : ℂ) * divisionValue L n u * weierstrassZeta L (n * u) =
    (n : ℂ) ^ 2 * divisionValue L n u * weierstrassZeta L u +
      eval₂ (Int.castRingHom ℂ) (ellipticMultipleGenerators L u)
        (ellipticMultipleDerivation (ellipticDivisionPolynomial n))
  have hopen := L.isClosed_lattice.isOpen_compl
  have hnear : ∀ᶠ w in 𝓝 u, ∀ k ∈ Finset.Icc 1 n, (k : ℂ) * w ∉ L.lattice := by
    rw [Finset.eventually_all]
    intro k hk
    have hc : ContinuousAt (fun w : ℂ => (k : ℂ) * w) u :=
      continuousAt_const.mul continuousAt_id
    exact hc.eventually (hopen.mem_nhds
      (h_regular k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2))
  have heq : (fun w => S.sigma ((n : ℂ) * w)) =ᶠ[𝓝 u]
      (fun w => (-1) ^ (n + 1) * S.sigma w ^ (n ^ 2) * divisionValue L n w) := by
    filter_upwards [hnear] with w hw
    exact (sigma_multiplication_aux L S h_wp_division n hn w
      (fun k hk hkn => hw k (Finset.mem_Icc.mpr ⟨hk, hkn⟩))).1
  have hpred : S.sigma u ^ (n ^ 2 - 1) * S.sigma u = S.sigma u ^ (n ^ 2) := by
    rw [← pow_succ]
    congr 1
    have : 0 < n ^ 2 := pow_pos hn _
    omega
  have hpow : HasDerivAt (fun w => S.sigma w ^ (n ^ 2))
      ((n : ℂ) ^ 2 * S.sigma u ^ (n ^ 2) * weierstrassZeta L u) u := by
    convert! (S.hasDerivAt u hu).pow (n ^ 2) using 1
    simp only [Nat.cast_pow]
    rw [← hpred]
    ring
  have hleft : HasDerivAt (fun w => S.sigma ((n : ℂ) * w))
      ((n : ℂ) * weierstrassZeta L (n * u) * S.sigma (n * u)) u := by
    convert! (S.hasDerivAt ((n : ℂ) * u) (h_regular n hn le_rfl)).comp u
      ((hasDerivAt_id u).const_mul (n : ℂ)) using 1
    simp only [mul_one]
    ring
  have hright := (hpow.const_mul ((-1 : ℂ) ^ (n + 1))).mul
    (hasDerivAt_divisionValue L h_zeta_deriv n u hu)
  have hh := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  rw [hformula] at hh
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero (n + 1) (by norm_num : (-1 : ℂ) ≠ 0))
    (pow_ne_zero (n ^ 2) (S.ne_zero u hu)))
  linear_combination hh

