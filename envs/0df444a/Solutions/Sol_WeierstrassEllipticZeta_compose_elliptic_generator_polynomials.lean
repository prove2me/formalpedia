-- Prove2me | solution 1 for WeierstrassEllipticZeta.compose_elliptic_generator_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T18:15:35.012563+00:00
-- url     : https://prove2.me/submissions/2465c1a2-fd91-417e-8055-f70d5043c0f6

import Definitions.Def_WeierstrassEllipticZeta_MultiplePolynomials
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic.Ring
import Definitions.Def_WeierstrassEllipticZeta_DifferentialPolynomials
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Module.Connected
import Definitions.Def_WeierstrassEllipticZeta_Defs

noncomputable section

open MvPolynomial

namespace TranscendenceTheory

private def polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [polyLength_eq]
    apply Finset.sum_subset hp
    intro m _ hm
    simp [notMem_support_iff.mp hm]
  rw [heq _ support_sum]
  simp_rw [coeff_sum]
  calc
    _ ≤ ∑ m ∈ t, ∑ i ∈ s, ((f i).coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m _
      exact Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [polyLength, support_monomial, ha]

private lemma polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p * q) ≤ polyLength p * polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => polyLength_sum_le _ _).trans
  simp only [polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← polyLength_eq, le_refl]

private lemma polyLength_one {τ : Type} : polyLength (1 : MvPolynomial τ ℤ) = 1 := by
  exact polyLength_monomial (0 : τ →₀ ℕ) 1

private lemma polyLength_C {τ : Type} (a : ℤ) :
    polyLength (C a : MvPolynomial τ ℤ) = a.natAbs :=
  polyLength_monomial 0 a

private lemma polyLength_pow {τ : Type} (p : MvPolynomial τ ℤ) (n : ℕ) :
    polyLength (p ^ n) ≤ polyLength p ^ n := by
  induction n with
  | zero => simp [polyLength_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private lemma polyLength_prod {τ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial τ ℤ) :
    polyLength (∏ i ∈ s, f i) ≤ ∏ i ∈ s, polyLength (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyLength_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_left _ ih)

/-- Clear separate coordinate denominators with degree and coefficient-length bounds. -/
theorem polynomial_clear_denominators_bound {σ τ A : Type} [Fintype σ] [CommRing A]
    (p : MvPolynomial σ ℤ) (k d H : σ → ℕ)
    (s q : σ → MvPolynomial τ ℤ)
    (hp : ∀ i, p.degreeOf i ≤ k i)
    (hs_degree : ∀ i, (s i).totalDegree ≤ d i)
    (hq_degree : ∀ i, (q i).totalDegree ≤ d i)
    (hs_length : ∀ i, (∑ m ∈ (s i).support, ((s i).coeff m).natAbs) ≤ H i)
    (hq_length : ∀ i, (∑ m ∈ (q i).support, ((q i).coeff m).natAbs) ≤ H i) :
    ∃ r : MvPolynomial τ ℤ,
      r.totalDegree ≤ ∑ i, k i * d i ∧
      (∑ m ∈ r.support, (r.coeff m).natAbs) ≤
        (∑ m ∈ p.support, (p.coeff m).natAbs) * ∏ i, H i ^ k i ∧
      ∀ (φ : MvPolynomial τ ℤ →+* A) (y : σ → A),
        (∀ i, φ (s i) = φ (q i) * y i) →
        φ r = (∏ i, φ (q i) ^ k i) * eval₂ (Int.castRingHom A) y p := by
  classical
  let term (m : σ →₀ ℕ) : MvPolynomial τ ℤ :=
    C (p.coeff m) * ∏ i, q i ^ (k i - m i) * s i ^ m i
  let r : MvPolynomial τ ℤ := ∑ m ∈ p.support, term m
  have hm (m : σ →₀ ℕ) (hmem : m ∈ p.support) (i : σ) : m i ≤ k i :=
    (monomial_le_degreeOf i hmem).trans (hp i)
  have hterm_degree (m : σ →₀ ℕ) (hmem : m ∈ p.support) :
      (term m).totalDegree ≤ ∑ i, k i * d i := by
    apply (totalDegree_mul _ _).trans
    simp only [totalDegree_C, zero_add]
    apply (totalDegree_finsetProd _ _).trans
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ (k i - m i) * (q i).totalDegree + m i * (s i).totalDegree :=
        (totalDegree_mul _ _).trans (Nat.add_le_add (totalDegree_pow _ _) (totalDegree_pow _ _))
      _ ≤ (k i - m i) * d i + m i * d i :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (hq_degree i))
          (Nat.mul_le_mul_left _ (hs_degree i))
      _ = k i * d i := by rw [← Nat.add_mul, Nat.sub_add_cancel (hm m hmem i)]
  have hterm_length (m : σ →₀ ℕ) (hmem : m ∈ p.support) :
      polyLength (term m) ≤ (p.coeff m).natAbs * ∏ i, H i ^ k i := by
    apply (polyLength_mul _ _).trans
    rw [polyLength_C]
    apply Nat.mul_le_mul_left
    apply (polyLength_prod _ _).trans
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i _
    calc
      _ ≤ polyLength (q i) ^ (k i - m i) * polyLength (s i) ^ m i :=
        (polyLength_mul _ _).trans (Nat.mul_le_mul (polyLength_pow _ _) (polyLength_pow _ _))
      _ ≤ H i ^ (k i - m i) * H i ^ m i :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (hq_length i) _) (Nat.pow_le_pow_left (hs_length i) _)
      _ = H i ^ k i := by rw [← pow_add, Nat.sub_add_cancel (hm m hmem i)]
  refine ⟨r, totalDegree_finsetSum_le hterm_degree, ?_, ?_⟩
  · change polyLength r ≤ polyLength p * _
    apply (polyLength_sum_le _ _).trans
    calc
      _ ≤ ∑ m ∈ p.support, (p.coeff m).natAbs * ∏ i, H i ^ k i :=
        Finset.sum_le_sum hterm_length
      _ = _ := by rw [← Finset.sum_mul]; rfl
  · intro φ y hy
    change φ (∑ m ∈ p.support, term m) = _
    rw [map_sum, eval₂_eq']
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hmem
    have hfactor (i : σ) :
        φ (q i) ^ (k i - m i) * φ (s i) ^ m i = φ (q i) ^ k i * y i ^ m i := by
      rw [hy i, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hm m hmem i)]
    simp only [term, map_mul, map_prod, map_pow]
    simp_rw [hfactor]
    rw [Finset.prod_mul_distrib]
    have hc : φ (C (p.coeff m)) = (Int.castRingHom A) (p.coeff m) := by
      simp
    rw [hc]
    ring

end TranscendenceTheory

noncomputable section

open Filter
open scoped Topology

namespace WeierstrassEllipticZeta

private lemma zeta_analytic (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z) :
    AnalyticOnNhd ℂ (weierstrassZeta L) L.latticeᶜ :=
  (show DifferentiableOn ℂ (weierstrassZeta L) L.latticeᶜ from
    fun z hz => (hzeta z hz).differentiableAt.differentiableWithinAt).analyticOnNhd
      L.isClosed_lattice.isOpen_compl

private lemma wp_not_constant_germ (L : PeriodPair) (z c : ℂ) (hz : z ∉ L.lattice) :
    ¬ L.weierstrassP =ᶠ[𝓝 z] (fun _ => c) := by
  intro h
  have hconnected : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp)
      (countable_of_Lindelof_of_discrete (X := L.lattice))).2
  have heq : Set.EqOn L.weierstrassP (fun _ => c) L.latticeᶜ :=
    L.analyticOnNhd_weierstrassP.eqOn_of_preconnected_of_frequently_eq
      (fun _ _ => analyticAt_const) hconnected hz
        (h.filter_mono nhdsWithin_le_nhds).frequently
  have hregular : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ L.lattice := by
    have hnhds : ∀ᶠ w in 𝓝 (0 : ℂ), w ∈ ((L.lattice : Set ℂ) \ {0})ᶜ :=
      L.compl_lattice_sdiff_singleton_mem_nhds 0
    filter_upwards [hnhds.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with w hw hw0
    exact fun hwL => hw ⟨hwL, hw0⟩
  have hnear : L.weierstrassP =ᶠ[𝓝[≠] (0 : ℂ)] (fun _ => c) :=
    hregular.mono fun w hw => heq hw
  have ho := meromorphicOrderAt_congr hnear
  rw [L.order_weierstrassP 0 L.lattice.zero_mem, meromorphicOrderAt_const] at ho
  split_ifs at ho <;> norm_num at ho

private lemma wp_difference_ne (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hplus : z + v ∉ L.lattice) (hminus : z - v ∉ L.lattice) :
    L.weierstrassP v - L.weierstrassP z ≠ 0 := by
  intro heq
  let f : ℂ → ℂ := fun w => L.weierstrassP w - L.weierstrassP v
  let a : ℂ → ℂ := fun w => weierstrassZeta L (w + v) +
    weierstrassZeta L (w - v) - 2 * weierstrassZeta L w -
      weierstrassZeta L v - weierstrassZeta L (-v)
  have hf : AnalyticAt ℂ f z := (L.analyticOnNhd_weierstrassP z hz).sub analyticAt_const
  have ha : AnalyticAt ℂ a z := by
    have hZ := zeta_analytic L hzeta
    have hp : AnalyticAt ℂ (fun w => weierstrassZeta L (w + v)) z :=
      (hZ _ hplus).comp (f := fun w : ℂ => w + v) (show AnalyticAt ℂ (fun w : ℂ => w + v) z from
        analyticAt_id.add analyticAt_const)
    have hm : AnalyticAt ℂ (fun w => weierstrassZeta L (w - v)) z :=
      (hZ _ hminus).comp (f := fun w : ℂ => w - v) (show AnalyticAt ℂ (fun w : ℂ => w - v) z from
        analyticAt_id.sub analyticAt_const)
    exact ((((hp.add hm).sub (analyticAt_const.mul (hZ _ hz))).sub
      analyticAt_const).sub analyticAt_const)
  have hzero : f z = 0 := by dsimp [f]; linear_combination -heq
  have hfinite : analyticOrderAt f z ≠ ⊤ := by
    intro ho
    apply wp_not_constant_germ L z (L.weierstrassP v) hz
    filter_upwards [analyticOrderAt_eq_top.mp ho] with w hw
    exact sub_eq_zero.mp hw
  have hderiv : deriv f =ᶠ[𝓝 z] f * a := by
    have hopen := L.isClosed_lattice.isOpen_compl
    filter_upwards [hopen.mem_nhds hz,
      (continuousAt_id.add continuousAt_const).eventually (hopen.mem_nhds hplus),
      (continuousAt_id.sub continuousAt_const).eventually (hopen.mem_nhds hminus)]
        with w hw hwp hwm
    have h1 := hadd w v hw hv hwp
    have h2 := hadd w (-v) hw (by simpa using hv) (by simpa [sub_eq_add_neg] using hwm)
    rw [L.weierstrassP_neg, L.derivWeierstrassP_neg] at h2
    have hD : HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
      simpa using (L.differentiableOn_weierstrassP.differentiableAt
        (hopen.mem_nhds hw)).hasDerivAt
    change deriv (fun w => L.weierstrassP w - L.weierstrassP v) w = f w * a w
    rw [(hD.sub_const _).deriv]
    dsimp [f, a]
    simp only [sub_eq_add_neg] at h2 ⊢
    linear_combination (h1 + h2) / 2
  have ho : analyticOrderAt (deriv f) z + 1 = analyticOrderAt f z := by
    simpa [hzero] using hf.analyticOrderAt_deriv_add_one
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hf ha] at ho
  have hle : analyticOrderAt f z + 1 ≤ analyticOrderAt f z := by
    calc
      _ ≤ (analyticOrderAt f z + analyticOrderAt a z) + 1 :=
        add_le_add (show analyticOrderAt f z ≤ analyticOrderAt f z + analyticOrderAt a z from
          le_self_add) le_rfl
      _ = _ := ho
  exact (lt_irrefl _ ((ENat.add_one_le_iff hfinite).mp hle))

theorem cleared_addition_jet_vanishing_iff
    (L : PeriodPair)
    (hzeta : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (hadd : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice)
    (hp : z + v ∉ L.lattice) (hn : z - v ∉ L.lattice)
    (M T : ℕ) {ι : Type} [Fintype ι]
    (l₀ l₂ l₃ : ι → ℕ) (c : ι → ℂ) :
    (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) ≠ 0 ∧
    ((∀ n < T, ∑ i, c i *
        iteratedDeriv n (clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i))
          z = 0) ↔
      ∀ n < T, iteratedDeriv n (fun w =>
        ∑ i, c i * w ^ l₀ i * L.weierstrassP w ^ l₂ i *
          weierstrassZeta L w ^ l₃ i) (z + v) = 0) := by
  classical
  have hunit : (2 * (L.weierstrassP v - L.weierstrassP z)) ^ (3 * M) ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (by norm_num) (wp_difference_ne L hzeta hadd _ _ hz hv hp hn))
  refine ⟨hunit, ?_⟩
  let A : ℂ → ℂ := fun w => (2 * (L.weierstrassP v - L.weierstrassP w)) ^ (3 * M)
  let F : ℂ → ℂ := fun w => ∑ i, c i * w ^ l₀ i *
    L.weierstrassP w ^ l₂ i * weierstrassZeta L w ^ l₃ i
  let G : ℂ → ℂ := fun w => F (w + v)
  have hA : AnalyticAt ℂ A z :=
    (analyticAt_const.mul (analyticAt_const.sub
      (L.analyticOnNhd_weierstrassP _ hz))).pow _
  have hF : AnalyticAt ℂ F (z + v) := by
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (((analyticAt_const.mul (analyticAt_id.pow _)).mul
      ((L.analyticOnNhd_weierstrassP _ hp).pow _)).mul
      ((zeta_analytic L hzeta _ hp).pow _))
  have hG : AnalyticAt ℂ G z :=
    hF.comp (f := fun w : ℂ => w + v) (show AnalyticAt ℂ (fun w : ℂ => w + v) z from
      analyticAt_id.add analyticAt_const)
  have hmono (i : ι) : AnalyticAt ℂ
      (clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i)) z := by
    have haddA : AnalyticAt ℂ (fun w : ℂ => w + v) z :=
      analyticAt_id.add analyticAt_const
    exact ((((haddA.pow _).mul hA).mul
      (((L.analyticOnNhd_weierstrassP _ hp).comp (f := fun w : ℂ => w + v) haddA).pow _)).mul
      (((zeta_analytic L hzeta _ hp).comp (f := fun w : ℂ => w + v) haddA).pow _))
  have hsum (n : ℕ) : iteratedDeriv n (A * G) z =
      ∑ i, c i * iteratedDeriv n
        (clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i)) z := by
    have heq : A * G = fun w => ∑ i, c i *
        clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) w := by
      funext w
      simp only [Pi.mul_apply, A, G, F, Finset.mul_sum, clearedAdditionMonomial]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [heq, iteratedDeriv_fun_sum (f := fun i w => c i *
      clearedAdditionMonomial L v M (l₀ i) (l₂ i) (l₃ i) w)
        (fun i _ => (analyticAt_const.mul (hmono i)).contDiffAt)]
    apply Finset.sum_congr rfl
    intro i hi
    exact iteratedDeriv_const_mul_field _ _
  have horder : analyticOrderAt (A * G) z = analyticOrderAt G z := by
    rw [analyticOrderAt_mul hA hG, hA.analyticOrderAt_eq_zero.mpr hunit, zero_add]
  have hiff : (∀ n < T, iteratedDeriv n (A * G) z = 0) ↔
      ∀ n < T, iteratedDeriv n G z = 0 := by
    rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hA.mul hG),
      ← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hG, horder]
  simpa only [hsum, G, iteratedDeriv_comp_add_const] using hiff

end WeierstrassEllipticZeta

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

private def polyLength {σ : Type} (p : MvPolynomial σ ℤ) : ℕ :=
  ∑ m ∈ p.support, (p.coeff m).natAbs

private lemma polyLength_eq {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength p = ∑ m ∈ p.support, (p.coeff m).natAbs := rfl

private lemma polyLength_sum_le {σ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial σ ℤ) :
    polyLength (∑ i ∈ s, f i) ≤ ∑ i ∈ s, polyLength (f i) := by
  classical
  let t := s.biUnion fun i => (f i).support
  have heq (p : MvPolynomial σ ℤ) (hp : p.support ⊆ t) :
      polyLength p = ∑ m ∈ t, (p.coeff m).natAbs := by
    rw [polyLength_eq]
    apply Finset.sum_subset hp
    intro m _ hm
    simp [notMem_support_iff.mp hm]
  rw [heq _ support_sum]
  simp_rw [coeff_sum]
  calc
    _ ≤ ∑ m ∈ t, ∑ i ∈ s, ((f i).coeff m).natAbs := by
      apply Finset.sum_le_sum
      intro m _
      exact Int.natAbs_sum_le _ _
    _ = ∑ i ∈ s, polyLength (f i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      exact (heq _ (Finset.subset_biUnion_of_mem (fun i => (f i).support) hi)).symm

private lemma polyLength_monomial {σ : Type} (m : σ →₀ ℕ) (a : ℤ) :
    polyLength (monomial m a) = a.natAbs := by
  classical
  by_cases ha : a = 0 <;> simp [polyLength, support_monomial, ha]

private lemma polyLength_mul {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p * q) ≤ polyLength p * polyLength q := by
  classical
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, monomial_mul]
  apply (polyLength_sum_le _ _).trans
  apply (Finset.sum_le_sum fun _ _ => polyLength_sum_le _ _).trans
  simp only [polyLength_monomial, Int.natAbs_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, ← polyLength_eq, le_refl]

private lemma polyLength_one {τ : Type} : polyLength (1 : MvPolynomial τ ℤ) = 1 := by
  exact polyLength_monomial (0 : τ →₀ ℕ) 1

private lemma polyLength_C {τ : Type} (a : ℤ) :
    polyLength (C a : MvPolynomial τ ℤ) = a.natAbs :=
  polyLength_monomial 0 a

private lemma polyLength_pow {τ : Type} (p : MvPolynomial τ ℤ) (n : ℕ) :
    polyLength (p ^ n) ≤ polyLength p ^ n := by
  induction n with
  | zero => simp [polyLength_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_right _ ih)

private lemma polyLength_prod {τ ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial τ ℤ) :
    polyLength (∏ i ∈ s, f i) ≤ ∏ i ∈ s, polyLength (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polyLength_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (polyLength_mul _ _).trans (Nat.mul_le_mul_left _ ih)

private lemma polyLength_add {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p + q) ≤ polyLength p + polyLength q := by
  simpa [Fin.sum_univ_succ] using polyLength_sum_le (Finset.univ : Finset (Fin 2)) ![p, q]

private lemma polyLength_neg {σ : Type} (p : MvPolynomial σ ℤ) :
    polyLength (-p) = polyLength p := by simp [polyLength]

private lemma polyLength_sub {σ : Type} (p q : MvPolynomial σ ℤ) :
    polyLength (p - q) ≤ polyLength p + polyLength q := by
  simpa only [sub_eq_add_neg, polyLength_neg] using polyLength_add p (-q)

private lemma polyLength_X {σ : Type} (j : σ) :
    polyLength (X j : MvPolynomial σ ℤ) = 1 := polyLength_monomial _ 1

private lemma polyLength_rename {σ τ : Type} (f : σ → τ) (p : MvPolynomial σ ℤ) :
    polyLength (rename f p) ≤ polyLength p := by
  classical
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, rename_monomial]
  apply (polyLength_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  exact (polyLength_monomial _ _).le

private lemma wp_prime_addition (L : PeriodPair)
    (hadd : ∀ z v : ℂ, z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (z v : ℂ) (hz : z ∉ L.lattice) (hv : v ∉ L.lattice) (hplus : z + v ∉ L.lattice) :
    4 * (L.weierstrassP v - L.weierstrassP z) ^ 3 * L.derivWeierstrassP (z + v) =
      -4 * L.derivWeierstrassP z * (L.weierstrassP v - L.weierstrassP z) ^ 3 -
      2 * (L.derivWeierstrassP v - L.derivWeierstrassP z) *
        (6 * L.weierstrassP z ^ 2 - 2 * (L.g₂ / 4)) *
        (L.weierstrassP v - L.weierstrassP z) +
      2 * L.derivWeierstrassP z * (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2 := by
  have hopen := L.isClosed_lattice.isOpen_compl
  have hP (w : ℂ) (hw : w ∉ L.lattice) :
      HasDerivAt L.weierstrassP (L.derivWeierstrassP w) w := by
    simpa using (L.differentiableOn_weierstrassP.differentiableAt (hopen.mem_nhds hw)).hasDerivAt
  have hD := hasDerivAt_derivWeierstrassP L z hz
  have hshift : HasDerivAt (fun w => L.weierstrassP (w + v))
      (L.derivWeierstrassP (z + v)) z := by
    convert! (hP _ hplus).comp z ((hasDerivAt_id z).add_const v) using 1
    simp only [mul_one]
  have heq : (fun w => 4 * (L.weierstrassP v - L.weierstrassP w) ^ 2 *
      L.weierstrassP (w + v)) =ᶠ[𝓝 z] (fun w =>
        -4 * (L.weierstrassP w + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP w) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP w) ^ 2) := by
    filter_upwards [hopen.mem_nhds hz,
      (continuousAt_id.add continuousAt_const).eventually (hopen.mem_nhds hplus)] with w hw hwp
    exact hadd w v hw hv hwp
  have hleft := ((((hP z hz).const_sub (L.weierstrassP v)).pow 2).const_mul 4).mul hshift
  have hright := ((((hP z hz).add_const (L.weierstrassP v)).const_mul (-4)).mul
    (((hP z hz).const_sub (L.weierstrassP v)).pow 2)).add
      ((hD.const_sub (L.derivWeierstrassP v)).pow 2)
  have hh := (hleft.congr_of_eventuallyEq heq.symm).unique hright
  simp only [Pi.pow_apply] at hh
  have hbase := hadd z v hz hv hplus
  linear_combination (L.weierstrassP v - L.weierstrassP z) * hh +
    2 * L.derivWeierstrassP z * hbase

private def addDen : MvPolynomial (Fin 7) ℤ :=
  C 4 * (X 4 - X 1) ^ 3

private def addNum : Fin 3 → MvPolynomial (Fin 7) ℤ :=
  ![C 2 * (X 4 - X 1) ^ 2 * (C 2 * (X 0 + X 3) * (X 4 - X 1) + (X 5 - X 2)),
    (X 4 - X 1) * (-C 4 * (X 1 + X 4) * (X 4 - X 1) ^ 2 + (X 5 - X 2) ^ 2),
    -C 4 * X 2 * (X 4 - X 1) ^ 3 -
      C 2 * (X 5 - X 2) * (C 6 * X 1 ^ 2 - C 2 * X 6) * (X 4 - X 1) +
      C 2 * X 2 * (X 5 - X 2) ^ 2]

private def PolyBound {σ : Type} (p : MvPolynomial σ ℤ) (d h : ℕ) : Prop :=
  p.totalDegree ≤ d ∧ polyLength p ≤ h

private lemma bound_C {σ : Type} (a : ℤ) : PolyBound (C a : MvPolynomial σ ℤ) 0 a.natAbs :=
  ⟨by simp only [totalDegree_C, le_refl], (polyLength_C a).le⟩
private lemma bound_X {σ : Type} (j : σ) : PolyBound (X j : MvPolynomial σ ℤ) 1 1 :=
  ⟨by simp, (polyLength_X j).le⟩
private lemma bound_mul {σ : Type} {p q : MvPolynomial σ ℤ} {d e h k : ℕ}
    (hp : PolyBound p d h) (hq : PolyBound q e k) : PolyBound (p * q) (d + e) (h * k) :=
  ⟨(totalDegree_mul _ _).trans (Nat.add_le_add hp.1 hq.1),
    (polyLength_mul _ _).trans (Nat.mul_le_mul hp.2 hq.2)⟩
private lemma bound_add {σ : Type} {p q : MvPolynomial σ ℤ} {d e h k : ℕ}
    (hp : PolyBound p d h) (hq : PolyBound q e k) : PolyBound (p + q) (max d e) (h + k) :=
  ⟨(totalDegree_add _ _).trans (max_le_max hp.1 hq.1),
    (polyLength_add _ _).trans (Nat.add_le_add hp.2 hq.2)⟩
private lemma bound_sub {σ : Type} {p q : MvPolynomial σ ℤ} {d e h k : ℕ}
    (hp : PolyBound p d h) (hq : PolyBound q e k) : PolyBound (p - q) (max d e) (h + k) :=
  ⟨(totalDegree_sub _ _).trans (max_le_max hp.1 hq.1),
    (polyLength_sub _ _).trans (Nat.add_le_add hp.2 hq.2)⟩
private lemma bound_neg {σ : Type} {p : MvPolynomial σ ℤ} {d h : ℕ}
    (hp : PolyBound p d h) : PolyBound (-p) d h := by simpa [PolyBound, polyLength_neg] using hp
private lemma bound_pow {σ : Type} {p : MvPolynomial σ ℤ} {d h : ℕ}
    (hp : PolyBound p d h) (n : ℕ) : PolyBound (p ^ n) (n * d) (h ^ n) :=
  ⟨(totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hp.1),
    (polyLength_pow _ _).trans (Nat.pow_le_pow_left hp.2 _)⟩
private lemma bound_mono {σ : Type} {p : MvPolynomial σ ℤ} {d e h k : ℕ}
    (hp : PolyBound p d h) (hd : d ≤ e) (hh : h ≤ k) : PolyBound p e k :=
  ⟨hp.1.trans hd, hp.2.trans hh⟩

private lemma addition_polynomial_bounds :
    PolyBound addDen 4 128 ∧ ∀ j, PolyBound (addNum j) 4 128 := by
  have hx (j : Fin 7) := bound_X j
  have hd := bound_sub (hx 4) (hx 1)
  have hy := bound_sub (hx 5) (hx 2)
  have hz := bound_add (hx 0) (hx 3)
  have hp := bound_add (hx 1) (hx 4)
  have hg := bound_sub (bound_mul (bound_C 6) (bound_pow (hx 1) 2))
    (bound_mul (bound_C 2) (hx 6))
  refine ⟨bound_mono (bound_mul (bound_C 4) (bound_pow hd 3)) (by norm_num) (by norm_num), ?_⟩
  intro j
  fin_cases j
  · exact bound_mono (bound_mul (bound_mul (bound_C 2) (bound_pow hd 2))
      (bound_add (bound_mul (bound_mul (bound_C 2) hz) hd) hy)) (by norm_num) (by norm_num)
  · exact bound_mono (bound_mul hd (bound_add
      (bound_mul (bound_mul (bound_neg (bound_C 4)) hp) (bound_pow hd 2))
      (bound_pow hy 2))) (by norm_num) (by norm_num)
  · exact bound_mono (bound_add
      (bound_sub (bound_mul (bound_mul (bound_neg (bound_C 4)) (hx 2)) (bound_pow hd 3))
        (bound_mul (bound_mul (bound_mul (bound_C 2) hy) hg) hd))
      (bound_mul (bound_mul (bound_C 2) (hx 2)) (bound_pow hy 2))) (by norm_num) (by norm_num)

private def additionCoordinates (L : PeriodPair) (z v : ℂ) : Fin 7 → ℂ :=
  ![weierstrassZeta L z, L.weierstrassP z, L.derivWeierstrassP z,
    weierstrassZeta L v, L.weierstrassP v, L.derivWeierstrassP v, L.g₂ / 4]

private lemma compose_presentations (L : PeriodPair) (ω u₁ u₂ z v : ℂ)
    (D₁ D₂ H₁ H₂ : ℕ)
    (A : EllipticGeneratorPresentation L ω u₁ u₂ z D₁ H₁)
    (B : EllipticGeneratorPresentation L ω u₁ u₂ v D₂ H₂)
    (hden : eval₂ (Int.castRingHom ℂ) (additionCoordinates L z v) addDen ≠ 0)
    (hvalues : ∀ j : Fin 3,
      eval₂ (Int.castRingHom ℂ) (additionCoordinates L z v) (addNum j) =
      eval₂ (Int.castRingHom ℂ) (additionCoordinates L z v) addDen *
        (![weierstrassZeta L (z + v), L.weierstrassP (z + v), L.derivWeierstrassP (z + v)] j)) :
    Nonempty (EllipticGeneratorPresentation L ω u₁ u₂ (z + v)
      (12 * D₁ + 12 * D₂ + 4) (128 * H₁ ^ 12 * H₂ ^ 12)) := by
  classical
  let s : Fin 7 → MvPolynomial (Fin 9) ℤ :=
    ![A.numerator 0, A.numerator 1, A.numerator 2,
      B.numerator 0, B.numerator 1, B.numerator 2, X 1]
  let q : Fin 7 → MvPolynomial (Fin 9) ℤ :=
    ![A.denominator, A.denominator, A.denominator,
      B.denominator, B.denominator, B.denominator, 1]
  let d : Fin 7 → ℕ := ![D₁, D₁, D₁, D₂, D₂, D₂, 1]
  let h : Fin 7 → ℕ := ![H₁, H₁, H₁, H₂, H₂, H₂, 1]
  let E := eval₂Hom (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂)
  let F := ∏ j, E (q j) ^ 4
  have hsD (j : Fin 7) : (s j).totalDegree ≤ d j := by
    fin_cases j
    · exact A.numerator_degree 0
    · exact A.numerator_degree 1
    · exact A.numerator_degree 2
    · exact B.numerator_degree 0
    · exact B.numerator_degree 1
    · exact B.numerator_degree 2
    · simp [s, d]
  have hqD (j : Fin 7) : (q j).totalDegree ≤ d j := by
    fin_cases j <;> first | exact A.denominator_degree | exact B.denominator_degree | simp [q, d]
  have hsh (j : Fin 7) : (∑ m ∈ (s j).support, ((s j).coeff m).natAbs) ≤ h j := by
    fin_cases j
    · exact A.numerator_length 0
    · exact A.numerator_length 1
    · exact A.numerator_length 2
    · exact B.numerator_length 0
    · exact B.numerator_length 1
    · exact B.numerator_length 2
    · exact (polyLength_X (1 : Fin 9)).le
  have hqh (j : Fin 7) : (∑ m ∈ (q j).support, ((q j).coeff m).natAbs) ≤ h j := by
    fin_cases j <;> first | exact A.denominator_length | exact B.denominator_length | exact polyLength_one.le
  have hsq (j : Fin 7) : E (s j) = E (q j) * additionCoordinates L z v j := by
    fin_cases j
    · exact A.evaluation 0
    · exact A.evaluation 1
    · exact A.evaluation 2
    · exact B.evaluation 0
    · exact B.evaluation 1
    · exact B.evaluation 2
    · simp [E, s, q, additionCoordinates, ellipticArithmeticGenerators]
  have hF : F ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply pow_ne_zero
    fin_cases j <;> first | exact A.denominator_ne_zero | exact B.denominator_ne_zero | simp [E, q]
  have hclear (P : MvPolynomial (Fin 7) ℤ) (hP : PolyBound P 4 128) :
      ∃ r : MvPolynomial (Fin 9) ℤ,
        r.totalDegree ≤ 12 * D₁ + 12 * D₂ + 4 ∧
        (∑ m ∈ r.support, (r.coeff m).natAbs) ≤ 128 * H₁ ^ 12 * H₂ ^ 12 ∧
        E r = F * eval₂ (Int.castRingHom ℂ) (additionCoordinates L z v) P := by
    obtain ⟨r, hrD, hrH, hre⟩ := TranscendenceTheory.polynomial_clear_denominators_bound
      (A := ℂ) P (fun _ => 4) d h s q
      (fun j => (degreeOf_le_totalDegree P j).trans hP.1) hsD hqD hsh hqh
    refine ⟨r, ?_, ?_, hre E (additionCoordinates L z v) hsq⟩
    · convert hrD using 1
      simp [d, Fin.sum_univ_succ]
      omega
    · apply hrH.trans
      have hh := Nat.mul_le_mul_right (∏ j, h j ^ 4) hP.2
      have hprod : (∏ j, h j ^ 4) = H₁ ^ 12 * H₂ ^ 12 := by
        simp [h, Fin.prod_univ_succ]
        ring
      simpa only [polyLength, hprod, mul_assoc] using hh
  obtain ⟨Q, hQD, hQH, hQE⟩ := hclear addDen addition_polynomial_bounds.1
  have hnums (j : Fin 3) := hclear (addNum j) (addition_polynomial_bounds.2 j)
  choose R hRD hRH hRE using hnums
  refine ⟨{
    numerator := R
    denominator := Q
    numerator_degree := hRD
    denominator_degree := hQD
    numerator_length := hRH
    denominator_length := hQH
    denominator_ne_zero := ?_
    evaluation := ?_ }⟩
  · change E Q ≠ 0
    rw [hQE]
    exact mul_ne_zero hF hden
  · intro j
    change E (R j) = E Q * _
    rw [hRE, hvalues, hQE, mul_assoc]

private lemma lift_multiple (L : PeriodPair) (ω u₁ u₂ u : ℂ) (n D H : ℕ)
    (f : Fin 5 → Fin 9)
    (hf : ellipticArithmeticGenerators L ω u₁ u₂ ∘ f = ellipticMultipleGenerators L u)
    (A : EllipticMultiplePresentation L u n D H) :
    Nonempty (EllipticGeneratorPresentation L ω u₁ u₂ (n * u) D H) := by
  refine ⟨{
    numerator := fun j => rename f (A.numerator j)
    denominator := rename f A.denominator
    numerator_degree := fun j => (totalDegree_rename_le _ _).trans (A.numerator_degree j)
    denominator_degree := (totalDegree_rename_le _ _).trans A.denominator_degree
    numerator_length := fun j => (polyLength_rename _ _).trans (A.numerator_length j)
    denominator_length := (polyLength_rename _ _).trans A.denominator_length
    denominator_ne_zero := ?_
    evaluation := ?_ }⟩
  · rw [eval₂_rename, hf]
    exact A.denominator_ne_zero
  · intro j
    rw [eval₂_rename, eval₂_rename, hf]
    exact A.evaluation j

private lemma shift_presentation (L : PeriodPair) (ω u₁ u₂ w : ℂ) (n D H : ℕ)
    (hp : L.weierstrassP (w + n * ω) = L.weierstrassP w ∧
      L.derivWeierstrassP (w + n * ω) = L.derivWeierstrassP w ∧
      weierstrassZeta L (w + n * ω) = weierstrassZeta L w + n * zetaQuasiPeriod L ω)
    (A : EllipticGeneratorPresentation L ω u₁ u₂ w D H) :
    Nonempty (EllipticGeneratorPresentation L ω u₁ u₂ (w + n * ω) (D + 1) ((1 + n) * H)) := by
  let R := A.numerator 0 + C (n : ℤ) * X 0 * A.denominator
  have hP (j : Fin 3) : PolyBound (A.numerator j) D H :=
    ⟨A.numerator_degree j, A.numerator_length j⟩
  have hQ : PolyBound A.denominator D H := ⟨A.denominator_degree, A.denominator_length⟩
  have hR : PolyBound R (D + 1) ((1 + n) * H) := by
    apply bound_mono (bound_add (hP 0) (bound_mul
      (bound_mul (bound_C (n : ℤ)) (bound_X 0)) hQ))
    · omega
    · simp only [Int.natAbs_natCast, mul_one]
      exact le_of_eq (by ring)
  have hHH : H ≤ (1 + n) * H := by nlinarith
  refine ⟨{
    numerator := ![R, A.numerator 1, A.numerator 2]
    denominator := A.denominator
    numerator_degree := ?_
    denominator_degree := A.denominator_degree.trans (Nat.le_add_right _ _)
    numerator_length := ?_
    denominator_length := A.denominator_length.trans hHH
    denominator_ne_zero := A.denominator_ne_zero
    evaluation := ?_ }⟩
  · intro j
    fin_cases j
    · exact hR.1
    · exact (hP 1).1.trans (Nat.le_add_right _ _)
    · exact (hP 2).1.trans (Nat.le_add_right _ _)
  · intro j
    fin_cases j
    · exact hR.2
    · exact (hP 1).2.trans hHH
    · exact (hP 2).2.trans hHH
  · intro j
    fin_cases j
    · change eval₂ (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂) R =
        eval₂ (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂) A.denominator *
          weierstrassZeta L (w + n * ω)
      dsimp only [R]
      rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_C, eval₂_X, A.evaluation, hp.2.2]
      simp only [ellipticArithmeticGenerators, Matrix.cons_val_zero]
      simp only [map_natCast]
      ring
    · change eval₂ (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂) (A.numerator 1) =
        eval₂ (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂) A.denominator *
          L.weierstrassP (w + n * ω)
      rw [hp.1]
      exact A.evaluation 1
    · change eval₂ (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂) (A.numerator 2) =
        eval₂ (Int.castRingHom ℂ) (ellipticArithmeticGenerators L ω u₁ u₂) A.denominator *
          L.derivWeierstrassP (w + n * ω)
      rw [hp.2.1]
      exact A.evaluation 2

/-- Combine single-point multiplication polynomials by addition and period translation. -/
theorem solution
    (L : PeriodPair) (ω u₁ u₂ : ℂ)
    (h_grid : RegularAuxiliaryGridData L ω u₁ u₂)
    (h_zeta_deriv : ∀ z : ℂ, z ∉ L.lattice →
      HasDerivAt (weierstrassZeta L) (-L.weierstrassP z) z)
    (h_zeta_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      2 * (L.weierstrassP v - L.weierstrassP z) * weierstrassZeta L (z + v) =
        2 * (weierstrassZeta L z + weierstrassZeta L v) *
          (L.weierstrassP v - L.weierstrassP z) +
        L.derivWeierstrassP v - L.derivWeierstrassP z)
    (h_wp_addition : ∀ z v : ℂ,
      z ∉ L.lattice → v ∉ L.lattice → z + v ∉ L.lattice →
      4 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * L.weierstrassP (z + v) =
        -4 * (L.weierstrassP z + L.weierstrassP v) *
          (L.weierstrassP v - L.weierstrassP z) ^ 2 +
        (L.derivWeierstrassP v - L.derivWeierstrassP z) ^ 2)
    (h₁ : EllipticMultiplePolynomialData L u₁)
    (h₂ : EllipticMultiplePolynomialData L u₂) :
    EllipticGeneratorPolynomialData L ω u₁ u₂ := by
  classical
  obtain ⟨C₁, H₁, hC₁, hH₁, hm₁⟩ := h₁
  obtain ⟨C₂, H₂, hC₂, hH₂, hm₂⟩ := h₂
  let C := 12 * (C₁ + C₂) + 5
  let H := 129 + H₁ ^ 12 + H₂ ^ 12 + H₁ + H₂
  have hH : 1 ≤ H := by dsimp [H]; omega
  have hH₁H : H₁ ≤ H := by dsimp [H]; omega
  have hH₂H : H₂ ≤ H := by dsimp [H]; omega
  have h128 : 128 ≤ H := by dsimp [H]; omega
  have hH₁12 : H₁ ^ 12 ≤ H := by dsimp [H]; omega
  have hH₂12 : H₂ ^ 12 ≤ H := by dsimp [H]; omega
  let f₁ : Fin 5 → Fin 9 := ![1, 2, 3, 4, 5]
  let f₂ : Fin 5 → Fin 9 := ![1, 2, 6, 7, 8]
  have hf₁ : ellipticArithmeticGenerators L ω u₁ u₂ ∘ f₁ = ellipticMultipleGenerators L u₁ := by
    funext j; fin_cases j <;> rfl
  have hf₂ : ellipticArithmeticGenerators L ω u₁ u₂ ∘ f₂ = ellipticMultipleGenerators L u₂ := by
    funext j; fin_cases j <;> rfl
  have hreg (m : Fin 3 → ℤ) (hm : m 0 ≠ 0 ∨ m 1 ≠ 0) :
      integerGridPoint u₁ u₂ ω m ∉ L.lattice := by
    intro hl
    have hh := (h_grid.lattice_iff m).mp hl
    rcases hm with h | h
    · exact h hh.1
    · exact h hh.2
  refine ⟨C, H, by dsimp [C]; omega, by omega, ?_⟩
  intro a ha
  let T := a 0 ^ 2 + a 1 ^ 2 + 1
  let w : ℂ := (a 0 : ℂ) * u₁ + (a 1 : ℂ) * u₂
  have hT : 1 ≤ T := by dsimp [T]; omega
  have haT : a 0 ^ 2 ≤ T := by dsimp [T]; omega
  have hbT : a 1 ^ 2 ≤ T := by dsimp [T]; omega
  have hab : a 0 ≠ 0 ∨ a 1 ≠ 0 := by
    by_contra! hh
    apply ha
    exact (h_grid.lattice_iff _).mpr ⟨by simp [hh.1], by simp [hh.2]⟩
  have hw : w ∉ L.lattice := by
    have hh : (a 0 : ℤ) ≠ 0 ∨ (a 1 : ℤ) ≠ 0 := by exact_mod_cast hab
    simpa [integerGridPoint, w] using hreg ![(a 0 : ℤ), (a 1 : ℤ), 0] hh
  have hdeg₁ : C₁ * a 0 ^ 2 + 1 ≤ C * T := by
    have hh := Nat.mul_le_mul_left C₁ haT
    have hC : C₁ + 1 ≤ C := by dsimp [C]; omega
    have hC' := Nat.mul_le_mul_right T hC
    nlinarith
  have hdeg₂ : C₂ * a 1 ^ 2 + 1 ≤ C * T := by
    have hh := Nat.mul_le_mul_left C₂ hbT
    have hC : C₂ + 1 ≤ C := by dsimp [C]; omega
    have hC' := Nat.mul_le_mul_right T hC
    nlinarith
  have hlen₁ : H₁ ^ (a 0 ^ 2) ≤ H ^ T :=
    (Nat.pow_le_pow_left hH₁H _).trans (pow_le_pow_right₀ hH haT)
  have hlen₂ : H₂ ^ (a 1 ^ 2) ≤ H ^ T :=
    (Nat.pow_le_pow_left hH₂H _).trans (pow_le_pow_right₀ hH hbT)
  have hbase : ∃ D J : ℕ,
      Nonempty (EllipticGeneratorPresentation L ω u₁ u₂ w D J) ∧
      D + 1 ≤ C * T ∧ J ≤ H ^ T := by
    by_cases ha0 : a 0 = 0
    · have hb0 : 0 < a 1 := Nat.pos_of_ne_zero (hab.resolve_left (not_not.mpr ha0))
      obtain ⟨A⟩ := hm₂ (a 1) hb0
      refine ⟨C₂ * a 1 ^ 2, H₂ ^ (a 1 ^ 2), ?_, hdeg₂, hlen₂⟩
      simpa [w, ha0] using lift_multiple L ω u₁ u₂ u₂ (a 1) _ _ f₂ hf₂ A
    by_cases hb0 : a 1 = 0
    · obtain ⟨A⟩ := hm₁ (a 0) (Nat.pos_of_ne_zero ha0)
      refine ⟨C₁ * a 0 ^ 2, H₁ ^ (a 0 ^ 2), ?_, hdeg₁, hlen₁⟩
      simpa [w, hb0] using lift_multiple L ω u₁ u₂ u₁ (a 0) _ _ f₁ hf₁ A
    obtain ⟨A₀⟩ := hm₁ (a 0) (Nat.pos_of_ne_zero ha0)
    obtain ⟨B₀⟩ := hm₂ (a 1) (Nat.pos_of_ne_zero hb0)
    obtain ⟨A⟩ := lift_multiple L ω u₁ u₂ u₁ (a 0) _ _ f₁ hf₁ A₀
    obtain ⟨B⟩ := lift_multiple L ω u₁ u₂ u₂ (a 1) _ _ f₂ hf₂ B₀
    let z : ℂ := a 0 * u₁
    let v : ℂ := a 1 * u₂
    have hz : z ∉ L.lattice := by
      simpa [integerGridPoint, z] using hreg ![(a 0 : ℤ), 0, 0]
        (Or.inl (by change (a 0 : ℤ) ≠ 0; exact_mod_cast ha0))
    have hv : v ∉ L.lattice := by
      simpa [integerGridPoint, v] using hreg ![0, (a 1 : ℤ), 0]
        (Or.inr (by change (a 1 : ℤ) ≠ 0; exact_mod_cast hb0))
    have hn : z - v ∉ L.lattice := by
      simpa [integerGridPoint, z, v, sub_eq_add_neg] using
        hreg ![(a 0 : ℤ), -(a 1 : ℤ), 0]
          (Or.inl (by change (a 0 : ℤ) ≠ 0; exact_mod_cast ha0))
    have hp : z + v ∉ L.lattice := hw
    have hdiff : L.weierstrassP v - L.weierstrassP z ≠ 0 := by
      have hh := (cleared_addition_jet_vanishing_iff L h_zeta_deriv h_zeta_addition z v
        hz hv hp hn 1 0 (ι := Fin 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)).1
      intro he
      simp [he] at hh
    have hden : eval₂ (Int.castRingHom ℂ) (additionCoordinates L z v) addDen ≠ 0 := by
      simpa [addDen, additionCoordinates] using
        mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) (pow_ne_zero 3 hdiff)
    have hZ := h_zeta_addition z v hz hv hp
    have hP := h_wp_addition z v hz hv hp
    have hD := wp_prime_addition L h_wp_addition z v hz hv hp
    have hvalues : ∀ j : Fin 3,
        eval₂ (Int.castRingHom ℂ) (additionCoordinates L z v) (addNum j) =
        eval₂ (Int.castRingHom ℂ) (additionCoordinates L z v) addDen *
          (![weierstrassZeta L (z + v), L.weierstrassP (z + v), L.derivWeierstrassP (z + v)] j) := by
      intro j
      fin_cases j <;> simp [addNum, addDen, additionCoordinates]
      · linear_combination -2 * (L.weierstrassP v - L.weierstrassP z) ^ 2 * hZ
      · linear_combination -(L.weierstrassP v - L.weierstrassP z) * hP
      · linear_combination -hD
    refine ⟨12 * (C₁ * a 0 ^ 2) + 12 * (C₂ * a 1 ^ 2) + 4,
      128 * (H₁ ^ (a 0 ^ 2)) ^ 12 * (H₂ ^ (a 1 ^ 2)) ^ 12,
      compose_presentations L ω u₁ u₂ z v _ _ _ _ A B hden hvalues, ?_, ?_⟩
    · have h1 := Nat.mul_le_mul_left C₁ haT
      have h2 := Nat.mul_le_mul_left C₂ hbT
      dsimp [C]
      nlinarith
    · calc
        _ = 128 * (H₁ ^ 12) ^ (a 0 ^ 2) * (H₂ ^ 12) ^ (a 1 ^ 2) := by
          simp only [← pow_mul, mul_comm]
        _ ≤ H * H ^ (a 0 ^ 2) * H ^ (a 1 ^ 2) := Nat.mul_le_mul
          (Nat.mul_le_mul h128 (Nat.pow_le_pow_left hH₁12 _)) (Nat.pow_le_pow_left hH₂12 _)
        _ = H ^ T := by simp [← pow_succ', ← pow_add, T, add_assoc, add_comm]
  obtain ⟨D, J, ⟨P⟩, hD, hJ⟩ := hbase
  have hperiod := h_grid.period_values w (a 2) hw
  obtain ⟨Q⟩ := shift_presentation L ω u₁ u₂ w (a 2) D J (by exact_mod_cast hperiod) P
  have heq : w + (a 2 : ℂ) * ω = integerGridPoint u₁ u₂ ω (fun j => a j) := by
    simp [w, integerGridPoint]
  rw [← heq]
  refine ⟨{
    numerator := Q.numerator
    denominator := Q.denominator
    numerator_degree := fun j => (Q.numerator_degree j).trans hD
    denominator_degree := Q.denominator_degree.trans hD
    numerator_length := fun j => (Q.numerator_length j).trans (Nat.mul_le_mul_left _ hJ)
    denominator_length := Q.denominator_length.trans (Nat.mul_le_mul_left _ hJ)
    denominator_ne_zero := Q.denominator_ne_zero
    evaluation := Q.evaluation }⟩

