-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap20.P05.formationEqualsMarginalPure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:20:04.220114+00:00
-- url     : https://prove2.me/submissions/ad0a1185-2b4c-4c16-b28c-4809f022f899

import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P05
noncomputable section

open Filter

open scoped ENNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Gap20.P05

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity rankOne traceSize traceClosure IsSeparable)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (generalizedRelativeEntropy traceSecond)

open QAlgorithms.Entanglement (partialTransposeFirst)

open QAlgorithms.Papers.Independent.Dependency50.P07 (bipartitePower)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

open QAlgorithms.Papers.Independent.Gap48.P26 (entropyBits)


theorem g74l_coef_le {I : Type} (X : Matrix I I ℂ) (i j : I) :
    ENNReal.ofReal ‖X i j‖ ≤ traceSize X := by
  unfold traceSize
  refine le_iInf fun e => ENNReal.ofReal_le_ofReal ?_
  rw [e.coefficients i j]
  have hb : ∀ n, ‖e.left n i * star (e.right n j)‖ ≤ ‖e.left n‖ * ‖e.right n‖ := by
    intro n
    rw [norm_mul, norm_star]
    exact mul_le_mul (lp.norm_apply_le_norm two_ne_zero _ _)
      (lp.norm_apply_le_norm two_ne_zero _ _) (norm_nonneg _) (norm_nonneg _)
  have hs : Summable (fun n => ‖e.left n i * star (e.right n j)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb e.summable
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb e.summable)

theorem g74l_traceSize_zero {I : Type} : traceSize (0 : Matrix I I ℂ) = 0 := by
  refine le_antisymm ?_ bot_le
  refine iInf_le_of_le (⟨fun _ => 0, fun _ => 0, by simp, by intro i j; simp⟩ :
    QAlgorithms.Papers.Independent.Dependency50.P33.NuclearExpansion (0 : Matrix I I ℂ)) ?_
  simp

theorem g74l_coef_tendsto {I : Type} (X : Matrix I I ℂ) (P : ℕ → Matrix I I ℂ)
    (h : Tendsto (fun N => traceSize (X - P N)) atTop (𝓝 0)) (i j : I) :
    Tendsto (fun N => P N i j) atTop (𝓝 (X i j)) := by
  have h1 : Tendsto (fun N => ENNReal.ofReal ‖(X - P N) i j‖) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => bot_le) (fun N => g74l_coef_le _ i j)
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
  simp only [Function.comp_def, ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_zero] at h2
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine h2.congr (fun N => ?_)
  rw [Matrix.sub_apply, norm_sub_rev]

/-- the two-coordinate test functional -/
def g74l_G {I : Type} (i j : I) (z1 z2 : ℂ) (Y : Matrix I I ℂ) : ℂ :=
  star z1 * Y i i * z1 + star z1 * Y i j * z2 + star z2 * Y j i * z1 + star z2 * Y j j * z2

theorem g74l_G_rankOne {I : Type} (i j : I) (z1 z2 : ℂ) (w : Hilbert I) :
    g74l_G i j z1 z2 (rankOne w) =
      ((Complex.normSq (star z1 * w i + star z2 * w j) : ℝ) : ℂ) := by
  rw [← Complex.mul_conj]
  simp only [g74l_G, QAlgorithms.Papers.Independent.Dependency50.P33.rankOne, map_add,
    map_mul, Complex.star_def, Complex.conj_conj]
  ring

theorem g74l_parallel {I : Type} (u : Hilbert I)
    (e : QAlgorithms.Papers.Independent.Next46.P42.PureDecomposition I)
    (hX : e.hasAverage (rankOne u)) (m : ℕ) (hm : e.weight m ≠ 0) (v : Hilbert I)
    (hv : (e.state m).val.coefficients = rankOne v) (i j : I) :
    v i * u j = u i * v j := by
  set z1 : ℂ := star (u j) with hz1
  set z2 : ℂ := - star (u i) with hz2
  have hP := g74l_coef_tendsto (rankOne u) (fun N => ∑ n ∈ Finset.range N,
    (((e.weight n : ℝ) : ℂ) • (e.state n).val.coefficients)) hX
  have hPij : ∀ N a b, (∑ n ∈ Finset.range N,
      (((e.weight n : ℝ) : ℂ) • (e.state n).val.coefficients)) a b =
      ∑ n ∈ Finset.range N, ((e.weight n : ℝ) : ℂ) * (e.state n).val.coefficients a b := by
    intro N a b
    simp [Matrix.sum_apply]
  have hG : ∀ N, g74l_G i j z1 z2 (∑ n ∈ Finset.range N,
      (((e.weight n : ℝ) : ℂ) • (e.state n).val.coefficients)) =
      ∑ n ∈ Finset.range N, ((e.weight n : ℝ) : ℂ) *
        g74l_G i j z1 z2 (e.state n).val.coefficients := by
    intro N
    simp only [g74l_G, hPij, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hpure : ∀ n, ∃ r : ℝ, 0 ≤ r ∧
      g74l_G i j z1 z2 (e.state n).val.coefficients = (r : ℂ) := by
    intro n
    obtain ⟨w, _, hw⟩ := (e.state n).property
    exact ⟨_, Complex.normSq_nonneg _, by rw [hw, g74l_G_rankOne]⟩
  choose r hr0 hr using hpure
  have hlim : Tendsto (fun N => (g74l_G i j z1 z2 (∑ n ∈ Finset.range N,
      (((e.weight n : ℝ) : ℂ) • (e.state n).val.coefficients))).re) atTop
      (𝓝 (g74l_G i j z1 z2 (rankOne u)).re) := by
    apply (Complex.continuous_re.tendsto _).comp
    unfold g74l_G
    exact ((((tendsto_const_nhds.mul (hP i i)).mul tendsto_const_nhds).add
      ((tendsto_const_nhds.mul (hP i j)).mul tendsto_const_nhds)).add
      ((tendsto_const_nhds.mul (hP j i)).mul tendsto_const_nhds)).add
      ((tendsto_const_nhds.mul (hP j j)).mul tendsto_const_nhds)
  have hX0 : (g74l_G i j z1 z2 (rankOne u)).re = 0 := by
    rw [g74l_G_rankOne]
    have : star z1 * u i + star z2 * u j = 0 := by
      simp only [hz1, hz2, star_neg, star_star]; ring
    rw [this]; simp
  have hre : ∀ N, (g74l_G i j z1 z2 (∑ n ∈ Finset.range N,
      (((e.weight n : ℝ) : ℂ) • (e.state n).val.coefficients))).re =
      ∑ n ∈ Finset.range N, (e.weight n : ℝ) * r n := by
    intro N
    rw [hG, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [hr n]
    simp
  have hge : ∀ N, m < N → (e.weight m : ℝ) * r m ≤ (g74l_G i j z1 z2 (∑ n ∈ Finset.range N,
      (((e.weight n : ℝ) : ℂ) • (e.state n).val.coefficients))).re := by
    intro N hN
    rw [hre]
    exact Finset.single_le_sum (f := fun n => (e.weight n : ℝ) * r n)
      (fun n _ => mul_nonneg (NNReal.coe_nonneg _) (hr0 n)) (Finset.mem_range.mpr hN)
  have hle : (e.weight m : ℝ) * r m ≤ 0 := by
    rw [← hX0]
    exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨m + 1, fun N hN => hge N (by omega)⟩)
  have hw : 0 < (e.weight m : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hm)
  have hrm : r m = 0 := by nlinarith [hr0 m]
  have h0 : g74l_G i j z1 z2 (rankOne v) = 0 := by rw [← hv, hr m, hrm]; simp
  rw [g74l_G_rankOne, Complex.ofReal_eq_zero, Complex.normSq_eq_zero] at h0
  simp only [hz1, hz2, star_neg, star_star] at h0
  linear_combination h0

theorem g74l_rankOne_eq {I : Type} (u v : Hilbert I) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : ∀ i j, v i * u j = u i * v j) : rankOne v = rankOne u := by
  obtain ⟨i0, hi0⟩ : ∃ i0, u i0 ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : u = 0 := lp.ext (funext fun i => by simp [hall i])
    rw [this, norm_zero] at hu
    exact zero_ne_one hu
  set c : ℂ := v i0 / u i0 with hc
  have hvi : ∀ i, v i = c * u i := by
    intro i
    have := h i i0
    rw [hc]
    field_simp
    linear_combination this
  have hvc : v = c • u := lp.ext (funext fun i => by simp [hvi i])
  have hcn : ‖c‖ = 1 := by
    rw [hvc, norm_smul, hu, mul_one] at hv
    exact hv
  have hcc : c * star c = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hcn]
    simp
  funext i j
  simp only [QAlgorithms.Papers.Independent.Dependency50.P33.rankOne, hvi, star_mul]
  linear_combination (u i * star (u j)) * hcc

theorem g74l_eof_pure (sigma : PureState (ℕ × ℕ)) :
    QAlgorithms.Papers.Independent.Next46.P42.countableEof sigma.val.coefficients =
      QAlgorithms.Papers.Independent.Frontier18.P07.extendedEntropyNats
        (traceSecond sigma.val.coefficients) := by
  apply le_antisymm
  · let e0 : QAlgorithms.Papers.Independent.Next46.P42.PureDecomposition (ℕ × ℕ) :=
      { weight := fun n => if n = 0 then 1 else 0
        summable := by
          apply summable_of_ne_finset_zero (s := {0})
          intro n hn
          simp at hn
          simp [hn]
        mass := by
          rw [tsum_eq_single 0]
          · simp
          · intro n hn; simp [hn]
        state := fun _ => sigma }
    have h0 : e0.hasAverage sigma.val.coefficients := by
      apply tendsto_atTop_of_eventually_const (i₀ := 1)
      intro N hN
      rw [Finset.sum_eq_single 0]
      · simp [e0, g74l_traceSize_zero]
      · intro n _ hn; simp [e0, hn]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    refine iInf_le_of_le ⟨e0, h0⟩ (le_of_eq ?_)
    rw [tsum_eq_single 0]
    · simp [e0]
    · intro n hn; simp [e0, hn]
  · refine le_iInf fun ⟨e, he⟩ => ?_
    obtain ⟨u, hu, hX⟩ := sigma.property
    rw [hX] at he
    have heq : ∀ n, e.weight n ≠ 0 →
        (e.state n).val.coefficients = sigma.val.coefficients := by
      intro n hn
      obtain ⟨v, hv1, hv⟩ := (e.state n).property
      rw [hv, hX]
      apply g74l_rankOne_eq u v hu hv1
      intro i j
      exact g74l_parallel u e he n hn v hv i j
    have hs1 : ∑' n, e.weight n = 1 := by
      apply NNReal.coe_injective
      rw [NNReal.coe_tsum]
      simpa using e.mass
    have hsum1 : ∑' n, (e.weight n : ℝ≥0∞) = 1 := by
      rw [← ENNReal.coe_tsum (NNReal.summable_coe.mp e.summable), hs1]
      simp
    apply le_of_eq
    conv_lhs => rw [← one_mul (QAlgorithms.Papers.Independent.Frontier18.P07.extendedEntropyNats
      (traceSecond sigma.val.coefficients)), ← hsum1, ← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro n
    by_cases hn : e.weight n = 0
    · simp [hn]
    · rw [heq n hn]

theorem solution (h : HamiltonianData) (M : ℝ) (hM : 0 < M)
    (sigma : PureState (ℕ × ℕ)) (hsigma : sigma.val ∈ energyBound h M) :
    countableFormationBits sigma.val.coefficients = marginalEntropy sigma.val.coefficients := by
  unfold countableFormationBits marginalEntropy entropyBits
  rw [g74l_eof_pure]

end
