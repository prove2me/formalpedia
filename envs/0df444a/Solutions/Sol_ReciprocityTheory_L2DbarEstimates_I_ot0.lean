-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.ot0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:41.239061+00:00
-- url     : https://prove2.me/submissions/ca8e7bbf-dbc2-4fd5-b974-1de2499a5883

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Ot0
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_continuous_weightFunction
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_lintegral_dyadic_shell_bound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_lintegral_le_sum_setLIntegral
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_localExtension_eq_mul_jacobian
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_localExtension_eq_zero_off
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_mem_zeroSet_of_weight_nonpos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_not_mem_neighborhood_of_ne
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sqrt_add_sq_le_weighted
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_volume_singleton_eq_zero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_weightFunction_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M]
    (hF : FixedStatement n M) (hS : ShellStatement n M) (hL : LocalStatement n M)
    (hCut : CutoffStatement) : JacobianInterpolationStatement n M := by
  intro X g ph ph2 r j c hn hj hr hg hph hphL hph2 hph2L hbd hfin0 hJ0
  have hfin : (zeroSet n g).Finite := hfin0
  have hJ : ∀ p ∈ zeroSet n g, jac n X.z g p ≠ 0 := fun p hp => hJ0 p hp
  have hz := X.isLocalHomeomorph
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = Real.pi ^ n / (Nat.factorial (n - 1) : ℝ) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = r ^ (2 * n) := ⟨_, rfl⟩
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hRpos : 0 < R := by rw [hR]; positivity
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg = ∑ p ∈ hfin.toFinset,
      ‖c p‖ ^ 2 * Real.exp (-ph2 p - (j : ℝ) * ph p) := ⟨_, rfl⟩
  have hsum : (∑' x : {x : M // ∀ i, g i x = 0},
      ENNReal.ofReal (‖c x‖ ^ 2 * Real.exp (-ph2 x - (j : ℝ) * ph x))) = ENNReal.ofReal Sg := by
    rw [hSg, ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity), ← Finset.tsum_subtype]
    exact (Equiv.subtypeEquivRight (fun x => (hfin.mem_toFinset).symm)).tsum_eq
      (fun y => ENNReal.ofReal (‖c y.1‖ ^ 2 * Real.exp (-ph2 y.1 - (j : ℝ) * ph y.1)))
  by_cases hS0 : Sg = 0
  · have hc : ∀ p ∈ zeroSet n g, c p = 0 := by
      intro p hp
      rw [hSg] at hS0
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => by positivity)).1 hS0 p
        (hfin.mem_toFinset.2 hp)
      have h2 : ‖c p‖ ^ 2 = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · exact absurd h (Real.exp_pos _).ne'
      simpa using h2
    refine ⟨fun _ => 0, fun e _ => differentiableOn_const 0, fun x hx => ?_, ?_⟩
    · simp [hc x hx]
    · simp
  have hSpos : 0 < Sg := lt_of_le_of_ne
    (by rw [hSg]; exact Finset.sum_nonneg fun p _ => by positivity) (Ne.symm hS0)
  have hN0 : ∀ p : M, ∃ N : Set M, p ∈ zeroSet n g → IsOpen N ∧ p ∈ N ∧
      ∀ τ : ℝ, 0 < τ → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫⁻ x in N ∩ shell n g ph r ε, ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 *
          Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
        ENNReal.ofReal ((1 + τ) * (Q * Real.log 2) * R * Real.exp (-ph2 p - (j : ℝ) * ph p)) := by
    intro p
    by_cases hp : p ∈ zeroSet n g
    · obtain ⟨N, h1, h2, h3⟩ := hS X.z g ph ph2 r j p hn hz hg hph hph2 hr hp (hJ p hp)
      rw [← hQ, ← hR] at h3
      exact ⟨N, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨Set.univ, fun h => absurd h hp⟩
  choose N hN using hN0
  obtain ⟨W, m, hLD, hWN⟩ := hL X.z g ph r N hz hg hph hr hfin hJ
    (fun p hp => ⟨(hN p hp).1, (hN p hp).2.1⟩)
  obtain ⟨χ, hχ⟩ := hCut
  have hevm : Measurable (ev n g ph r) := (continuous_weightFunction n X.z hz g ph r hg hph).measurable
  have hWm : ∀ p ∈ zeroSet n g, MeasurableSet (W p) := fun p hp => (hLD.2 p hp).1.measurableSet

  have E1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ zeroSet n g,
      ∫⁻ x in N p ∩ shell n g ph r ε, ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 *
          Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
        ENNReal.ofReal ((1 + 1 / 200) * (Q * Real.log 2) * R *
          Real.exp (-ph2 p - (j : ℝ) * ph p)) :=
    (eventually_all_finite hfin).2 (fun p hp => (hN p hp).2.2 (1 / 200) (by norm_num))
  have E2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ p ∈ zeroSet n g, ∀ t : ℝ, 0 < t → t ≤ ε →
      ∫⁻ x in N p ∩ shell n g ph r t, ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 *
          Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
        ENNReal.ofReal ((1 + 1) * (Q * Real.log 2) * R * Real.exp (-ph2 p - (j : ℝ) * ph p)) := by
    refine (eventually_all_finite hfin).2 (fun p hp => ?_)
    obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 ((hN p hp).2.2 1 one_pos)
    filter_upwards [Ioo_mem_nhdsGT hu] with ε hε t ht htε
    exact hsub ⟨ht, htε.trans_lt hε.2⟩
  have E3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have E4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / 100 :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually_lt_const (by norm_num)
  have E5 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε ^ 2 < m := by
    have h : Tendsto (fun ε : ℝ => 2 * ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have hc : Continuous (fun ε : ℝ => 2 * ε ^ 2) := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact h.eventually_lt_const hLD.1
  have E6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 + ε ^ 2) ^ n < 1 + 1 / 200 := by
    have h : Tendsto (fun ε : ℝ => (1 + ε ^ 2) ^ n) (𝓝[>] 0) (𝓝 1) := by
      have hc : Continuous (fun ε : ℝ => (1 + ε ^ 2) ^ n) := by fun_prop
      have := (hc.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact h.eventually_lt_const (by norm_num)
  obtain ⟨ε, hε1, hε2, hε0, hε100, hεm, hεn⟩ :=
    (E1.and (E2.and (E3.and (E4.and (E5.and E6))))).exists
  obtain ⟨F, hFh, hFS, hFb⟩ := hF X g ph ph2 r j c W m χ ε hn hg hph hphL hph2 hph2L hr hj hbd
    hfin hJ hLD hχ hε0 (by linarith) hεm
  refine ⟨F, hFh, fun x hx => hFS x hx, ?_⟩

  have hG : ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
      Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
      ENNReal.ofReal ((1 + 1 / 200) * (Q * Real.log 2) * R * Sg) := by
    calc _ ≤ ∑ p ∈ hfin.toFinset, ∫⁻ x in W p, ENNReal.ofReal (‖c p‖ ^ 2) *
          ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) *
            ev n g ph r x ^ (-(n : ℝ))) ∂(vol n X.z).restrict (shell n g ph r ε) := by
          refine lintegral_le_sum_setLIntegral _ _ _ (fun p hp => hWm p (hfin.mem_toFinset.1 hp)) _ _ ?_ ?_
          · intro x hx
            by_contra hno
            push_neg at hno
            apply hx
            rw [localExtension_eq_zero_off n X.z g c W (fun p hp => hno p (hfin.mem_toFinset.2 hp))]
            simp
          · intro p hp x hx
            rw [localExtension_eq_mul_jacobian n X.z g ph r c W m hLD hfin (hfin.mem_toFinset.1 hp) hx,
              ← ENNReal.ofReal_mul (sq_nonneg _)]
            apply le_of_eq
            congr 1
            rw [norm_mul]
            ring
      _ ≤ ∑ p ∈ hfin.toFinset, ENNReal.ofReal (‖c p‖ ^ 2) *
          ENNReal.ofReal ((1 + 1 / 200) * (Q * Real.log 2) * R *
            Real.exp (-ph2 p - (j : ℝ) * ph p)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := hfin.mem_toFinset.1 hp
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.restrict_restrict (hWm p hp')]
          gcongr
          exact (lintegral_mono_set (Set.inter_subset_inter_left _ (hWN p hp'))).trans (hε1 p hp')
      _ = ENNReal.ofReal ((1 + 1 / 200) * (Q * Real.log 2) * R * Sg) := by
          rw [hSg, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          · refine Finset.sum_congr rfl fun p _ => ?_
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            congr 1
            ring
          · intro p _
            positivity

  have hF0 : otNorm n X.z ph ph2 j (cutExt n X.z g ph r c W χ ε) ≤
      ENNReal.ofReal (2 * ((1 + 1) * (Q * Real.log 2) * R) * ε ^ 2 * Sg) := by
    unfold otNorm
    calc _ ≤ ∑ p ∈ hfin.toFinset, ∫⁻ x in W p ∩ {x | ev n g ph r x < ε ^ 2},
          ENNReal.ofReal (‖c p‖ ^ 2) * ENNReal.ofReal (‖jac n X.z g x‖ ^ 2 *
            Real.exp (-ph2 x - ((n : ℝ) + j) * ph x)) ∂vol n X.z := by
          refine lintegral_le_sum_setLIntegral _ _ _ (fun p hp => (hWm p (hfin.mem_toFinset.1 hp)).inter
            (measurableSet_lt hevm measurable_const)) _ _ ?_ ?_
          · intro x hx
            have hne : cutExt n X.z g ph r c W χ ε x ≠ 0 := by
              intro h0
              apply hx
              simp [h0]
            unfold cutExt at hne
            have hχne : χ (ev n g ph r x / ε ^ 2) ≠ 0 := fun h => hne (by simp [h])
            have hgne : gt n X.z g c W x ≠ 0 := fun h => hne (by simp [h])
            have hlt : ev n g ph r x < ε ^ 2 := by
              by_contra hge
              push_neg at hge
              exact hχne (hχ.2.2.1 _ ((one_le_div (by positivity)).2 hge))
            by_contra hno
            push_neg at hno
            exact hgne (localExtension_eq_zero_off n X.z g c W
              (fun p hp hxp => hno p (hfin.mem_toFinset.2 hp) ⟨hxp, hlt⟩))
          · intro p hp x hx
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            apply ENNReal.ofReal_le_ofReal
            unfold cutExt
            rw [localExtension_eq_mul_jacobian n X.z g ph r c W m hLD hfin (hfin.mem_toFinset.1 hp) hx.1,
              norm_mul, norm_mul, Complex.norm_real]
            have h1 : ‖χ (ev n g ph r x / ε ^ 2)‖ ≤ 1 := by
              rw [Real.norm_eq_abs, abs_le]
              constructor <;> linarith [(hχ.2.2.2.1 (ev n g ph r x / ε ^ 2)).1,
                (hχ.2.2.2.1 (ev n g ph r x / ε ^ 2)).2]
            have hE := Real.exp_pos (-ph2 x - ((n : ℝ) + j) * ph x)
            have h2 : (‖χ (ev n g ph r x / ε ^ 2)‖ * (‖c p‖ * ‖jac n X.z g x‖)) ^ 2 ≤
                (‖c p‖ * ‖jac n X.z g x‖) ^ 2 := by
              rw [mul_pow]
              exact mul_le_of_le_one_left (sq_nonneg _)
                (by nlinarith [norm_nonneg (χ (ev n g ph r x / ε ^ 2))])
            calc _ ≤ (‖c p‖ * ‖jac n X.z g x‖) ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) :=
                  mul_le_mul_of_nonneg_right h2 hE.le
              _ = _ := by ring
      _ ≤ ∑ p ∈ hfin.toFinset, ENNReal.ofReal (‖c p‖ ^ 2) * ENNReal.ofReal
          (2 * ((1 + 1) * (Q * Real.log 2) * R * Real.exp (-ph2 p - (j : ℝ) * ph p)) * ε ^ 2) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp' := hfin.mem_toFinset.1 hp
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          gcongr
          refine lintegral_dyadic_shell_bound (vol n X.z) (ev n g ph r) hevm (weightFunction_nonneg n g ph r) (W p)
            (hWm p hp') (fun x => ‖jac n X.z g x‖ ^ 2 * Real.exp (-ph2 x - ((n : ℝ) + j) * ph x))
            (fun x => by positivity) n hn ε _ hε0 (by linarith) (by positivity) ?_ ?_
          · refine measure_mono_null (fun x hx => ?_) (volume_singleton_eq_zero n hn X.z hz p)
            have hxS := mem_zeroSet_of_weight_nonpos n g ph r hr.ne' x hx.2
            by_contra hxp
            exact not_mem_neighborhood_of_ne n g ph r W m hLD hp' hxS hxp hx.1 ((hLD.2 x hxS).2.1)
          · intro t ht htε
            exact (lintegral_mono_set (Set.inter_subset_inter_left _ (hWN p hp'))).trans
              (hε2 p hp' t ht htε)
      _ = _ := by
          rw [hSg, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
          · refine Finset.sum_congr rfl fun p _ => ?_
            rw [← ENNReal.ofReal_mul (sq_nonneg _)]
            congr 1
            ring
          · intro p _
            positivity

  have hA0 : 0 ≤ 2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72 := by positivity
  have hxG : ENNReal.ofReal (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72) *
      ∫⁻ x in shell n g ph r ε, ENNReal.ofReal (‖gt n X.z g c W x‖ ^ 2 *
        Real.exp (-ph2 x - ((n : ℝ) + j) * ph x) * ev n g ph r x ^ (-(n : ℝ))) ∂vol n X.z ≤
      ENNReal.ofReal (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72 *
        ((1 + 1 / 200) * (Q * Real.log 2) * R * Sg)) := by
    rw [ENNReal.ofReal_mul hA0]
    gcongr
  have hmain := sqrt_add_sq_le_weighted _ _ _ _ (by positivity) (by positivity) hxG hF0
  have hε2' : ε ^ 2 ≤ 1 / 10000 := by nlinarith
  have hcoef : 101 / 100 * (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72 * ((1 + 1 / 200) * Real.log 2))
      + 101 * (2 * ((1 + 1) * Real.log 2) * ε ^ 2) ≤ 280 := by
    have he := Real.exp_one_lt_d9
    have hl := Real.log_two_lt_d9
    have hu0 : 0 ≤ (1 + ε ^ 2) ^ n := by positivity
    have h1 : Real.exp 1 * (1 + ε ^ 2) ^ n ≤ 2.7182818286 * (1 + 1 / 200) :=
      mul_le_mul he.le hεn.le hu0 (by norm_num)
    have h2 : Real.exp 1 * (1 + ε ^ 2) ^ n * Real.log 2 ≤
        2.7182818286 * (1 + 1 / 200) * 0.6931471808 :=
      mul_le_mul h1 hl.le hlog.le (by norm_num)
    have h3 : Real.log 2 * ε ^ 2 ≤ 0.6931471808 * (1 / 10000) :=
      mul_le_mul hl.le hε2' (sq_nonneg _) (by norm_num)
    nlinarith
  have hconst : 0 ≤ ohsawaTakegoshiConstant n r := by unfold ohsawaTakegoshiConstant; positivity
  calc _ ≤ _ := hFb
    _ ≤ _ := hmain
    _ ≤ ENNReal.ofReal (ohsawaTakegoshiConstant n r * Sg) := by
        apply ENNReal.ofReal_le_ofReal
        have hy : 0 ≤ Q * R * Sg := by positivity
        have hot : ohsawaTakegoshiConstant n r = 280 * Q * R := by rw [hQ, hR]; unfold ohsawaTakegoshiConstant; ring
        rw [hot]
        calc _ = (101 / 100 * (2 * Real.exp 1 * (1 + ε ^ 2) ^ n * 72 * ((1 + 1 / 200) *
              Real.log 2)) + 101 * (2 * ((1 + 1) * Real.log 2) * ε ^ 2)) * (Q * R * Sg) := by ring
          _ ≤ 280 * (Q * R * Sg) := mul_le_mul_of_nonneg_right hcoef hy
          _ = _ := by ring
    _ = _ := by rw [ENNReal.ofReal_mul hconst, hsum]
end ReciprocityTheory.L2DbarEstimates.I
