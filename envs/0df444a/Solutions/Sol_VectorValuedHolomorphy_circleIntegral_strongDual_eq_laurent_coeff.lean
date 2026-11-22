-- Prove2me | solution 1 for VectorValuedHolomorphy.circleIntegral_strongDual_eq_laurent_coeff
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:17:52.49367+00:00
-- url     : https://prove2.me/submissions/5941028d-923f-4572-9685-264651b67e4e

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_circleIntegral_strongDual_eq_laurent_coeff

open scoped Pointwise Uniformity

/-- A continuous linear functional composed with a holomorphic vector-valued function is
holomorphic. -/
theorem differentiableOn_strongDual_comp {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    {U : Set ℂ} {f : ℂ → E} (hf : DifferentiableOn ℂ f U) (ℓ : StrongDual ℂ E) :
    DifferentiableOn ℂ (fun z => ℓ (f z)) U := by
  intro z hz
  obtain ⟨f', hf'⟩ := hf z hz
  refine ⟨ℓ.comp f', HasFDerivWithinAt.of_isLittleOTVS ?_⟩
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, map_sub]
    using ℓ.isBigOTVS_comp.trans_isLittleOTVS hf'.isLittleOTVS

/-- Multiplying a uniformly convergent sequence of functions with values in a topological vector
space by a bounded scalar function preserves uniform convergence. -/
theorem tendstoUniformlyOn_smul_of_bounded {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    {F : ℕ → ℂ → E} {f : ℂ → E} {K : Set ℂ} {c : ℂ → ℂ} {M : ℝ}
    (hc : ∀ z ∈ K, ‖c z‖ ≤ M) (h : TendstoUniformlyOn F f atTop K) :
    TendstoUniformlyOn (fun n z => c z • F n z) (fun z => c z • f z) atTop K := by
  intro u hu
  rw [uniformity_eq_comap_nhds_zero E, Filter.mem_comap] at hu
  obtain ⟨V, hV, hVu⟩ := hu
  obtain ⟨W, ⟨hW, hWb⟩, hWV⟩ := (nhds_basis_balanced ℂ E).mem_iff.mp hV
  have hM' : (0 : ℝ) < max M 1 := lt_max_of_lt_right one_pos
  have hne : ((max M 1 : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hM'.ne')
  have hW' : ((max M 1 : ℝ) : ℂ)⁻¹ • W ∈ 𝓝 (0 : E) := (set_smul_mem_nhds_zero_iff hne).mpr hW
  have hu' : {x : E × E | x.2 - x.1 ∈ ((max M 1 : ℝ) : ℂ)⁻¹ • W} ∈ 𝓤 E := by
    rw [uniformity_eq_comap_nhds_zero E]
    exact Filter.preimage_mem_comap hW'
  filter_upwards [h _ hu'] with n hn z hz
  refine hVu (hWV ?_)
  obtain ⟨w, hw, hwe⟩ := hn z hz
  have hwe' : ((max M 1 : ℝ) : ℂ)⁻¹ • w = F n z - f z := hwe
  show c z • F n z - c z • f z ∈ W
  rw [← smul_sub, ← hwe', smul_smul]
  refine hWb.smul_mem ?_ hw
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hM'.le, ← div_eq_mul_inv,
    div_le_one hM']
  exact (hc z hz).trans (le_max_left _ _)

/-- A sequence of entire functions which converges uniformly on a circle and pointwise inside it
has a limit which is holomorphic on the open disc (maximum modulus principle and the Weierstrass
convergence theorem). -/
theorem differentiableOn_ball_of_tendstoUniformlyOn_sphere {φ : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    {z₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hφ : ∀ m, Differentiable ℂ (φ m))
    (hunif : TendstoUniformlyOn φ G atTop (sphere z₀ ρ))
    (hpt : ∀ z ∈ ball z₀ ρ, Tendsto (fun m => φ m z) atTop (𝓝 (G z))) :
    DifferentiableOn ℂ G (ball z₀ ρ) := by
  have hU : TendstoUniformlyOn φ G atTop (ball z₀ ρ) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hC := hunif.uniformCauchySeqOn
    rw [Metric.uniformCauchySeqOn_iff] at hC
    obtain ⟨M, hM⟩ := hC (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop M] with m hm z hz
    have hb : ∀ n ≥ M, ‖φ m z - φ n z‖ ≤ ε / 2 := by
      intro n hn
      have hd : DiffContOnCl ℂ (fun w => φ m w - φ n w) (ball z₀ ρ) :=
        ((hφ m).sub (hφ n)).diffContOnCl
      refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd (fun w hw => ?_)
        (subset_closure hz)
      rw [frontier_ball z₀ hρ.ne'] at hw
      have := hM m hm n hn w hw
      rw [dist_eq_norm] at this
      exact this.le
    have hlim : Tendsto (fun n => ‖φ m z - φ n z‖) atTop (𝓝 ‖φ m z - G z‖) :=
      (tendsto_const_nhds.sub (hpt z hz)).norm
    have hle : ‖φ m z - G z‖ ≤ ε / 2 := le_of_tendsto hlim (eventually_atTop.2 ⟨M, hb⟩)
    rw [dist_comm, dist_eq_norm]
    linarith
  exact hU.tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun m => (hφ m).differentiableOn) isOpen_ball

/-- Cauchy's theorem with one singular point: if `F = P + Q` near `z₀` with `Q` holomorphic at `z₀`
and `P` holomorphic off `z₀`, then `∮ F = ∮ P` over any circle enclosing `z₀` whose closed disc
lies in the domain of holomorphy of `F` minus `z₀`. -/
theorem circleIntegral_eq_of_decomp {U : Set ℂ} (hU : IsOpen U) {F P Q : ℂ → ℂ}
    {z₀ c : ℂ} {ρ : ℝ} (hcρ : closedBall c ρ ⊆ U) (hz₀ : z₀ ∈ ball c ρ)
    (hF : DifferentiableOn ℂ F (U \ {z₀})) (hPd : ∀ z, z ≠ z₀ → DifferentiableAt ℂ P z)
    (hQ : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ Q z)
    (hFPQ : ∀ᶠ z in 𝓝[≠] z₀, F z = P z + Q z) :
    (∮ z in C(c, ρ), F z) = ∮ z in C(c, ρ), P z := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt hz₀
  have hsph : ∀ z ∈ sphere c ρ, z ≠ z₀ := by
    intro z hz h
    rw [h] at hz
    exact absurd (mem_ball.mp hz₀) (by rw [mem_sphere.mp hz]; exact lt_irrefl _)
  have hFd : ∀ z ∈ U, z ≠ z₀ → DifferentiableAt ℂ F z := by
    intro z hzU hz
    exact (hF z ⟨hzU, hz⟩).differentiableAt
      ((hU.sdiff isClosed_singleton).mem_nhds ⟨hzU, hz⟩)
  set G : ℂ → ℂ := Function.update (fun z => F z - P z) z₀ (Q z₀) with hG
  have hGd : ∀ z ∈ closedBall c ρ, DifferentiableAt ℂ G z := by
    intro z hz
    by_cases hzz : z = z₀
    · subst hzz
      have hev : G =ᶠ[𝓝 z] Q := by
        have h1 : ∀ᶠ w in 𝓝 z, w ≠ z → F w = P w + Q w := by
          have := hFPQ
          rw [eventually_nhdsWithin_iff] at this
          exact this
        filter_upwards [h1] with w hw
        by_cases hwz : w = z
        · rw [hwz, hG, Function.update_self]
        · rw [hG, Function.update_of_ne hwz]
          show F w - P w = Q w
          rw [hw hwz]
          ring
      exact hQ.self_of_nhds.congr_of_eventuallyEq hev
    · have hev : G =ᶠ[𝓝 z] fun w => F w - P w := by
        filter_upwards [isOpen_compl_singleton.mem_nhds hzz] with w hw
        rw [hG, Function.update_of_ne hw]
      exact ((hFd z (hcρ hz) hzz).sub (hPd z hzz)).congr_of_eventuallyEq hev
  have hGc : ContinuousOn G (closedBall c ρ) := fun z hz =>
    (hGd z hz).continuousAt.continuousWithinAt
  have hzero : (∮ z in C(c, ρ), G z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hρ.le
      Set.countable_empty hGc (fun z hz => hGd z (ball_subset_closedBall hz.1))
  have hcongr : (∮ z in C(c, ρ), G z) = ∮ z in C(c, ρ), (F z - P z) := by
    refine circleIntegral.integral_congr hρ.le fun z hz => ?_
    show G z = F z - P z
    rw [hG, Function.update_of_ne (hsph z hz)]
  have hFi : CircleIntegrable F c ρ := by
    refine ContinuousOn.circleIntegrable hρ.le fun z hz => ?_
    exact (hFd z (hcρ (sphere_subset_closedBall hz)) (hsph z hz)).continuousAt.continuousWithinAt
  have hPi : CircleIntegrable P c ρ := by
    refine ContinuousOn.circleIntegrable hρ.le fun z hz => ?_
    exact (hPd z (hsph z hz)).continuousAt.continuousWithinAt
  rw [hcongr, circleIntegral.integral_sub hFi hPi, sub_eq_zero] at hzero
  exact hzero

/-- The circle integral of the finite part `∑_{j < (n+1)⁺} bⱼ (z - z₀)^{j - (n+1)}` of a Laurent
series around a circle enclosing `z₀` is `2πi bₙ` (and `0` if `n < 0`). -/
theorem circleIntegral_zpow_sum {z₀ c : ℂ} {ρ : ℝ} (hz₀ : z₀ ∈ ball c ρ) (b : ℕ → ℂ) (n : ℤ) :
    (∮ z in C(c, ρ), ∑ j ∈ Finset.range (n + 1).toNat, b j * (z - z₀) ^ ((j : ℤ) - (n + 1)))
      = 2 * π * Complex.I * (if 0 ≤ n then b n.toNat else 0) := by
  have hρ : 0 < ρ := dist_nonneg.trans_lt hz₀
  have hns : z₀ ∉ sphere c |ρ| := by
    rw [abs_of_pos hρ]
    intro h
    exact absurd (mem_ball.mp hz₀) (by rw [mem_sphere.mp h]; exact lt_irrefl _)
  have hint : ∀ j : ℕ,
      CircleIntegrable (fun z => b j * (z - z₀) ^ ((j : ℤ) - (n + 1))) c ρ := fun j =>
    (circleIntegrable_sub_zpow_iff.mpr (Or.inr (Or.inr hns))).const_smul (a := b j)
  rw [circleIntegral.integral_fun_sum (fun j _ => hint j)]
  simp only [circleIntegral.integral_const_mul]
  have hterm : ∀ j : ℕ, (∮ z in C(c, ρ), (z - z₀) ^ ((j : ℤ) - (n + 1)))
      = if (j : ℤ) = n then 2 * π * Complex.I else 0 := by
    intro j
    split_ifs with h
    · have h1 : (j : ℤ) - (n + 1) = -1 := by omega
      rw [h1]
      simp only [zpow_neg_one]
      exact circleIntegral.integral_sub_inv_of_mem_ball hz₀
    · exact circleIntegral.integral_sub_zpow_of_ne (by omega) _ _ _
  simp only [hterm, mul_ite, mul_zero]
  split_ifs with hn
  · rw [Finset.sum_eq_single n.toNat]
    · rw [if_pos (Int.toNat_of_nonneg hn)]
      ring
    · intro j _ hj
      rw [if_neg]
      intro h
      apply hj
      omega
    · intro h
      exfalso
      apply h
      rw [Finset.mem_range]
      omega
  · refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_range] at hj
    omega

/-- The regular part of a Laurent series converging uniformly on the compact subsets of a
punctured disc is holomorphic on the whole disc. -/
theorem regular_part {z₀ : ℂ} {F : ℂ → ℂ} {b : ℕ → ℂ} {n : ℤ} {R : ℝ}
    (hS : ∀ K : Set ℂ, IsCompact K → K ⊆ ball z₀ R \ {z₀} →
      TendstoUniformlyOn
        (fun (m : ℕ) (z : ℂ) => ∑ j ∈ Finset.range m, b j * (z - z₀) ^ ((j : ℤ) - (n + 1)))
        F atTop K) :
    ∃ Q : ℂ → ℂ, DifferentiableOn ℂ Q (ball z₀ R) ∧ ∀ z ∈ ball z₀ R, z ≠ z₀ →
      F z = (∑ j ∈ Finset.range (n + 1).toNat, b j * (z - z₀) ^ ((j : ℤ) - (n + 1))) + Q z := by
  set p := (n + 1).toNat with hp
  set e := (-(n + 1)).toNat with he
  have hpe : ∀ i : ℕ, ((p + i : ℕ) : ℤ) - (n + 1) = ((i + e : ℕ) : ℤ) := by
    intro i
    have := Int.toNat_sub_toNat_neg (n + 1)
    push_cast
    omega
  set S : ℕ → ℂ → ℂ := fun m z => ∑ j ∈ Finset.range m, b j * (z - z₀) ^ ((j : ℤ) - (n + 1))
    with hSdef
  set P : ℂ → ℂ := fun z => ∑ j ∈ Finset.range p, b j * (z - z₀) ^ ((j : ℤ) - (n + 1)) with hP
  set φ : ℕ → ℂ → ℂ := fun m z => ∑ i ∈ Finset.range m, b (p + i) * (z - z₀) ^ (i + e) with hφ
  set Q : ℂ → ℂ := fun z => if z = z₀ then b p * 0 ^ e else F z - P z with hQ
  have hsplit : ∀ (m : ℕ) (z : ℂ), S (p + m) z = P z + φ m z := by
    intro m z
    simp only [hSdef, hP, hφ]
    rw [Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hpe i, zpow_natCast]
  have hφd : ∀ m, Differentiable ℂ (φ m) := by
    intro m
    simp only [hφ]
    fun_prop
  refine ⟨Q, ?_, ?_⟩
  · intro z hz
    obtain ⟨ρ', hzρ, hρR⟩ := exists_between (mem_ball.mp hz)
    have hρ' : 0 < ρ' := dist_nonneg.trans_lt hzρ
    have hsphere : sphere z₀ ρ' ⊆ ball z₀ R \ {z₀} := by
      intro w hw
      have hwd : dist w z₀ = ρ' := mem_sphere.mp hw
      refine ⟨mem_ball.mpr (hwd ▸ hρR), fun hwz => ?_⟩
      rw [Set.mem_singleton_iff.mp hwz, dist_self] at hwd
      exact hρ'.ne hwd
    have hunif : TendstoUniformlyOn φ Q atTop (sphere z₀ ρ') := by
      have h1 := hS _ (isCompact_sphere z₀ ρ') hsphere
      rw [Metric.tendstoUniformlyOn_iff] at h1 ⊢
      intro ε hε
      obtain ⟨M, hM⟩ := eventually_atTop.mp (h1 ε hε)
      refine eventually_atTop.mpr ⟨M, fun m hm w hw => ?_⟩
      have h2 := hM (p + m) (by omega) w hw
      have hwz : w ≠ z₀ := (hsphere hw).2
      have h3 : S (p + m) w = P w + φ m w := hsplit m w
      have h4 : Q w = F w - P w := by simp only [hQ, if_neg hwz]
      change dist (F w) (S (p + m) w) < ε at h2
      rw [h4, dist_eq_norm]
      rw [h3, dist_eq_norm] at h2
      have h5 : F w - P w - φ m w = F w - (P w + φ m w) := by ring
      rw [h5]
      exact h2
    have hpt : ∀ w ∈ ball z₀ ρ', Tendsto (fun m => φ m w) atTop (𝓝 (Q w)) := by
      intro w hw
      by_cases hwz : w = z₀
      · rw [hwz]
        have hQ0 : Q z₀ = b p * 0 ^ e := by simp only [hQ, if_pos rfl]
        rw [hQ0]
        refine tendsto_atTop_of_eventually_const (i₀ := 1) fun m hm => ?_
        simp only [hφ, sub_self]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro j _ hj
          rw [zero_pow (by omega), mul_zero]
        · intro h
          exact absurd (Finset.mem_range.mpr hm) h
      · have hsub : ({w} : Set ℂ) ⊆ ball z₀ R \ {z₀} := by
          rintro _ rfl
          exact ⟨ball_subset_ball hρR.le hw, hwz⟩
        have h1 := (hS {w} isCompact_singleton hsub).tendsto_at (Set.mem_singleton w)
        have h2 : Tendsto (fun m => S (m + p) w) atTop (𝓝 (F w)) :=
          (tendsto_add_atTop_iff_nat p).mpr h1
        have h3 := h2.sub_const (P w)
        have h4 : Q w = F w - P w := by simp only [hQ, if_neg hwz]
        rw [h4]
        refine Tendsto.congr (fun m => ?_) h3
        show S (m + p) w - P w = φ m w
        rw [add_comm, hsplit m w]
        ring
    have hd := differentiableOn_ball_of_tendstoUniformlyOn_sphere hρ' hφd hunif hpt
    exact (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball.mpr hzρ))).differentiableWithinAt
  · intro z _ hzz
    simp only [hQ, if_neg hzz]
    ring

/-- Scalar version: Laurent coefficients as circle integrals. -/
theorem circleIntegral_eq_laurent_coeff_scalar {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    {z₀ c : ℂ} {ρ : ℝ} (hcρ : closedBall c ρ ⊆ U) (hz₀ : z₀ ∈ ball c ρ)
    (hF : DifferentiableOn ℂ F (U \ {z₀})) {b : ℕ → ℂ} {n : ℤ} {R : ℝ} (hR : 0 < R)
    (hS : ∀ K : Set ℂ, IsCompact K → K ⊆ ball z₀ R \ {z₀} →
      TendstoUniformlyOn
        (fun (m : ℕ) (z : ℂ) => ∑ j ∈ Finset.range m, b j * (z - z₀) ^ ((j : ℤ) - (n + 1)))
        F atTop K) :
    (∮ z in C(c, ρ), F z) = 2 * π * Complex.I * (if 0 ≤ n then b n.toNat else 0) := by
  obtain ⟨Q, hQ, hFPQ⟩ := regular_part hS
  rw [circleIntegral_eq_of_decomp hU hcρ hz₀ hF
    (P := fun z => ∑ j ∈ Finset.range (n + 1).toNat, b j * (z - z₀) ^ ((j : ℤ) - (n + 1)))
    (Q := Q) ?_ ?_ ?_]
  · exact circleIntegral_zpow_sum hz₀ b n
  · intro z hz
    refine DifferentiableAt.fun_sum fun j _ => ?_
    exact (differentiableAt_const _).mul
      ((differentiableAt_id.sub_const z₀).zpow (Or.inl (sub_ne_zero.mpr hz)))
  · filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz
    exact hQ.differentiableAt (isOpen_ball.mem_nhds hz)
  · rw [eventually_nhdsWithin_iff]
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz hzz
    exact hFPQ z hz hzz

end Sol_VectorValuedHolomorphy_circleIntegral_strongDual_eq_laurent_coeff

open Sol_VectorValuedHolomorphy_circleIntegral_strongDual_eq_laurent_coeff

theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E} {z₀ c : ℂ} {ρ : ℝ}
    (hcρ : closedBall c ρ ⊆ U) (hz₀ : z₀ ∈ ball c ρ) (hf : DifferentiableOn ℂ f (U \ {z₀}))
    {N : ℕ} {a : ℕ → E} {R : ℝ} (hR : 0 < R)
    (ha : ∀ K : Set ℂ, IsCompact K → K ⊆ ball z₀ R \ {z₀} →
      TendstoUniformlyOn
        (fun (n : ℕ) (z : ℂ) => ∑ j ∈ Finset.range n, (z - z₀) ^ ((j : ℤ) - (N : ℤ)) • a j)
        f atTop K)
    (ℓ : StrongDual ℂ E) (k : ℤ) :
    (∮ z in C(c, ρ), ℓ (f z) / (z - z₀) ^ (k + 1)) =
      2 * π * Complex.I * ℓ (if 0 ≤ k + (N : ℤ) then a (k + (N : ℤ)).toNat else 0) := by
  have hF : DifferentiableOn ℂ (fun z => ℓ (f z) / (z - z₀) ^ (k + 1)) (U \ {z₀}) := by
    intro z hz
    have hzz : z - z₀ ≠ 0 := sub_ne_zero.mpr hz.2
    exact ((differentiableOn_strongDual_comp hf ℓ) z hz).div
      ((differentiableAt_id.sub_const z₀).zpow (Or.inl hzz)).differentiableWithinAt
      (zpow_ne_zero _ hzz)
  have hS : ∀ K : Set ℂ, IsCompact K → K ⊆ ball z₀ R \ {z₀} →
      TendstoUniformlyOn
        (fun (m : ℕ) (z : ℂ) => ∑ j ∈ Finset.range m,
          ℓ (a j) * (z - z₀) ^ ((j : ℤ) - ((k + (N : ℤ)) + 1)))
        (fun z => ℓ (f z) / (z - z₀) ^ (k + 1)) atTop K := by
    intro K hK hKs
    have h1 := ℓ.uniformContinuous.comp_tendstoUniformlyOn (ha K hK hKs)
    have hcont : ContinuousOn (fun z : ℂ => ((z - z₀) ^ (k + 1))⁻¹) K := by
      intro z hz
      have hzz : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKs hz).2
      exact (((continuous_id.sub continuous_const).continuousAt.zpow₀ (k + 1)
        (Or.inl hzz)).inv₀ (zpow_ne_zero _ hzz)).continuousWithinAt
    obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcont
    have h2 := tendstoUniformlyOn_smul_of_bounded hM h1
    refine (h2.congr (Eventually.of_forall fun m z hz => ?_)).congr_right fun z hz => ?_
    · have hzz : z - z₀ ≠ 0 := sub_ne_zero.mpr (hKs hz).2
      show ((z - z₀) ^ (k + 1))⁻¹ •
          ℓ (∑ j ∈ Finset.range m, (z - z₀) ^ ((j : ℤ) - (N : ℤ)) • a j) = _
      rw [map_sum, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul]
      have hexp : (j : ℤ) - ((k + (N : ℤ)) + 1) = -(k + 1) + ((j : ℤ) - (N : ℤ)) := by ring
      rw [hexp, zpow_add₀ hzz (-(k + 1)) ((j : ℤ) - (N : ℤ)), zpow_neg]
      ring
    · show ((z - z₀) ^ (k + 1))⁻¹ • ℓ (f z) = ℓ (f z) / (z - z₀) ^ (k + 1)
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [circleIntegral_eq_laurent_coeff_scalar hU hcρ hz₀ hF hR hS]
  congr 1
  split_ifs with h
  · rfl
  · rw [map_zero]
