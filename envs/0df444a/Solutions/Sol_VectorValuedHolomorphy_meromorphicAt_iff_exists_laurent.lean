-- Prove2me | solution 1 for VectorValuedHolomorphy.meromorphicAt_iff_exists_laurent
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:15:27.057831+00:00
-- url     : https://prove2.me/submissions/81b16a63-71a0-4fed-9ba6-da99e4861803

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_Meromorphic
import Theorems.Thm_VectorValuedHolomorphy_differentiableOn_iff_forall_strongDual
import Theorems.Thm_VectorValuedHolomorphy_tendstoUniformlyOn_taylor

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_meromorphicAt_iff_exists_laurent

open scoped Pointwise Uniformity

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

/-- Clearing the pole: `(w - z₀)^N` times a Laurent partial sum is a polynomial partial sum. -/
theorem smul_laurent_sum {E : Type*} [AddCommGroup E] [Module ℂ E] (a : ℕ → E) (N m : ℕ)
    {w z₀ : ℂ} (hw : w ≠ z₀) :
    (w - z₀) ^ N • ∑ j ∈ Finset.range m, (w - z₀) ^ ((j : ℤ) - (N : ℤ)) • a j
      = ∑ j ∈ Finset.range m, (w - z₀) ^ j • a j := by
  have h0 : w - z₀ ≠ 0 := sub_ne_zero.mpr hw
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← zpow_natCast (w - z₀) N, ← zpow_add₀ h0, ← zpow_natCast (w - z₀) j]
  congr 2
  ring

/-- Dividing a Taylor partial sum by `(w - z₀)^N` gives a Laurent partial sum. -/
theorem zpow_neg_smul_taylor_sum {E : Type*} [AddCommGroup E] [Module ℂ E] (v : ℕ → E) (N m : ℕ)
    {w z₀ : ℂ} (hw : w ≠ z₀) :
    (w - z₀) ^ (-(N : ℤ)) • ∑ k ∈ Finset.range m, ((w - z₀) ^ k / (k.factorial : ℂ)) • v k
      = ∑ j ∈ Finset.range m,
          (w - z₀) ^ ((j : ℤ) - (N : ℤ)) • (((j.factorial : ℂ))⁻¹ • v j) := by
  have h0 : w - z₀ ≠ 0 := sub_ne_zero.mpr hw
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul, zpow_sub₀ h0, zpow_neg, zpow_natCast, zpow_natCast]
  congr 1
  ring

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

end Sol_VectorValuedHolomorphy_meromorphicAt_iff_exists_laurent

open Sol_VectorValuedHolomorphy_meromorphicAt_iff_exists_laurent in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] (f : ℂ → E) (z₀ : ℂ) :
    VectorValuedHolomorphy.MeromorphicAt f z₀ ↔
      ∃ (N : ℕ) (a : ℕ → E) (R : ℝ), 0 < R ∧
        ∀ K : Set ℂ, IsCompact K → K ⊆ ball z₀ R \ {z₀} →
          TendstoUniformlyOn
            (fun (n : ℕ) (z : ℂ) =>
              ∑ j ∈ Finset.range n, (z - z₀) ^ ((j : ℤ) - (N : ℤ)) • a j)
            f atTop K := by
  constructor
  · -- a pole-clearing representation gives a Laurent expansion
    rintro ⟨N, g, hg, hfg⟩
    obtain ⟨r₁, hr₁, hg⟩ := Metric.eventually_nhds_iff_ball.mp hg
    obtain ⟨r₂, hr₂, hfg⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_nhdsWithin_iff.mp hfg)
    have hr : 0 < min r₁ r₂ := lt_min hr₁ hr₂
    have hgd : DifferentiableOn ℂ g (ball z₀ (min r₁ r₂)) := fun z hz =>
      (hg z (ball_subset_ball (min_le_left _ _) hz)).differentiableWithinAt
    have hweak :=
      (VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual isOpen_ball g).mp hgd
    refine ⟨N, fun j => ((j.factorial : ℂ))⁻¹ • deriv^[j] g z₀, min r₁ r₂, hr,
      fun K hK hKsub => ?_⟩
    rcases K.eq_empty_or_nonempty with rfl | hne
    · exact tendstoUniformlyOn_empty
    have hdist : ContinuousOn (fun z : ℂ => dist z z₀) K :=
      (continuous_id.dist continuous_const).continuousOn
    obtain ⟨z₁, hz₁, hmax⟩ := hK.exists_isMaxOn hne hdist
    obtain ⟨z₂, hz₂, hmin⟩ := hK.exists_isMinOn hne hdist
    have hz₁r : dist z₁ z₀ < min r₁ r₂ := mem_ball.mp (hKsub hz₁).1
    have hz₂0 : 0 < dist z₂ z₀ := dist_pos.mpr (hKsub hz₂).2
    have hKcl : K ⊆ closedBall z₀ (dist z₁ z₀) := fun z hz =>
      mem_closedBall.mpr (isMaxOn_iff.mp hmax z hz)
    have hT := (VectorValuedHolomorphy.tendstoUniformlyOn_taylor isOpen_ball hweak
      (c := z₀) (R := dist z₁ z₀) (closedBall_subset_ball hz₁r)).mono hKcl
    have hbound : ∀ z ∈ K, ‖(z - z₀) ^ (-(N : ℤ))‖ ≤ (dist z₂ z₀ ^ N)⁻¹ := by
      intro z hz
      rw [zpow_neg, zpow_natCast, norm_inv, norm_pow]
      have h1 : dist z₂ z₀ ≤ ‖z - z₀‖ := by
        rw [← dist_eq_norm]
        exact isMinOn_iff.mp hmin z hz
      gcongr
    have hT' := tendstoUniformlyOn_smul_of_bounded (c := fun z => (z - z₀) ^ (-(N : ℤ)))
      hbound hT
    refine (hT'.congr (Eventually.of_forall fun n z hz => ?_)).congr_right fun z hz => ?_
    · exact zpow_neg_smul_taylor_sum (fun k => deriv^[k] g z₀) N n (hKsub hz).2
    · have hzne : z ≠ z₀ := (hKsub hz).2
      have h0 : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne
      have hgz := hfg z (ball_subset_ball (min_le_right _ _) (hKsub hz).1) hzne
      show (z - z₀) ^ (-(N : ℤ)) • g z = f z
      rw [hgz, smul_smul, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero N h0), one_smul]
  · -- a Laurent expansion gives a pole-clearing representation
    rintro ⟨N, a, R, hR, hconv⟩
    classical
    set g : ℂ → E := fun z => if z = z₀ then a 0 else (z - z₀) ^ N • f z with hgdef
    have hg_ne : ∀ z, z ≠ z₀ → g z = (z - z₀) ^ N • f z := fun z hz => if_neg hz
    have hg_z₀ : g z₀ = a 0 := if_pos rfl
    -- the polynomial partial sums converge to `g` at every point of the disc
    have hpt : ∀ w ∈ ball z₀ R,
        Tendsto (fun m : ℕ => ∑ j ∈ Finset.range m, (w - z₀) ^ j • a j) atTop (𝓝 (g w)) := by
      intro w hw
      by_cases hwz : w = z₀
      · rw [hwz, hg_z₀]
        refine tendsto_atTop_of_eventually_const (i₀ := 1) fun m hm => ?_
        rw [Finset.sum_eq_single 0]
        · simp
        · intro j _ hj
          simp [hj]
        · intro h
          exact absurd (Finset.mem_range.mpr hm) h
      · have hsub : ({w} : Set ℂ) ⊆ ball z₀ R \ {z₀} := by
          rintro _ rfl
          exact ⟨hw, hwz⟩
        have h1 := (hconv {w} isCompact_singleton hsub).tendsto_at (Set.mem_singleton w)
        have h2 := h1.const_smul ((w - z₀) ^ N)
        rw [hg_ne w hwz]
        exact Tendsto.congr (fun m => smul_laurent_sum a N m hwz) h2
    -- `g` is weakly holomorphic on the disc, hence holomorphic
    have hgd : DifferentiableOn ℂ g (ball z₀ R) := by
      rw [VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual isOpen_ball g]
      intro ℓ z hz
      obtain ⟨ρ, hzρ, hρR⟩ := exists_between (mem_ball.mp hz)
      have hρ : 0 < ρ := dist_nonneg.trans_lt hzρ
      have hsphere : sphere z₀ ρ ⊆ ball z₀ R \ {z₀} := by
        intro w hw
        have hwd : dist w z₀ = ρ := mem_sphere.mp hw
        refine ⟨mem_ball.mpr (hwd ▸ hρR), fun hwz => ?_⟩
        rw [Set.mem_singleton_iff.mp hwz, dist_self] at hwd
        exact hρ.ne hwd
      have h1 := hconv (sphere z₀ ρ) (isCompact_sphere z₀ ρ) hsphere
      have hbound : ∀ w ∈ sphere z₀ ρ, ‖(w - z₀) ^ N‖ ≤ ρ ^ N := by
        intro w hw
        rw [norm_pow, ← dist_eq_norm, mem_sphere.mp hw]
      have h2 := tendstoUniformlyOn_smul_of_bounded (c := fun w => (w - z₀) ^ N) hbound h1
      have h3 := ℓ.uniformContinuous.comp_tendstoUniformlyOn h2
      have h4 : TendstoUniformlyOn
          (fun (m : ℕ) (w : ℂ) => ∑ j ∈ Finset.range m, (w - z₀) ^ j * ℓ (a j))
          (fun w => ℓ (g w)) atTop (sphere z₀ ρ) := by
        refine (h3.congr (Eventually.of_forall fun m w hw => ?_)).congr_right fun w hw => ?_
        · show ℓ ((w - z₀) ^ N • ∑ j ∈ Finset.range m, (w - z₀) ^ ((j : ℤ) - (N : ℤ)) • a j) = _
          rw [smul_laurent_sum a N m (hsphere hw).2, map_sum]
          simp only [map_smul, smul_eq_mul]
        · show ℓ ((w - z₀) ^ N • f w) = ℓ (g w)
          rw [hg_ne w (hsphere hw).2]
      have hφ : ∀ m : ℕ, Differentiable ℂ
          (fun w : ℂ => ∑ j ∈ Finset.range m, (w - z₀) ^ j * ℓ (a j)) := by
        intro m
        fun_prop
      have h5 := differentiableOn_ball_of_tendstoUniformlyOn_sphere hρ hφ h4 (fun w hw => by
        have h6 := (ℓ.continuous.tendsto (g w)).comp (hpt w (ball_subset_ball hρR.le hw))
        refine Tendsto.congr (fun m => ?_) h6
        simp only [Function.comp_apply, map_sum, map_smul, smul_eq_mul])
      exact (h5.differentiableAt (isOpen_ball.mem_nhds hzρ)).differentiableWithinAt
    refine ⟨N, g, ?_, ?_⟩
    · filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hR)] with z hz
      exact hgd.differentiableAt (isOpen_ball.mem_nhds hz)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact hg_ne z hz
