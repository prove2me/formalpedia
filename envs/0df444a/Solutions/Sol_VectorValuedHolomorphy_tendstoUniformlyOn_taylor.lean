-- Prove2me | solution 1 for VectorValuedHolomorphy.tendstoUniformlyOn_taylor
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:07:04.594061+00:00
-- url     : https://prove2.me/submissions/01ce1063-489b-4fb6-babc-2b564c43a476

import Mathlib
import Theorems.Thm_VectorValuedHolomorphy_differentiableOn_iterate_deriv

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace Sol_VectorValuedHolomorphy_tendstoUniformlyOn_taylor

/-- The vector space `E`, regarded as a seminormed space for the seminorm `p`. -/
def SN {E : Type*} [AddCommGroup E] [Module ℂ E] (_p : Seminorm ℂ E) : Type _ := E

section SN

variable {E : Type*} [AddCommGroup E] [Module ℂ E] (p : Seminorm ℂ E)

noncomputable instance : SeminormedAddCommGroup (SN p) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := E) p.toAddGroupSeminorm

noncomputable instance : Module ℂ (SN p) := inferInstanceAs (Module ℂ E)

noncomputable instance : NormedSpace ℂ (SN p) :=
  ⟨fun c x => (map_smul_eq_mul p c x).le⟩

/-- The identity map from `E` to the seminormed space `(E, p)`. -/
def toSN : E →ₗ[ℂ] SN p := LinearMap.id

theorem norm_toSN (x : E) : ‖toSN p x‖ = p x := rfl

end SN

/-- **Hahn–Banach**, seminorm form: a continuous seminorm `p` on a topological vector space is
controlled by the continuous linear functionals dominated by multiples of `p`. -/
theorem seminorm_le_of_forall_dual_le {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] (p : Seminorm ℂ E) (hp : Continuous p)
    (x : E) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ (ℓ : StrongDual ℂ E) (K : ℝ), 0 ≤ K → (∀ y, ‖ℓ y‖ ≤ K * p y) → ‖ℓ x‖ ≤ M * K) :
    p x ≤ M := by
  have hι : Continuous (toSN p) := by
    refine (Metric.continuous_iff' (f := fun y : E => toSN p y)).mpr fun x ε hε => ?_
    have hcont : Continuous (fun y : E => p (y - x)) :=
      hp.comp (continuous_id.sub continuous_const)
    have hsmall := (hcont.continuousAt (x := x)).eventually_lt continuousAt_const
      (show p (x - x) < ε by simpa using hε)
    simp only [dist_eq_norm, ← map_sub, norm_toSN]
    exact hsmall
  rw [← norm_toSN p x]
  refine NormedSpace.norm_le_dual_bound ℂ (toSN p x) hM fun φ => ?_
  exact h (φ.comp ⟨toSN p, hι⟩) ‖φ‖ (norm_nonneg φ) fun y => φ.le_opNorm (toSN p y)

/-- Remainder estimate for the Taylor series of a scalar holomorphic function: if `g` is
holomorphic on a neighbourhood of the closed disc of radius `R'` and bounded by `C` on its boundary
circle, then on the closed disc of radius `R < R'` the `n`-th Taylor remainder is at most
`C (R/R')^n / (1 - R/R')`. -/
theorem norm_taylor_sub_le {g : ℂ → ℂ} {c : ℂ} {R R' C : ℝ} (hR : 0 ≤ R) (hRR' : R < R')
    (hg : DifferentiableOn ℂ g (closedBall c R')) (hC : ∀ w ∈ sphere c R', ‖g w‖ ≤ C)
    {z : ℂ} (hz : z ∈ closedBall c R) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, ((z - c) ^ k / (k.factorial : ℂ)) * iteratedDeriv k g c) - g z‖
      ≤ C * (R / R') ^ n * (1 - R / R')⁻¹ := by
  have hR' : 0 < R' := hR.trans_lt hRR'
  have hq0 : 0 ≤ R / R' := div_nonneg hR hR'.le
  have hq1 : R / R' < 1 := (div_lt_one hR').2 hRR'
  have hgb : DifferentiableOn ℂ g (ball c R') := hg.mono ball_subset_closedBall
  have hdc : DiffContOnCl ℂ g (ball c R') := by
    refine DifferentiableOn.diffContOnCl ?_
    rwa [closure_ball c hR'.ne']
  have hzb : z ∈ ball c R' := closedBall_subset_ball hRR' hz
  have hs := Complex.hasSum_taylorSeries_on_ball hgb hzb
  have hz' : ‖z - c‖ ≤ R := by simpa [dist_eq_norm] using hz
  have hbound : ∀ k : ℕ,
      ‖((k.factorial : ℂ))⁻¹ • (z - c) ^ k • iteratedDeriv k g c‖ ≤ C * (R / R') ^ k := by
    intro k
    have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR' hdc hC
    have hfac : (0 : ℝ) < (k.factorial : ℝ) := by positivity
    rw [norm_smul, norm_smul, norm_inv, norm_pow, Complex.norm_natCast]
    calc ((k.factorial : ℝ))⁻¹ * (‖z - c‖ ^ k * ‖iteratedDeriv k g c‖)
        ≤ ((k.factorial : ℝ))⁻¹ * (R ^ k * (k.factorial * C / R' ^ k)) := by gcongr
      _ = C * (R / R') ^ k := by
        rw [div_pow]
        field_simp
  have htail := (hasSum_nat_add_iff' n).mpr hs
  have hgeom : HasSum (fun k : ℕ => C * (R / R') ^ (k + n))
      (C * (R / R') ^ n * (1 - R / R')⁻¹) := by
    have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (C * (R / R') ^ n)
    have e : (fun k : ℕ => C * (R / R') ^ (k + n)) =
        fun k : ℕ => C * (R / R') ^ n * (R / R') ^ k := by
      funext k
      ring
    rw [e]
    exact h
  have hfin := htail.norm_le_of_bounded hgeom (fun k => hbound (k + n))
  have hsum : ∑ i ∈ Finset.range n, ((i.factorial : ℂ))⁻¹ • (z - c) ^ i • iteratedDeriv i g c
      = ∑ k ∈ Finset.range n, ((z - c) ^ k / (k.factorial : ℂ)) * iteratedDeriv k g c :=
    Finset.sum_congr rfl fun k _ => by
      rw [smul_eq_mul, smul_eq_mul]
      ring
  rw [hsum] at hfin
  rw [← norm_neg, neg_sub]
  exact hfin

end Sol_VectorValuedHolomorphy_tendstoUniformlyOn_taylor

open Sol_VectorValuedHolomorphy_tendstoUniformlyOn_taylor in
theorem solution {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U)
    {c : ℂ} {R : ℝ} (hcR : closedBall c R ⊆ U) :
    TendstoUniformlyOn
      (fun (n : ℕ) (z : ℂ) =>
        ∑ k ∈ Finset.range n, ((z - c) ^ k / (k.factorial : ℂ)) • deriv^[k] f c)
      f atTop (closedBall c R) := by
  rcases lt_or_ge R 0 with hRneg | hR0
  · rw [closedBall_eq_empty.2 hRneg]
    exact tendstoUniformlyOn_empty
  -- a slightly larger closed disc is still contained in `U`
  obtain ⟨δ, hδ, hδU⟩ := (isCompact_closedBall c R).exists_cthickening_subset_open hU hcR
  rw [cthickening_closedBall hδ.le hR0] at hδU
  have hRR' : R < δ + R := lt_add_of_pos_left R hδ
  have hR' : 0 < δ + R := hR0.trans_lt hRR'
  have hcU : c ∈ U := hcR (mem_closedBall_self hR0)
  have hq0 : 0 ≤ R / (δ + R) := div_nonneg hR0 hR'.le
  have hq1 : R / (δ + R) < 1 := (div_lt_one hR').2 hRR'
  -- `f` is continuous on `U`, and its derivatives are computed weakly
  have hder := VectorValuedHolomorphy.differentiableOn_iterate_deriv hU hf
  have hcont : ContinuousOn f U := (hder 0).1.continuousOn
  -- the seminorm estimate for the remainder
  have key : ∀ p : Seminorm ℂ E, Continuous p → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ closedBall c R,
        p ((∑ k ∈ Finset.range n, ((z - c) ^ k / (k.factorial : ℂ)) • deriv^[k] f c) - f z)
          < ε := by
    intro p hp ε hε
    obtain ⟨M, hM⟩ := (isCompact_sphere c (δ + R)).exists_bound_of_continuousOn
      ((hp.comp_continuousOn hcont).mono (sphere_subset_closedBall.trans hδU))
    have hM' : ∀ w ∈ sphere c (δ + R), p (f w) ≤ max M 0 := fun w hw =>
      (le_abs_self _).trans ((hM w hw).trans (le_max_left _ _))
    have hlim : Tendsto (fun n : ℕ => max M 0 * (R / (δ + R)) ^ n * (1 - R / (δ + R))⁻¹)
        atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (max M 0)).mul_const
        ((1 - R / (δ + R))⁻¹)
      simpa using this
    filter_upwards [hlim.eventually_lt_const hε] with n hn z hz
    refine lt_of_le_of_lt ?_ hn
    refine seminorm_le_of_forall_dual_le p hp _ (by positivity) fun ℓ K hK0 hK => ?_
    have hsph : ∀ w ∈ sphere c (δ + R), ‖ℓ (f w)‖ ≤ K * max M 0 := fun w hw =>
      (hK (f w)).trans (mul_le_mul_of_nonneg_left (hM' w hw) hK0)
    have hsc := norm_taylor_sub_le hR0 hRR' ((hf ℓ).mono hδU) hsph hz n
    have hval : ℓ ((∑ k ∈ Finset.range n, ((z - c) ^ k / (k.factorial : ℂ)) • deriv^[k] f c)
        - f z) = (∑ k ∈ Finset.range n,
          ((z - c) ^ k / (k.factorial : ℂ)) * iteratedDeriv k (fun w => ℓ (f w)) c) - ℓ (f z) := by
      rw [map_sub, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, (hder k).2 ℓ c hcU, smul_eq_mul]
    rw [hval]
    refine hsc.trans (le_of_eq ?_)
    ring
  -- uniform convergence from the seminorm estimates
  intro u hu
  rw [uniformity_eq_comap_nhds_zero E, Filter.mem_comap] at hu
  obtain ⟨V, hV, hVu⟩ := hu
  obtain ⟨⟨s, ε⟩, hε, hball⟩ :=
    (PolynormableSpace.withSeminorms ℂ E).hasBasis_zero_ball.mem_iff.mp hV
  have hall : ∀ᶠ n : ℕ in atTop, ∀ q ∈ s, ∀ z ∈ closedBall c R,
      q.1 ((∑ k ∈ Finset.range n, ((z - c) ^ k / (k.factorial : ℂ)) • deriv^[k] f c) - f z)
        < ε :=
    (Filter.eventually_all_finset s).2 fun q _ => key q.1 q.2 ε hε
  filter_upwards [hall] with n hn z hz
  refine hVu (hball ?_)
  rw [Seminorm.mem_ball_zero]
  exact Seminorm.finset_sup_apply_lt hε fun q hq => hn q hq z hz
