-- Prove2me | solution 1 for RelaxedPRS.Feas.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T05:19:29.91598+00:00
-- url     : https://prove2.me/submissions/5a2a85f2-cc7d-4512-bfdc-bfd7c8dbaec1

import Mathlib
import Definitions.Def_ThreeOpSplitting_ConvexRates_Problem
import Definitions.Def_RandomGradFree_Nonsmooth_IsMetricProjection
import Definitions.Def_RelaxedPRS_Feas_Setting

set_option autoImplicit false

open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth Filter Topology

namespace RPF950

open scoped InnerProductSpace

/-- Nearest point of a closed convex nonempty set, with the obtuse-angle characterization. -/
theorem proj_exists {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : Set H} (hKc : IsClosed K) (hKv : Convex ℝ K) (hne : K.Nonempty) (z : H) :
    ∃ p, p ∈ K ∧ ‖z - p‖ = Metric.infDist z K ∧ ∀ w ∈ K, ⟪z - p, w - p⟫_ℝ ≤ 0 := by
  obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hKc.isComplete hKv z
  refine ⟨p, hp, ?_, (norm_eq_iInf_iff_real_inner_le_zero hKv hp).1 hmin⟩
  apply le_antisymm
  · rw [Metric.le_infDist hne]
    intro w hw
    have hbdd : BddBelow (Set.range fun w : K => ‖z - (w : H)‖) :=
      ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
    rw [hmin, dist_eq_norm]
    exact ciInf_le hbdd ⟨w, hw⟩
  · rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hp

/-- One averaged projection step `z + α (p - z)` is Fejér with a gain `α (2 - α) d²`. -/
theorem avg_step {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {K : Set H} {z p x : H} (hpi : ∀ w ∈ K, ⟪z - p, w - p⟫_ℝ ≤ 0) (hx : x ∈ K)
    {α : ℝ} (hα : 0 ≤ α) :
    ‖z + α • (p - z) - x‖ ^ 2 ≤ ‖z - x‖ ^ 2 - α * (2 - α) * ‖z - p‖ ^ 2 := by
  have h := hpi x hx
  have e1 : z + α • (p - z) - x = (1 - α) • (z - p) - (x - p) := by module
  have e2 : z - x = (z - p) - (x - p) := by abel
  rw [e1, e2]
  generalize z - p = a at h ⊢
  generalize x - p = b at h ⊢
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, real_inner_smul_left, mul_pow,
    Real.norm_eq_abs, sq_abs]
  nlinarith [mul_nonneg hα (neg_nonneg.mpr h)]

/-- The prox of `γ d²_K` is `z + 2γ/(2γ+1) (P_K z - z)`. -/
theorem prox_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : Set H} (hKc : IsClosed K) (hKv : Convex ℝ K) (hne : K.Nonempty) {γ : ℝ} (hγ : 0 < γ)
    {P : H → H} (hP : IsProx γ (RelaxedPRS.Feas.dsq K) P) (z p : H) (hp : p ∈ K)
    (hpd : ‖z - p‖ = Metric.infDist z K) (hpi : ∀ w ∈ K, ⟪z - p, w - p⟫_ℝ ≤ 0) :
    P z = z + (2 * γ / (2 * γ + 1)) • (p - z) := by
  set a : ℝ := 2 * γ / (2 * γ + 1) with ha
  set c : ℝ := 1 / (2 * γ + 1) with hc
  have hac : 1 - a = c := by rw [ha, hc]; field_simp; ring
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  set p0 : H := z + a • (p - z) with hp0
  have h := hP z p0
  simp only [RelaxedPRS.Feas.dsq] at h
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
  set y : H := P z with hy
  set u : H := z - p with hu
  set e : H := y - p0 with he
  -- upper bound on the value at p0
  have hup : Metric.infDist p0 K ≤ c * ‖u‖ := by
    have h1 : Metric.infDist p0 K ≤ ‖p0 - p‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem hp
    have h2 : p0 - p = c • u := by rw [hp0, hu, ← hac]; module
    rw [h2, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0] at h1
    exact h1
  have hup2 : Metric.infDist p0 K ^ 2 ≤ c ^ 2 * ‖u‖ ^ 2 := by
    have := pow_le_pow_left₀ Metric.infDist_nonneg hup 2
    rw [mul_pow] at this; exact this
  have hp0z : p0 - z = a • (p - z) := by rw [hp0]; abel
  have hp0z2 : ‖p0 - z‖ ^ 2 = a ^ 2 * ‖u‖ ^ 2 := by
    rw [hp0z, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← norm_neg (p - z), neg_sub]
  -- lower bound on the value at y
  obtain ⟨q, hq, hqd, -⟩ := proj_exists hKc hKv hne y
  have hlow : Metric.infDist y K ^ 2 ≥ 2 * c * ⟪y - p, u⟫_ℝ - c ^ 2 * ‖u‖ ^ 2 := by
    rw [← hqd]
    have h0 : 0 ≤ ‖(y - q) - c • u‖ ^ 2 := sq_nonneg _
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
      sq_abs] at h0
    have h3 : ⟪u, q - p⟫_ℝ ≤ 0 := hpi q hq
    have h4 : ⟪y - q, u⟫_ℝ = ⟪y - p, u⟫_ℝ - ⟪u, q - p⟫_ℝ := by
      rw [real_inner_comm (q - p) u, ← inner_sub_left]; congr 1; abel
    rw [h4] at h0
    nlinarith
  have hyp : y - p = c • u + e := by rw [he, hp0, hu, ← hac]; module
  have hyz : y - z = e - a • u := by rw [he, hp0, hu]; module
  have hi1 : ⟪y - p, u⟫_ℝ = c * ‖u‖ ^ 2 + ⟪e, u⟫_ℝ := by
    rw [hyp, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hi2 : ‖y - z‖ ^ 2 = ‖e‖ ^ 2 - 2 * a * ⟪e, u⟫_ℝ + a ^ 2 * ‖u‖ ^ 2 := by
    rw [hyz, norm_sub_sq_real, norm_smul, real_inner_smul_right, mul_pow, Real.norm_eq_abs,
      sq_abs]; ring
  rw [hi1] at hlow
  rw [hi2, hp0z2] at h
  have hcoef : 2 * c - 2 * a / (2 * γ) = 0 := by rw [ha, hc]; field_simp; ring
  have hkey : ‖e‖ ^ 2 / (2 * γ) ≤ 0 := by
    have h5 : ‖e‖ ^ 2 / (2 * γ) + (2 * c - 2 * a / (2 * γ)) * ⟪e, u⟫_ℝ ≤ 0 := by
      have : (‖e‖ ^ 2 - 2 * a * ⟪e, u⟫_ℝ + a ^ 2 * ‖u‖ ^ 2) / (2 * γ) =
          ‖e‖ ^ 2 / (2 * γ) - 2 * a / (2 * γ) * ⟪e, u⟫_ℝ + a ^ 2 * ‖u‖ ^ 2 / (2 * γ) := by ring
      rw [this] at h
      have : a ^ 2 * ‖u‖ ^ 2 / (2 * γ) = a ^ 2 * ‖u‖ ^ 2 / (2 * γ) := rfl
      nlinarith
    rw [hcoef, zero_mul, add_zero] at h5
    exact h5
  have he0 : ‖e‖ ^ 2 ≤ 0 := by
    have := (div_nonpos_iff.mp hkey)
    rcases this with ⟨_, h6⟩ | ⟨h6, _⟩
    · linarith
    · exact h6
  have : e = 0 := by
    have : ‖e‖ = 0 := by nlinarith [norm_nonneg e]
    exact norm_eq_zero.mp this
  rw [he, sub_eq_zero] at this
  exact this

/-- One relaxed PRS step for the two projections. -/
theorem step_ineq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {Cf Cg : Set H} {z w zp pgz pfw x : H} {ag af l : ℝ} (hag : 0 ≤ ag) (haf : 0 ≤ af)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hpgi : ∀ y ∈ Cg, ⟪z - pgz, y - pgz⟫_ℝ ≤ 0)
    (hpfi : ∀ y ∈ Cf, ⟪w - pfw, y - pfw⟫_ℝ ≤ 0)
    (hw : w = (2 : ℝ) • (z + ag • (pgz - z)) - z)
    (hzp : zp = z + (2 * l) • ((w + af • (pfw - w)) - (z + ag • (pgz - z))))
    (hx : x ∈ Cf ∩ Cg) :
    ‖zp - x‖ ^ 2 ≤ ‖z - x‖ ^ 2 - l * ((2 * ag) * (2 - 2 * ag) * ‖z - pgz‖ ^ 2 +
      (2 * af) * (2 - 2 * af) * ‖w - pfw‖ ^ 2) := by
  have hw' : w = z + (2 * ag) • (pgz - z) := by rw [hw]; module
  set v : H := w + (2 * af) • (pfw - w) with hv
  have h1 := avg_step hpgi hx.2 (by linarith : (0:ℝ) ≤ 2 * ag)
  rw [← hw'] at h1
  have h2 := avg_step hpfi hx.1 (by linarith : (0:ℝ) ≤ 2 * af)
  rw [← hv] at h2
  have hzp' : zp - x = (1 - l) • (z - x) + l • (v - x) := by
    rw [hzp, hv, hw']; module
  have h3 : ‖zp - x‖ ≤ (1 - l) * ‖z - x‖ + l * ‖v - x‖ := by
    rw [hzp']
    calc ‖(1 - l) • (z - x) + l • (v - x)‖ ≤ ‖(1 - l) • (z - x)‖ + ‖l • (v - x)‖ :=
          norm_add_le _ _
      _ = (1 - l) * ‖z - x‖ + l * ‖v - x‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - l), abs_of_nonneg hl0]
  have h4 : ‖zp - x‖ ^ 2 ≤ (1 - l) * ‖z - x‖ ^ 2 + l * ‖v - x‖ ^ 2 := by
    have h5 : ‖zp - x‖ ^ 2 ≤ ((1 - l) * ‖z - x‖ + l * ‖v - x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    nlinarith [sq_nonneg (‖z - x‖ - ‖v - x‖), mul_nonneg hl0 (by linarith : (0:ℝ) ≤ 1 - l)]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The real-number core of (5.3). -/
theorem final_arith (γf γg l μ D Dg Dfw df dz : ℝ) (hγf : 0 < γf) (hγg : 0 < γg) (hl0 : 0 < l)
    (hμ : 0 < μ) (hD : 0 ≤ D) (hDg : 0 ≤ Dg) (hDfw : 0 ≤ Dfw) (hdf0 : 0 ≤ df)
    (hdf : df ≤ 2 * (2 * γg / (2 * γg + 1)) * Dg + Dfw) (hreg : D ≤ μ * max df Dg)
    (hstep : dz ^ 2 ≤ D ^ 2 - l * ((2 * (2 * γg / (2 * γg + 1))) * (2 - 2 * (2 * γg / (2 * γg + 1)))
      * Dg ^ 2 + (2 * (2 * γf / (2 * γf + 1))) * (2 - 2 * (2 * γf / (2 * γf + 1))) * Dfw ^ 2)) :
    dz ≤ RelaxedPRS.Feas.Cfeas γf γg l μ * D := by
  have hβg : (2 * (2 * γg / (2 * γg + 1))) * (2 - 2 * (2 * γg / (2 * γg + 1))) =
      8 * (γg / (2 * γg + 1) ^ 2) := by field_simp; ring
  have hβf : (2 * (2 * γf / (2 * γf + 1))) * (2 - 2 * (2 * γf / (2 * γf + 1))) =
      8 * (γf / (2 * γf + 1) ^ 2) := by field_simp; ring
  rw [hβg, hβf] at hstep
  have h4ag : 4 * (2 * γg / (2 * γg + 1)) ^ 2 = 16 * γg ^ 2 / (2 * γg + 1) ^ 2 := by
    field_simp; ring
  set ag := 2 * γg / (2 * γg + 1) with hag
  set m := min (γg / (2 * γg + 1) ^ 2) (γf / (2 * γf + 1) ^ 2) with hm
  set M := max (16 * γg ^ 2 / (2 * γg + 1) ^ 2) 1 with hM
  have hmpos : 0 < m := lt_min (by positivity) (by positivity)
  have hmg : m ≤ γg / (2 * γg + 1) ^ 2 := min_le_left _ _
  have hmf : m ≤ γf / (2 * γf + 1) ^ 2 := min_le_right _ _
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM4 : 4 * ag ^ 2 ≤ M := by rw [h4ag]; exact le_max_left _ _
  have hag0 : 0 ≤ ag := by rw [hag]; positivity
  have hmx : (max df Dg) ^ 2 ≤ 2 * M * (Dg ^ 2 + Dfw ^ 2) := by
    rcases le_total df Dg with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg Dfw]
    · rw [max_eq_left h]
      have h6 : df ^ 2 ≤ (2 * ag * Dg + Dfw) ^ 2 := pow_le_pow_left₀ hdf0 hdf 2
      nlinarith [sq_nonneg (2 * ag * Dg - Dfw), sq_nonneg Dg, sq_nonneg Dfw]
  have hD2 : D ^ 2 ≤ μ ^ 2 * (max df Dg) ^ 2 := by
    have := pow_le_pow_left₀ hD hreg 2
    rw [mul_pow] at this; exact this
  set S := 8 * (γg / (2 * γg + 1) ^ 2) * Dg ^ 2 + 8 * (γf / (2 * γf + 1) ^ 2) * Dfw ^ 2 with hS
  have hS1 : 8 * m * (Dg ^ 2 + Dfw ^ 2) ≤ S := by
    rw [hS]; nlinarith [sq_nonneg Dg, sq_nonneg Dfw]
  have hμ2 : 0 < μ ^ 2 * M := by positivity
  have hkey : 4 * m * D ^ 2 ≤ μ ^ 2 * M * S := by
    have h7 : D ^ 2 ≤ μ ^ 2 * (2 * M * (Dg ^ 2 + Dfw ^ 2)) :=
      le_trans hD2 (mul_le_mul_of_nonneg_left hmx (by positivity))
    have h8 : 0 ≤ μ ^ 2 * M := hμ2.le
    nlinarith [mul_le_mul_of_nonneg_left hS1 h8]
  have hdiv : 4 * m * D ^ 2 / (μ ^ 2 * M) ≤ S := by rw [div_le_iff₀ hμ2]; linarith
  have hA : dz ^ 2 ≤ (1 - 4 * l * m / (μ ^ 2 * M)) * D ^ 2 := by
    have : (1 - 4 * l * m / (μ ^ 2 * M)) * D ^ 2 = D ^ 2 - l * (4 * m * D ^ 2 / (μ ^ 2 * M)) := by
      field_simp
    rw [this]
    have := mul_le_mul_of_nonneg_left hdiv hl0.le
    linarith
  unfold RelaxedPRS.Feas.Cfeas
  rw [← hm, ← hM]
  have h9 := Real.abs_le_sqrt hA
  rw [Real.sqrt_mul' _ (sq_nonneg D), Real.sqrt_sq hD] at h9
  exact le_trans (le_abs_self dz) h9

end RPF950

open ThreeOpSplitting.ConvexRates RandomGradFree.Nonsmooth RelaxedPRS.Feas Filter Topology in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Cf Cg : Set H) (hCfc : IsClosed Cf) (hCfv : Convex ℝ Cf) (hCgc : IsClosed Cg)
    (hCgv : Convex ℝ Cg) (hne : (Cf ∩ Cg).Nonempty) (hreg : IsBddLinReg Cf Cg)
    (γf γg lam : ℕ → ℝ) (hγf : ∀ k, 0 < γf k) (hγg : ∀ k, 0 < γg k)
    (hlam : ∀ k, 0 < lam k ∧ lam k ≤ 1)
    (Pf Pg : ℕ → H → H) (hPf : ∀ k, IsProx (γf k) (dsq Cf) (Pf k))
    (hPg : ∀ k, IsProx (γg k) (dsq Cg) (Pg k))
    (z : ℕ → H) (hz : IsFeasRun Pf Pg lam z)
    (ρ μρ : ℝ) (hρ : 0 < ρ) (hμρ : 0 < μρ) (hball : ∀ j, z j ∈ Metric.ball (0 : H) ρ)
    (hμreg : ∀ x ∈ Metric.ball (0 : H) ρ,
      Metric.infDist x (Cf ∩ Cg) ≤ μρ * max (Metric.infDist x Cf) (Metric.infDist x Cg)) :
    (∀ k, Metric.infDist (z (k + 1)) (Cf ∩ Cg) ≤
        Cfeas (γf k) (γg k) (lam k) μρ * Metric.infDist (z k) (Cf ∩ Cg)) ∧
      ∀ c : ℝ, c < 1 → (∀ j, Cfeas (γf j) (γg j) (lam j) μρ ≤ c) →
        ∃ x ∈ Cf ∩ Cg, Tendsto z atTop (𝓝 x) ∧
          ∀ k, ‖z k - x‖ ≤ 2 * Metric.infDist (z 0) (Cf ∩ Cg) *
            ∏ i ∈ Finset.range k, Cfeas (γf i) (γg i) (lam i) μρ := by
  classical
  have hneg : Cg.Nonempty := hne.mono Set.inter_subset_right
  have hnef : Cf.Nonempty := hne.mono Set.inter_subset_left
  have hCc : IsClosed (Cf ∩ Cg) := hCfc.inter hCgc
  have hCv : Convex ℝ (Cf ∩ Cg) := hCfv.inter hCgv
  choose pg hpgK hpgd hpgi using RPF950.proj_exists hCgc hCgv hneg
  choose pf hpfK hpfd hpfi using RPF950.proj_exists hCfc hCfv hnef
  choose pc hpcK hpcd hpci using RPF950.proj_exists hCc hCv hne
  have hPg' : ∀ k y, Pg k y = y + (2 * γg k / (2 * γg k + 1)) • (pg y - y) := fun k y =>
    RPF950.prox_eq hCgc hCgv hneg (hγg k) (hPg k) y (pg y) (hpgK y) (hpgd y) (hpgi y)
  have hPf' : ∀ k y, Pf k y = y + (2 * γf k / (2 * γf k + 1)) • (pf y - y) := fun k y =>
    RPF950.prox_eq hCfc hCfv hnef (hγf k) (hPf k) y (pf y) (hpfK y) (hpfd y) (hpfi y)
  have hstep : ∀ k, ∀ x ∈ Cf ∩ Cg, ‖z (k + 1) - x‖ ^ 2 ≤ ‖z k - x‖ ^ 2 - lam k *
      ((2 * (2 * γg k / (2 * γg k + 1))) * (2 - 2 * (2 * γg k / (2 * γg k + 1))) *
          ‖z k - pg (z k)‖ ^ 2 +
        (2 * (2 * γf k / (2 * γf k + 1))) * (2 - 2 * (2 * γf k / (2 * γf k + 1))) *
          ‖((2 : ℝ) • Pg k (z k) - z k) - pf ((2 : ℝ) • Pg k (z k) - z k)‖ ^ 2) := by
    intro k x hx
    refine RPF950.step_ineq (Cf := Cf) (Cg := Cg) (by have := hγg k; positivity)
      (by have := hγf k; positivity) (hlam k).1.le (hlam k).2 (hpgi (z k))
      (hpfi ((2 : ℝ) • Pg k (z k) - z k)) (by rw [hPg']) ?_ hx
    rw [hz k, hPf' k ((2 : ℝ) • Pg k (z k) - z k)]
    all_goals (rw [hPg' k (z k)])
  have hβnn : ∀ k, 0 ≤ (2 * (2 * γg k / (2 * γg k + 1))) * (2 - 2 * (2 * γg k / (2 * γg k + 1))) ∧
      0 ≤ (2 * (2 * γf k / (2 * γf k + 1))) * (2 - 2 * (2 * γf k / (2 * γf k + 1))) := by
    intro k
    have h1 := hγg k
    have h2 := hγf k
    constructor
    · have : (2 * (2 * γg k / (2 * γg k + 1))) * (2 - 2 * (2 * γg k / (2 * γg k + 1))) =
          8 * (γg k / (2 * γg k + 1) ^ 2) := by field_simp; ring
      rw [this]; positivity
    · have : (2 * (2 * γf k / (2 * γf k + 1))) * (2 - 2 * (2 * γf k / (2 * γf k + 1))) =
          8 * (γf k / (2 * γf k + 1) ^ 2) := by field_simp; ring
      rw [this]; positivity
  -- (5.3)
  have hcontr : ∀ k, Metric.infDist (z (k + 1)) (Cf ∩ Cg) ≤
      Cfeas (γf k) (γg k) (lam k) μρ * Metric.infDist (z k) (Cf ∩ Cg) := by
    intro k
    have hs := hstep k (pc (z k)) (hpcK (z k))
    rw [hpcd] at hs
    have hdzp : Metric.infDist (z (k + 1)) (Cf ∩ Cg) ≤ ‖z (k + 1) - pc (z k)‖ := by
      rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hpcK _)
    have hdz2 : Metric.infDist (z (k + 1)) (Cf ∩ Cg) ^ 2 ≤ ‖z (k + 1) - pc (z k)‖ ^ 2 :=
      pow_le_pow_left₀ Metric.infDist_nonneg hdzp 2
    set w := (2 : ℝ) • Pg k (z k) - z k with hw
    have hzw : ‖z k - w‖ = 2 * (2 * γg k / (2 * γg k + 1)) * ‖z k - pg (z k)‖ := by
      have : z k - w = (2 * (2 * γg k / (2 * γg k + 1))) • (z k - pg (z k)) := by
        rw [hw, hPg']; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by have := hγg k; positivity)]
    have hdf : Metric.infDist (z k) Cf ≤ 2 * (2 * γg k / (2 * γg k + 1)) * ‖z k - pg (z k)‖ +
        ‖w - pf w‖ := by
      have h1 : Metric.infDist (z k) Cf ≤ ‖z k - pf w‖ := by
        rw [← dist_eq_norm]; exact Metric.infDist_le_dist_of_mem (hpfK _)
      have h2 := norm_sub_le_norm_sub_add_norm_sub (z k) w (pf w)
      rw [hzw] at h2
      linarith
    have hr := hμreg (z k) (hball k)
    rw [← hpgd (z k)] at hr
    exact RPF950.final_arith (γf k) (γg k) (lam k) μρ _ _ _ _ _ (hγf k) (hγg k) (hlam k).1 hμρ
      Metric.infDist_nonneg (norm_nonneg _) (norm_nonneg _) Metric.infDist_nonneg hdf hr
      (le_trans hdz2 hs)
  refine ⟨hcontr, ?_⟩
  intro c hc hCle
  set d : ℕ → ℝ := fun k => Metric.infDist (z k) (Cf ∩ Cg) with hd
  have hdnn : ∀ k, 0 ≤ d k := fun k => Metric.infDist_nonneg
  have hCnn : ∀ k, 0 ≤ Cfeas (γf k) (γg k) (lam k) μρ := fun k => Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := le_trans (hCnn 0) (hCle 0)
  -- Fejér monotonicity
  have hfej : ∀ x ∈ Cf ∩ Cg, ∀ k, ‖z (k + 1) - x‖ ≤ ‖z k - x‖ := by
    intro x hx k
    have h1 := hstep k x hx
    have h2 := hβnn k
    have h3 : 0 ≤ lam k * ((2 * (2 * γg k / (2 * γg k + 1))) * (2 - 2 * (2 * γg k / (2 * γg k + 1))) *
          ‖z k - pg (z k)‖ ^ 2 +
        (2 * (2 * γf k / (2 * γf k + 1))) * (2 - 2 * (2 * γf k / (2 * γf k + 1))) *
          ‖((2 : ℝ) • Pg k (z k) - z k) - pf ((2 : ℝ) • Pg k (z k) - z k)‖ ^ 2) := by
      apply mul_nonneg (hlam k).1.le
      exact add_nonneg (mul_nonneg h2.1 (sq_nonneg _)) (mul_nonneg h2.2 (sq_nonneg _))
    nlinarith [norm_nonneg (z (k + 1) - x), norm_nonneg (z k - x)]
  have hfejN : ∀ x ∈ Cf ∩ Cg, ∀ k n, k ≤ n → ‖z n - x‖ ≤ ‖z k - x‖ := by
    intro x hx k n hkn
    induction n, hkn using Nat.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact le_trans (hfej x hx n) ih
  have hdist : ∀ k n, k ≤ n → ‖z n - z k‖ ≤ 2 * d k := by
    intro k n hkn
    have h1 := norm_sub_le_norm_sub_add_norm_sub (z n) (pc (z k)) (z k)
    have h2 := hfejN (pc (z k)) (hpcK (z k)) k n hkn
    have h3 : ‖pc (z k) - z k‖ = d k := by rw [norm_sub_rev, hpcd]
    have h4 : ‖z k - pc (z k)‖ = d k := hpcd (z k)
    linarith
  have hdk : ∀ k, d k ≤ d 0 * ∏ i ∈ Finset.range k, Cfeas (γf i) (γg i) (lam i) μρ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.prod_range_succ]
      calc d (k + 1) ≤ Cfeas (γf k) (γg k) (lam k) μρ * d k := hcontr k
        _ ≤ Cfeas (γf k) (γg k) (lam k) μρ *
            (d 0 * ∏ i ∈ Finset.range k, Cfeas (γf i) (γg i) (lam i) μρ) :=
          mul_le_mul_of_nonneg_left ih (hCnn k)
        _ = _ := by ring
  have hdc : ∀ k, d k ≤ d 0 * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc d (k + 1) ≤ Cfeas (γf k) (γg k) (lam k) μρ * d k := hcontr k
        _ ≤ c * d k := mul_le_mul_of_nonneg_right (hCle k) (hdnn k)
        _ ≤ c * (d 0 * c ^ k) := mul_le_mul_of_nonneg_left ih hc0
        _ = d 0 * c ^ (k + 1) := by ring
  have hd0 : Tendsto (fun k => d 0 * c ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc).const_mul (d 0)
  have hcs : CauchySeq z := by
    refine cauchySeq_of_le_tendsto_0 (fun N => 4 * (d 0 * c ^ N)) (fun n m N hn hm => ?_)
      (by simpa using hd0.const_mul 4)
    have h1 := dist_triangle (z n) (z N) (z m)
    rw [dist_comm (z N) (z m), dist_eq_norm, dist_eq_norm, dist_eq_norm] at *
    have h2 := hdist N n hn
    have h3 := hdist N m hm
    have h4 := hdc N
    linarith
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcs
  have hdt : Tendsto d atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hd0 hdnn hdc
  have hdx : Tendsto d atTop (𝓝 (Metric.infDist x (Cf ∩ Cg))) :=
    ((Metric.continuous_infDist_pt (Cf ∩ Cg)).tendsto x).comp hx
  have hxC : x ∈ Cf ∩ Cg := by
    rw [hCc.mem_iff_infDist_zero hne]
    exact tendsto_nhds_unique hdx hdt
  refine ⟨x, hxC, hx, fun k => ?_⟩
  have hlim : Tendsto (fun n => ‖z n - z k‖) atTop (𝓝 ‖x - z k‖) := (hx.sub_const (z k)).norm
  have hb : ‖x - z k‖ ≤ 2 * d k :=
    le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨k, fun n hn => hdist k n hn⟩)
  rw [norm_sub_rev]
  have := hdk k
  calc ‖x - z k‖ ≤ 2 * d k := hb
    _ ≤ 2 * (d 0 * ∏ i ∈ Finset.range k, Cfeas (γf i) (γg i) (lam i) μρ) := by linarith
    _ = _ := by rw [hd]; ring
