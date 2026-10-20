-- Prove2me | solution 1 for PDSmooth.Framework.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:13:11.041581+00:00
-- url     : https://prove2.me/submissions/a8f0805a-100b-4a48-a556-085aed0cd140

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting
import Theorems.Thm_PDSmooth_Framework_strongConvex_Q
import Theorems.Thm_PDSmooth_Framework_strongConvex_Qrho
import Theorems.Thm_PDSmooth_Framework_lemma_4_2
import Theorems.Thm_PDSmooth_Framework_lemma_4_3

open Filter Topology

namespace PDSmoothSol
open PDSmooth.Framework

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- For `x ∈ X`, the integrand `y ↦ Φ x y - g y - ρ ωY y` is bounded on `Y`. -/
lemma integrand_bound {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) {x : E} (hx : x ∈ X) :
    ∃ M, ∀ y ∈ Y, |Φ x y - g y - ρ * ωY y| ≤ M := by
  have hc : ContinuousOn (fun y => Φ x y - g y - ρ * ωY y) Y := by
    have h1 : ContinuousOn (fun y => Φ x y) Y := by
      have := hA.Φ_cont.comp (Continuous.continuousOn (continuous_const.prodMk continuous_id))
        (fun y hy => ⟨hx, hy⟩)
      exact this
    exact (h1.sub hA.g_cont).sub (continuousOn_const.mul hA.ωY_cont)
  obtain ⟨M, hM⟩ := hA.Y_compact.exists_bound_of_continuousOn hc
  exact ⟨M, fun y hy => by simpa [Real.norm_eq_abs] using hM y hy⟩

lemma bddAbove_integrand {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) {x : E} (hx : x ∈ X) :
    BddAbove (Set.range fun y : Y => Φ x y - g y - ρ * ωY y) := by
  obtain ⟨M, hM⟩ := integrand_bound hA ρ hx
  refine ⟨M, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (le_abs_self _).trans (hM y y.2)

lemma bddAbove_absωY {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX) :
    BddAbove (Set.range fun y : Y => |ωY y|) := by
  obtain ⟨M, hM⟩ := hA.Y_compact.exists_bound_of_continuousOn hA.ωY_cont
  refine ⟨M, ?_⟩
  rintro _ ⟨y, rfl⟩
  simpa [Real.norm_eq_abs] using hM y y.2

lemma rangeY_nonneg {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX) :
    0 ≤ rangeY ωY Y := by
  obtain ⟨y0, hy0⟩ := hA.Y_nonempty
  exact (abs_nonneg _).trans (le_ciSup (bddAbove_absωY hA) (⟨y0, hy0⟩ : Y))

lemma fSmooth_lsc {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ : ℝ) : LowerSemicontinuousOn (fSmooth Φ g ωY Y ρ) X := by
  have : Nonempty Y := hA.Y_nonempty.to_subtype
  intro x hx a ha
  unfold fSmooth at ha
  obtain ⟨y, hy⟩ := exists_lt_of_lt_ciSup ha
  have hc : ContinuousOn (fun x' => Φ x' y) X :=
    hA.Φ_cont.comp (Continuous.continuousOn (continuous_id.prodMk continuous_const))
      (fun x' hx' => ⟨hx', y.2⟩)
  have hc2 : ContinuousWithinAt (fun x' => Φ x' y - g y - ρ * ωY y) X x :=
    ((hc x hx).sub continuousWithinAt_const).sub continuousWithinAt_const
  have hev := hc2 (Ioi_mem_nhds hy)
  filter_upwards [hev, self_mem_nhdsWithin] with x' h1 h2
  exact lt_of_lt_of_le h1
    (le_ciSup (f := fun y : Y => Φ x' y - g y - ρ * ωY y) (bddAbove_integrand hA ρ h2) y)

lemma Qprox_lsc {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (ρ lam : ℝ) (x : E) :
    LowerSemicontinuousOn (Qprox (qSmooth Φ g r ωY Y ρ) ωX lam x) X := by
  have h1 : LowerSemicontinuousOn (qSmooth Φ g r ωY Y ρ) X :=
    (fSmooth_lsc hA ρ).add hA.r_lsc
  have h2 : ContinuousOn (fun x' => lam⁻¹ * bregman ωX x' x) X := by
    unfold bregman
    apply continuousOn_const.mul
    apply (hA.ωX_cont.sub continuousOn_const).sub
    exact ((fderiv ℝ ωX x).continuous.comp (continuous_id.sub continuous_const)).continuousOn
  exact h1.add h2.lowerSemicontinuousOn

/-- A lower semicontinuous, `μ`-strongly convex (`μ > 0`) function on a nonempty closed set of a
finite-dimensional real normed space attains its minimum. -/
theorem exists_min_strongConvex [FiniteDimensional ℝ E] {X : Set E} {Q : E → ℝ} {μ : ℝ}
    (hμ : 0 < μ) (hne : X.Nonempty) (hcl : IsClosed X) (hsc : StrongConvexOn X μ Q)
    (hlsc : LowerSemicontinuousOn Q X) : ∃ p ∈ X, ∀ z ∈ X, Q p ≤ Q z := by
  obtain ⟨x0, hx0⟩ := hne
  have cpt : ∀ R, IsCompact (X ∩ Metric.closedBall x0 R) := fun R =>
    (isCompact_closedBall x0 R).inter_left hcl
  obtain ⟨m1, hm1, hmin1⟩ := (hlsc.mono Set.inter_subset_left).exists_isMinOn
    (show (X ∩ Metric.closedBall x0 1).Nonempty from
      ⟨x0, hx0, Metric.mem_closedBall_self zero_le_one⟩) (cpt 1)
  rw [isMinOn_iff] at hmin1
  have hC : Q m1 ≤ Q x0 := hmin1 x0 ⟨hx0, Metric.mem_closedBall_self zero_le_one⟩
  set C := Q x0 - Q m1 with hCdef
  have hC0 : 0 ≤ C := by linarith
  have lin : ∀ x ∈ X, Q x0 - C * (‖x - x0‖ + 1) ≤ Q x := by
    intro x hx
    by_cases hd : ‖x - x0‖ ≤ 1
    · have : Q m1 ≤ Q x := hmin1 x ⟨hx, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hd⟩
      nlinarith [norm_nonneg (x - x0)]
    · rw [not_le] at hd
      set d := ‖x - x0‖ with hddef
      have hd0 : 0 < d := by linarith
      set t := d⁻¹ with htdef
      have ht0 : 0 < t := inv_pos.mpr hd0
      have htd : t * d = 1 := inv_mul_cancel₀ hd0.ne'
      have ht1 : t ≤ 1 := by rw [htdef]; exact inv_le_one_of_one_le₀ hd.le
      have hwX : (1 - t) • x0 + t • x ∈ X :=
        hsc.1 hx0 hx (by linarith) ht0.le (by ring)
      have hwn : ‖(1 - t) • x0 + t • x - x0‖ = 1 := by
        have : (1 - t) • x0 + t • x - x0 = t • (x - x0) := by module
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← hddef, htd]
      have hw : Q m1 ≤ Q ((1 - t) • x0 + t • x) :=
        hmin1 _ ⟨hwX, by rw [Metric.mem_closedBall, dist_eq_norm, hwn]⟩
      have key := hsc.2 hx0 hx (show (0:ℝ) ≤ 1 - t by linarith) ht0.le
        (show (1 - t) + t = 1 by ring)
      simp only [smul_eq_mul] at key
      have hnn : 0 ≤ (1 - t) * t * (μ / 2 * ‖x0 - x‖ ^ 2) := by
        have : 0 ≤ 1 - t := by linarith
        positivity
      have h3 : Q m1 ≤ (1 - t) * Q x0 + t * Q x := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 hd0.le
      have h5 : d * ((1 - t) * Q x0 + t * Q x) = (d - 1) * Q x0 + Q x := by
        have : d * ((1 - t) * Q x0 + t * Q x) = d * Q x0 - (t * d) * Q x0 + (t * d) * Q x := by
          ring
        rw [this, htd]; ring
      rw [h5] at h4
      nlinarith
  have quad : ∀ x ∈ X, Q x0 - C * (‖x - x0‖ + 2) + μ / 4 * ‖x - x0‖ ^ 2 ≤ Q x := by
    intro x hx
    have hmX : (1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • x ∈ X :=
      hsc.1 hx0 hx (by norm_num) (by norm_num) (by norm_num)
    have key := hsc.2 hx0 hx (show (0:ℝ) ≤ 1 / 2 by norm_num) (show (0:ℝ) ≤ 1 / 2 by norm_num)
      (by norm_num)
    simp only [smul_eq_mul] at key
    have hl := lin _ hmX
    have hn : ‖(1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • x - x0‖ = 1 / 2 * ‖x - x0‖ := by
      have : (1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • x - x0 = (1 / 2 : ℝ) • (x - x0) := by module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    rw [hn] at hl
    rw [norm_sub_rev x0 x] at key
    nlinarith
  set R := 4 * (C + 1) / μ + 2 * C + 1 with hR
  obtain ⟨p, hp, hpmin⟩ := (hlsc.mono Set.inter_subset_left).exists_isMinOn
    (show (X ∩ Metric.closedBall x0 R).Nonempty from
      ⟨x0, hx0, Metric.mem_closedBall_self (by positivity)⟩) (cpt R)
  rw [isMinOn_iff] at hpmin
  refine ⟨p, hp.1, fun z hz => ?_⟩
  by_cases hzR : ‖z - x0‖ ≤ R
  · exact hpmin z ⟨hz, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hzR⟩
  · rw [not_le] at hzR
    have hp0 : Q p ≤ Q x0 := hpmin x0 ⟨hx0, Metric.mem_closedBall_self (by positivity)⟩
    have hq := quad z hz
    set d := ‖z - x0‖
    have hR1 : 4 * (C + 1) / μ < d := by
      have : 0 ≤ 2 * C + 1 := by linarith
      linarith
    have h1 : 4 * (C + 1) < μ * d := by
      rw [div_lt_iff₀ hμ] at hR1; linarith
    have hd0 : 0 < d := by
      have : 0 < 4 * (C + 1) / μ := by positivity
      linarith
    have h2 : d * (4 * (C + 1)) < d * (μ * d) := mul_lt_mul_of_pos_left h1 hd0
    have h3 : 2 * C + 1 < d := by
      have : 0 < 4 * (C + 1) / μ := by positivity
      linarith
    nlinarith

lemma qObj_eq_qSmooth_zero (Φ : E → F → ℝ) (g : F → ℝ) (r : E → ℝ) (ωY : F → ℝ) (Y : Set F) :
    qObj Φ g r Y = qSmooth Φ g r ωY Y 0 := by
  funext x; simp [qObj, qSmooth, fSmooth, fMax]

lemma run_mem {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ lam η : ℝ} {x : ℕ → E}
    (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x) :
    ∀ k : ℕ, 1 ≤ k → (∀ j : ℕ, 1 ≤ j → j < k → ¬ Stops γ lam η x j) → x k ∈ X := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ n ih =>
    intro _ hpre
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; exact hx.1
    · exact (hx.2 n hn (fun j hj1 hj2 => hpre j hj1 (by omega))).1

lemma rho_nonneg {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η) : 0 ≤ 2 * η / R := by positivity

lemma rho_mul_le {R η : ℝ} (hR : 0 ≤ R) (hη : 0 < η) : 2 * η / R * R ≤ 2 * η := by
  rcases hR.eq_or_lt with h | h
  · rw [← h]; simp; linarith
  · rw [div_mul_cancel₀ _ h.ne']

lemma lam_gap {γ lam : ℝ} (hγ : 0 < γ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) :
    0 < lam⁻¹ - γ := by
  have : γ < lam⁻¹ := by
    rw [lt_inv_comm₀ hlam0 hγ] at hlam1; exact hlam1
  linarith

end PDSmoothSol

open PDSmooth.Framework PDSmoothSol

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam ε η : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (hε : 0 < ε)
    (hη : η = ε ^ 2 * lam * (1 - γ * lam) / (32 * βX ^ 2))
    (x : ℕ → E) (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x)
    (K : ℕ) (hK1 : 1 ≤ K) (hKstop : Stops γ lam η x K)
    (hKfirst : ∀ j : ℕ, 1 ≤ j → j < K → ¬ Stops γ lam η x j) :
    (∀ p : E, IsProx (qObj Φ g r Y) ωX X lam (x K) p → ‖x K - p‖ ≤ ε * lam / βX) ∧
      IsNSPoint (qObj Φ g r Y) ωX X γ βX ε (x K) := by
  have hγ := hA.γ_pos
  have hμ := lam_gap hγ hlam0 hlam1
  have hβ : 0 < βX := lt_of_lt_of_le one_pos hA.βX_ge
  have hγl : γ * lam < 1 := by
    have := (lt_inv_comm₀ hlam0 hγ).mp hlam1
    have h2 : γ * lam < lam⁻¹ * lam := mul_lt_mul_of_pos_right this hlam0
    rwa [inv_mul_cancel₀ hlam0.ne'] at h2
  have hηpos : 0 < η := by
    rw [hη]; have : 0 < 1 - γ * lam := by linarith
    positivity
  have hR := rangeY_nonneg hA
  set ρ := 2 * η / rangeY ωY Y with hρdef
  have hρ0 : 0 ≤ ρ := rho_nonneg hR hηpos
  have hρR : ρ * rangeY ωY Y ≤ 2 * η := rho_mul_le hR hηpos
  have hxK : x K ∈ X := run_mem hx K hK1 hKfirst
  -- existence of the two proximal points
  obtain ⟨pρ, hpρX, hpρmin⟩ := exists_min_strongConvex hμ hA.X_nonempty hA.X_closed
    (PDSmooth.Framework.strongConvex_Qrho hA lam ρ hlam0 hlam1 hρ0 (x K) hxK) (Qprox_lsc hA ρ lam (x K))
  have hpρ : IsProx (qSmooth Φ g r ωY Y ρ) ωX X lam (x K) pρ := ⟨hpρX, hpρmin⟩
  have hQlsc : LowerSemicontinuousOn (Qprox (qObj Φ g r Y) ωX lam (x K)) X := by
    rw [qObj_eq_qSmooth_zero Φ g r ωY Y]; exact Qprox_lsc hA 0 lam (x K)
  obtain ⟨p0, hp0X, hp0min⟩ := exists_min_strongConvex hμ hA.X_nonempty hA.X_closed
    (PDSmooth.Framework.strongConvex_Q hA lam hlam0 hlam1 (x K) hxK) hQlsc
  -- the key value: `4 √(2η/μ) = ελ/β`
  have hval : 2 * η / (lam⁻¹ - γ) = (ε * lam / (4 * βX)) ^ 2 := by
    rw [hη]
    have h1 : 1 - γ * lam ≠ 0 := by linarith
    have h1' : 1 - lam * γ ≠ 0 := by rw [mul_comm]; exact h1
    have : lam⁻¹ - γ = (1 - γ * lam) / lam := by field_simp
    rw [this]
    field_simp
    ring
  have hsq : Real.sqrt (2 * η / (lam⁻¹ - γ)) = ε * lam / (4 * βX) := by
    rw [hval, Real.sqrt_sq (by positivity)]
  have bound : ∀ p : E, IsProx (qObj Φ g r Y) ωX X lam (x K) p → ‖x K - p‖ ≤ ε * lam / βX := by
    intro p hp
    have h1 := PDSmooth.Framework.lemma_4_2 hA lam η hlam0 hlam1 hηpos x hx K hK1 hKstop hKfirst pρ hpρ
    have h2 := PDSmooth.Framework.lemma_4_3 hA lam ρ hlam0 hlam1 hρ0 (x K) hxK p pρ hp hpρ
    have h3 : Real.sqrt (ρ * rangeY ωY Y / (lam⁻¹ - γ)) ≤ Real.sqrt (2 * η / (lam⁻¹ - γ)) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hρR hμ.le)
    have htri : ‖x K - p‖ ≤ ‖x K - pρ‖ + ‖pρ - p‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [hsq] at h1 h3
    have : ε * lam / βX = 4 * (ε * lam / (4 * βX)) := by field_simp
    rw [this]
    linarith
  refine ⟨bound, hxK, lam, hlam0, hlam1, p0, ⟨hp0X, hp0min⟩, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlam0)]
  have := bound p0 ⟨hp0X, hp0min⟩
  calc lam⁻¹ * ‖x K - p0‖ ≤ lam⁻¹ * (ε * lam / βX) :=
        mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hlam0.le)
    _ = ε / βX := by field_simp
