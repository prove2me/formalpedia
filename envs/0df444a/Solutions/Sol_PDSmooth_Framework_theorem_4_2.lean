-- Prove2me | solution 1 for PDSmooth.Framework.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:11:26.661293+00:00
-- url     : https://prove2.me/submissions/f8d35145-35b8-4c61-a823-7afc9048b743

import Mathlib
import Definitions.Def_PDSmooth_Framework_Setting
import Theorems.Thm_PDSmooth_Framework_eq_3_7

open Filter Topology

namespace PDSmoothSol
open PDSmooth.Framework

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

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

lemma bregman_self (ω : E → ℝ) (x : E) : bregman ω x x = 0 := by
  simp [bregman]

/-- (lb_BD): `D_ω(x', x) ≥ ½‖x' − x‖²` on `X`. -/
lemma bregman_lb {X : Set E} {ω : E → ℝ} (hsc : StrongConvexOn X 1 ω) {x x' : E}
    (hx : x ∈ X) (hx' : x' ∈ X) (hd : DifferentiableAt ℝ ω x) :
    (1 / 2) * ‖x' - x‖ ^ 2 ≤ bregman ω x' x := by
  set d := x' - x with hdd
  set L := fderiv ℝ ω x
  have hf : HasDerivAt (fun t : ℝ => ω (x + t • d)) (L d) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
    exact HasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hd.hasFDerivAt h1 (by simp)
  have hslope := hf.tendsto_slope_zero_right
  set n := ‖x - x'‖
  have hrhs : Tendsto (fun t : ℝ => ω x' - ω x - (1 - t) * (1 / 2 * n ^ 2)) (𝓝[>] 0)
      (𝓝 (ω x' - ω x - (1 / 2 * n ^ 2))) := by
    have : Tendsto (fun t : ℝ => ω x' - ω x - (1 - t) * (1 / 2 * n ^ 2)) (𝓝 0)
        (𝓝 (ω x' - ω x - (1 - 0) * (1 / 2 * n ^ 2))) :=
      ((continuous_const.sub ((continuous_const.sub continuous_id).mul continuous_const)).tendsto 0)
    rw [sub_zero, one_mul] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ • (ω (x + (0 + t) • d) - ω (x + (0:ℝ) • d)) ≤
      ω x' - ω x - (1 - t) * (1 / 2 * n ^ 2) := by
    have hlt : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 :=
      nhdsWithin_le_nhds (eventually_lt_nhds zero_lt_one)
    filter_upwards [hlt, self_mem_nhdsWithin] with t ht1 ht0
    have ht0' : (0:ℝ) < t := ht0
    have key := hsc.2 hx hx' (show (0:ℝ) ≤ 1 - t by linarith) ht0'.le (show (1 - t) + t = 1 by ring)
    have e : (1 - t) • x + t • x' = x + t • d := by rw [hdd]; module
    rw [e] at key
    simp only [smul_eq_mul] at key
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [inv_mul_le_iff₀ ht0']
    nlinarith [key]
  have := le_of_tendsto_of_tendsto hslope hrhs hev
  have hn : ‖x' - x‖ = n := norm_sub_rev _ _
  unfold bregman
  rw [hn]
  linarith

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

/-- One executed, non-terminating iteration decreases `q` by `(γλ/(1−γλ) − 4)η`. -/
lemma descent [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ}
    {ωX : E → ℝ} {ωY : F → ℝ} {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    {lam η : ℝ} (hlam0 : 0 < lam) (hlam1 : lam < γ⁻¹) (hη : 0 < η)
    {x : ℕ → E} (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x)
    (k : ℕ) (hk : 1 ≤ k) (hpre : ∀ j : ℕ, 1 ≤ j → j < k → ¬ Stops γ lam η x j)
    (hns : ¬ Stops γ lam η x k) :
    qObj Φ g r Y (x (k + 1)) ≤ qObj Φ g r Y (x k) - (γ * lam / (1 - γ * lam) - 4) * η := by
  have hγ := hA.γ_pos
  have hμ := lam_gap hγ hlam0 hlam1
  have hγl : γ * lam < 1 := by
    have := (lt_inv_comm₀ hlam0 hγ).mp hlam1
    have h2 : γ * lam < lam⁻¹ * lam := mul_lt_mul_of_pos_right this hlam0
    rwa [inv_mul_cancel₀ hlam0.ne'] at h2
  have hR := rangeY_nonneg hA
  set ρ := 2 * η / rangeY ωY Y with hρdef
  have hρ0 : 0 ≤ ρ := rho_nonneg hR hη
  have hρR : ρ * rangeY ωY Y ≤ 2 * η := rho_mul_le hR hη
  have hxk : x k ∈ X := run_mem hx k hk hpre
  obtain ⟨hxk1, hrun⟩ := hx.2 k hk hpre
  have h1 := hrun (x k) hxk
  have hb := bregman_lb hA.ωX_strong hxk hxk1 (hA.ωX_diff _ hxk)
  have hs : 0 ≤ 2 * η / (lam⁻¹ - γ) := by positivity
  have hD : 2 * η / (lam⁻¹ - γ) < ‖x (k + 1) - x k‖ ^ 2 := by
    unfold Stops at hns
    rw [not_le] at hns
    have := pow_lt_pow_left₀ hns (Real.sqrt_nonneg _) (two_ne_zero)
    rwa [Real.sq_sqrt hs] at this
  have e0 := abs_le.mp (PDSmooth.Framework.eq_3_7 hA ρ hρ0 (x k) hxk)
  have e1 := abs_le.mp (PDSmooth.Framework.eq_3_7 hA ρ hρ0 (x (k + 1)) hxk1)
  unfold Qprox at h1
  rw [bregman_self, mul_zero, add_zero] at h1
  unfold qSmooth at h1
  unfold qObj
  -- `λ⁻¹ D ≥ η/(1 − γλ)`
  have hli : 0 < lam⁻¹ := inv_pos.mpr hlam0
  have hc : lam⁻¹ * (1 / 2 * (2 * η / (lam⁻¹ - γ))) = η / (1 - γ * lam) := by
    have h1' : 1 - γ * lam ≠ 0 := by linarith
    have h2' : lam⁻¹ - γ ≠ 0 := hμ.ne'
    field_simp
  have hD2 : η / (1 - γ * lam) ≤ lam⁻¹ * bregman ωX (x (k + 1)) (x k) := by
    rw [← hc]
    apply mul_le_mul_of_nonneg_left _ hli.le
    linarith
  have he : (γ * lam / (1 - γ * lam) - 4) * η = η / (1 - γ * lam) - 5 * η := by
    have h1' : 1 - γ * lam ≠ 0 := by linarith
    field_simp
    ring
  rw [he]
  linarith

end PDSmoothSol

open PDSmooth.Framework PDSmoothSol

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {X : Set E} {Y : Set F} {Φ : E → F → ℝ} {g : F → ℝ} {r : E → ℝ} {ωX : E → ℝ} {ωY : F → ℝ}
    {γ βX : ℝ} (hA : StandingAssumptions X Y Φ g r ωX ωY γ βX)
    (lam η qstar : ℝ) (hlam0 : 0.8 * γ⁻¹ < lam) (hlam1 : lam < γ⁻¹) (hη : 0 < η)
    (hqstar : ∀ z ∈ X, qstar ≤ qObj Φ g r Y z)
    (x : ℕ → E) (hx : IsAlg1Run X Y Φ g r ωX ωY γ lam η x) :
    ∃ K : ℕ, 1 ≤ K ∧
      (K : ℤ) ≤ ⌈(qObj Φ g r Y (x 1) - qstar) / ((γ * lam / (1 - γ * lam) - 4) * η)⌉ + 1 ∧
      Stops γ lam η x K ∧ (∀ j : ℕ, 1 ≤ j → j < K → ¬ Stops γ lam η x j) := by
  classical
  have hγ := hA.γ_pos
  have hlam0' : 0 < lam := lt_trans (by positivity) hlam0
  have hγl : γ * lam < 1 := by
    have := (lt_inv_comm₀ hlam0' hγ).mp hlam1
    have h2 : γ * lam < lam⁻¹ * lam := mul_lt_mul_of_pos_right this hlam0'
    rwa [inv_mul_cancel₀ hlam0'.ne'] at h2
  have h08 : 0.8 < γ * lam := by
    have := mul_lt_mul_of_pos_left hlam0 hγ
    rwa [mul_left_comm, mul_inv_cancel₀ hγ.ne', mul_one] at this
  set c := (γ * lam / (1 - γ * lam) - 4) * η with hcdef
  have hc : 0 < c := by
    have h1 : 0 < 1 - γ * lam := by linarith
    have : 4 < γ * lam / (1 - γ * lam) := by
      rw [lt_div_iff₀ h1]; norm_num at h08 ⊢; linarith
    have : 0 < γ * lam / (1 - γ * lam) - 4 := by linarith
    positivity
  set q := qObj Φ g r Y with hqdef
  set B := (q (x 1) - qstar) / c with hBdef
  have hB0 : 0 ≤ B := by
    have := hqstar (x 1) hx.1
    rw [hBdef]; apply div_nonneg (by linarith) hc.le
  have hceil0 : 0 ≤ ⌈B⌉ := Int.ceil_nonneg hB0
  set N : ℕ := (⌈B⌉).toNat + 1 with hNdef
  have hNB : B < (N : ℝ) := by
    have h1 : B ≤ (⌈B⌉ : ℝ) := Int.le_ceil B
    have h2 : ((⌈B⌉).toNat : ℤ) = ⌈B⌉ := Int.toNat_of_nonneg hceil0
    have h3 : ((⌈B⌉).toNat : ℝ) = (⌈B⌉ : ℝ) := by exact_mod_cast h2
    rw [hNdef]; push_cast; linarith
  have hex : ∃ j : ℕ, 1 ≤ j ∧ j ≤ N ∧ Stops γ lam η x j := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ j : ℕ, 1 ≤ j → j ≤ N → ¬ Stops γ lam η x j := fun j h1 h2 => hcon j h1 h2
    have ind : ∀ k : ℕ, 1 ≤ k → k ≤ N + 1 → q (x k) ≤ q (x 1) - ((k : ℝ) - 1) * c := by
      intro k
      induction k with
      | zero => intro h; omega
      | succ n ih =>
        intro h1 h2
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn; simp
        · have ihn := ih hn (by omega)
          have hd := descent hA hlam0' hlam1 hη hx n hn
            (fun j hj1 hj2 => hall j hj1 (by omega)) (hall n hn (by omega))
          push_cast
          linarith
    have hN := ind (N + 1) (by omega) le_rfl
    have hmem : x (N + 1) ∈ X :=
      run_mem hx (N + 1) (by omega) (fun j hj1 hj2 => hall j hj1 (by omega))
    have hq := hqstar _ hmem
    push_cast at hN
    have : B * c < (N : ℝ) * c := mul_lt_mul_of_pos_right hNB hc
    rw [hBdef, div_mul_cancel₀ _ hc.ne'] at this
    linarith
  have hex' : ∃ j : ℕ, 1 ≤ j ∧ Stops γ lam η x j := by
    obtain ⟨j, h1, _, h3⟩ := hex; exact ⟨j, h1, h3⟩
  obtain ⟨j0, hj01, hj0N, hj0s⟩ := hex
  refine ⟨Nat.find hex', (Nat.find_spec hex').1, ?_, (Nat.find_spec hex').2, ?_⟩
  · have hle : Nat.find hex' ≤ j0 := Nat.find_min' hex' ⟨hj01, hj0s⟩
    have h2 : ((⌈B⌉).toNat : ℤ) = ⌈B⌉ := Int.toNat_of_nonneg hceil0
    have : (Nat.find hex' : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle.trans hj0N
    rw [hNdef] at this; push_cast at this; rw [h2] at this
    exact this
  · intro j hj1 hj2 hs
    exact Nat.find_min hex' hj2 ⟨hj1, hs⟩
