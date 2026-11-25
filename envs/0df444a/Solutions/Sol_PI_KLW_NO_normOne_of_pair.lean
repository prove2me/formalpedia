-- Prove2me | solution 1 for PI.KLW.NO.normOne_of_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:52.733498+00:00
-- url     : https://prove2.me/submissions/1b9fe5e2-854e-4da0-a185-7fbbe5007437

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_NormOneC
import Theorems.Thm_PI_KLW_NO_generic_pair
import Theorems.Thm_PI_KLW_NO_rp_two
import Theorems.Thm_PI_KLW_NO_rp_four
import Theorems.Thm_PI_KLW_NO_dvd_pow_p
import Theorems.Thm_PI_KLW_NO_eps
import Theorems.Thm_PI_KLW_NO_ne_of_split
import Theorems.Thm_PI_KLW_NO_one_add_p_unit
import Theorems.Thm_PI_KLW_NO_refl_norm
import Theorems.Thm_PI_KLW_NO_rp_pow
import Theorems.Thm_PI_KLW_NO_rp_pow_div
import Theorems.Thm_PI_KLW_Rp_add
import Theorems.Thm_PI_KLW_Rp_map
import Theorems.Thm_PI_KLW_Rp_mul
import Theorems.Thm_PI_KLW_Rp_natCast
import Theorems.Thm_PI_KLW_Rp_one
import Theorems.Thm_PI_KLW_Rp_sub
import Theorems.Thm_PI_KLW_Unimod_add_mem
import Theorems.Thm_PI_KLW_Unimod_hf_mem
import Theorems.Thm_PI_KLW_Unimod_smul_mem
import Theorems.Thm_PI_KLW_Unimod_sub_mem
import Theorems.Thm_PI_KLW_hf_add_left
import Theorems.Thm_PI_KLW_hf_add_right
import Theorems.Thm_PI_KLW_hf_single_left
import Theorems.Thm_PI_KLW_hf_smul_left
import Theorems.Thm_PI_KLW_hf_smul_right
import Theorems.Thm_PI_KLW_hf_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW PI.KLW.NO
namespace PI.KLW.NO
theorem _root_.solution {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] [Nonempty ι] (L : Set (ι → K)) (hK : Module.finrank ℚ K = 2)
    (hc : ∀ x, c (c x) = x) (hp : p.Prime) (hs : SplitK c p) (hU : Unimod K c p L)
    (hS : Spans K L) {x y : ι → K} (hx : x ∈ L) (hy : y ∈ L) (hxy : hf c x y = 1) :
    ∃ e ∈ L, hf c e e = 1 := by
  classical
  have hne := ne_of_split c hs
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨v₀, hv₀def⟩ : ∃ v₀ : ι → K, v₀ = Pi.single i0 1 := ⟨_, rfl⟩
  have hv₀ : hf c v₀ v₀ = 1 := by rw [hv₀def, hf_single_left]; simp
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁, hX, hY⟩ := generic_pair hc hp hU hx hy hxy v₀
  obtain ⟨N, hN0, hNv⟩ := hS v₀
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN0
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have bound : ∀ z ∈ L, Rp K p ((N : K) * (1 - hf c v₀ z)) := by
    intro z hz
    have h1 := hU.hf_mem hz hNv
    rw [hf_smul_right, map_natCast, hf_symm c hc v₀ z] at h1
    have h2 := Rp_map c h1
    rw [map_mul, map_natCast, hc] at h2
    rw [mul_sub, mul_one]; exact Rp_sub (Rp_natCast N) h2
  obtain ⟨X, hXdef⟩ : ∃ X : K, X = hf c v₀ x₁ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : K, Y = hf c v₀ y₁ := ⟨_, rfl⟩
  have hX1 : (1 : K) - X ≠ 0 := sub_ne_zero.2 (by rw [hXdef]; exact Ne.symm hX)
  have hY1 : (1 : K) - Y ≠ 0 := sub_ne_zero.2 (by rw [hYdef]; exact Ne.symm hY)
  have hbX : Rp K p ((N : K) * (1 - X)) := by rw [hXdef]; exact bound x₁ hx₁
  have hbY : Rp K p ((N : K) * (1 - Y)) := by rw [hYdef]; exact bound y₁ hy₁
  obtain ⟨J₁, hJ₁⟩ := dvd_pow_p c hc hK hne hp hbY (mul_ne_zero hNK hY1)
  obtain ⟨J₂, hJ₂⟩ := dvd_pow_p c hc hK hne hp hbX (mul_ne_zero hNK hX1)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = J₁ + J₂ := ⟨_, rfl⟩
  obtain ⟨α', hα'def⟩ : ∃ α' : K, α' = (p : K) ^ J / (1 - Y) := ⟨_, rfl⟩
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : K, γ' = (p : K) ^ J / (1 - X) := ⟨_, rfl⟩
  have hα : Rp K p α' := by
    have : α' = (N : K) * (p : K) ^ J₂ * ((p : K) ^ J₁ / (N * (1 - Y))) := by
      rw [hα'def, hJ, pow_add]; field_simp
    rw [this]; exact Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₂)) hJ₁
  have hγ : Rp K p γ' := by
    have : γ' = (N : K) * (p : K) ^ J₁ * ((p : K) ^ J₂ / (N * (1 - X))) := by
      rw [hγ'def, hJ, pow_add]; field_simp
    rw [this]; exact Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₁)) hJ₂

  obtain ⟨ε, hε, hsum, hδ⟩ := eps c hc hK hp hs (J + 1 + 2 * N)
  have hce : c ε = 1 - ε := by linear_combination hsum
  have hcε : Rp K p (c ε) := Rp_map c hε
  obtain ⟨e', he'def⟩ : ∃ e' : ι → K, e' = ε • x₁ + c ε • y₁ := ⟨_, rfl⟩
  have he' : e' ∈ L := by rw [he'def]; exact hU.add_mem (hU.smul_mem hε hx₁) (hU.smul_mem hcε hy₁)
  obtain ⟨Z, hZdef⟩ : ∃ Z : K, Z = 2 - hf c x₁ x₁ - hf c y₁ y₁ := ⟨_, rfl⟩
  have hZ : Rp K p Z := by
    rw [hZdef]; exact Rp_sub (Rp_sub rp_two (hU.hf_mem hx₁ hx₁)) (hU.hf_mem hy₁ hy₁)
  have hcZ : c Z = Z := by
    rw [hZdef, map_sub, map_sub, map_ofNat, ← hf_symm c hc x₁ x₁, ← hf_symm c hc y₁ y₁]
  have hyx : hf c y₁ x₁ = 1 := by rw [hf_symm c hc x₁ y₁, hxy₁, map_one]
  obtain ⟨d, hddef⟩ : ∃ d : K, d = ε * c ε * Z / 2 := ⟨_, rfl⟩
  have hu : hf c e' e' = 1 - 2 * d := by
    rw [he'def, hddef, hZdef]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxy₁, hyx]
    linear_combination (ε + c ε + 1) * hsum
  have hd : c d = d := by
    rw [hddef, map_div₀, map_mul, map_mul, hc, hcZ, map_ofNat]; ring
  have hB : hf c v₀ e' = c ε * X + ε * Y := by
    rw [he'def, hXdef, hYdef]; simp only [hf_add_right, hf_smul_right, hc]
  obtain ⟨β, hβdef⟩ : ∃ β : K, β = 1 - hf c v₀ e' - d := ⟨_, rfl⟩
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : K, Γ = ε * α' + c ε * γ' := ⟨_, rfl⟩
  have hΓ : Rp K p Γ := by rw [hΓdef]; exact Rp_add (Rp_mul hε hα) (Rp_mul hcε hγ)
  obtain ⟨C, hCdef⟩ : ∃ C : K, C = ε * c ε / (2 * N * (p : K) ^ (J + 1)) := ⟨_, rfl⟩
  have hC : Rp K p C := by
    have e1 : C = ε * c ε / (p : K) ^ (J + 1 + 2 * N) * ((p : K) ^ (2 * N) / ((2 * N : ℕ) : K)) := by
      rw [hCdef, show (p : K) ^ (J + 1 + 2 * N) = (p : K) ^ (J + 1) * (p : K) ^ (2 * N) by rw [pow_add]]
      push_cast; field_simp
    rw [e1]
    exact Rp_mul hδ (rp_pow_div hp (by omega) le_rfl)
  obtain ⟨ω, hωdef⟩ : ∃ ω : K, ω = C * ((2 * ((N : K) * (1 - Y)) * γ' + 2 * ((N : K) * (1 - X)) * α')
      - ((N : K) * Z * Γ + 4 * N * (p : K) ^ J)) := ⟨_, rfl⟩
  have hω : Rp K p ω := by
    rw [hωdef]
    refine Rp_mul hC (Rp_sub (Rp_add (Rp_mul (Rp_mul rp_two hbY) hγ) (Rp_mul (Rp_mul rp_two hbX) hα))
      (Rp_add (Rp_mul (Rp_mul (Rp_natCast N) hZ) hΓ)
        (Rp_mul (Rp_mul rp_four (Rp_natCast N)) (rp_pow (Rp_natCast p) J))))
  have hβΓ : β * Γ = (p : K) ^ J * (1 + (p : K) * ω) := by
    rw [hβdef, hB, hωdef, hCdef, hΓdef, hα'def, hγ'def, hddef, hce]
    field_simp
    ring
  obtain ⟨hne1, hinv⟩ := one_add_p_unit c hc hK hne hp hω
  have hPne : (p : K) ^ J * (1 + (p : K) * ω) ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hne1
  have hβ0 : β ≠ 0 := by rintro h; apply hPne; rw [← hβΓ, h, zero_mul]
  have hΓ0 : Γ ≠ 0 := by rintro h; apply hPne; rw [← hβΓ, h, mul_zero]
  obtain ⟨η, hηdef⟩ : ∃ η : K, η = d / β := ⟨_, rfl⟩
  have hβ' : β = (p : K) ^ J * (1 + (p : K) * ω) / Γ := by rw [eq_div_iff hΓ0]; exact hβΓ
  have hηN : Rp K p (η / N) := by
    have e1 : η / N = ((p : K) * C) * (Z * Γ) * (1 + (p : K) * ω)⁻¹ := by
      rw [hηdef, hβ', hddef, hCdef, pow_succ]
      field_simp
    rw [e1]
    exact Rp_mul (Rp_mul (Rp_mul (Rp_natCast p) hC) (Rp_mul hZ hΓ)) hinv
  have hη : Rp K p η := by
    have : η = (N : K) * (η / N) := by field_simp
    rw [this]; exact Rp_mul (Rp_natCast N) hηN
  refine ⟨(1 + η) • e' - η • v₀, ?_, refl_norm c hc hv₀ hu hd hβdef hβ0 hηdef⟩
  have hv : η • v₀ = (η / N) • ((N : K) • v₀) := by rw [smul_smul, div_mul_cancel₀ _ hNK]
  rw [hv]
  exact hU.sub_mem (hU.smul_mem (Rp_add Rp_one hη) he') (hU.smul_mem hηN hNv)
end PI.KLW.NO
