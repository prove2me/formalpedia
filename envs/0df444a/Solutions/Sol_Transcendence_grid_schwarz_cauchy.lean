-- Prove2me | solution 1 for Transcendence.grid_schwarz_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-02T09:17:29.233537+00:00
-- url     : https://prove2.me/submissions/c2402dda-ebb7-46c7-b2c4-6517bfeebba0

import Mathlib
import Theorems.Thm_Transcendence_cartesian_schwarz
import Theorems.Thm_Transcendence_polydisc_cauchy

/-!
# Schwarz's lemma on a lattice grid, then Cauchy's inequality

Waldschmidt's §4.6, step 5. The linear isomorphism `A : z ↦ Σ_j z_j y_j` carries the Cartesian grid
`{0, …, S₁ - 1}ⁿ` onto the lattice grid, so `f = F ∘ A` vanishes to total order `< n S₀` on the grid
(`iteratedFDeriv` commutes with the linear map). Node 1 (`cartesian_schwarz`) with `r' = c₉ S₁` and
`R' = 2·3ⁿ ρ r'` bounds `f` on the polydisc of radius `r'` by `n ρ^{-S₀S₁} B`. That polydisc covers
`A⁻¹` of the unit polydisc around every grid point, where `c₉ = cinv (cy + 1) + 1` and `cinv` bounds a
right inverse of `A`; Cauchy's inequality (node 0, `polydisc_cauchy`) there finishes. The constant is
`c = (cy + 1) · 2·3ⁿ · c₉`, `cy = Σ ‖y_j‖`.
-/

namespace GridSchwarzCauchy

lemma prod_count_factorial_le {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} (L : Fin k → ι) :
    (∏ ν, ((Finset.univ.filter fun l => L l = ν).card.factorial : ℝ)) ≤ k.factorial := by
  have hsum : ∑ ν, (Finset.univ.filter fun l => L l = ν).card = k := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := L) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))]
    simp
  have h := Nat.le_of_dvd (Nat.factorial_pos _) (Nat.prod_factorial_dvd_factorial_sum
    Finset.univ (fun ν => (Finset.univ.filter fun l => L l = ν).card))
  rw [hsum] at h
  exact_mod_cast h

/-- The linear isomorphism `z ↦ Σ_j z_j y_j` from `ℂⁿ` (coordinates `Fin n`, `n = |ι|`) to `ℂ^ι`. -/
noncomputable def linY {ι : Type*} [Fintype ι] (y : ι → ι → ℂ) :
    (Fin (Fintype.card ι) → ℂ) →L[ℂ] (ι → ℂ) :=
  ∑ j, (ContinuousLinearMap.proj j : (Fin (Fintype.card ι) → ℂ) →L[ℂ] ℂ).smulRight
    (y ((Fintype.equivFin ι).symm j))

lemma linY_apply {ι : Type*} [Fintype ι] (y : ι → ι → ℂ) (z : Fin (Fintype.card ι) → ℂ) :
    linY y z = ∑ j', z (Fintype.equivFin ι j') • y j' := by
  have : linY y z = ∑ j, z j • y ((Fintype.equivFin ι).symm j) := by simp [linY]
  rw [this]
  exact Fintype.sum_equiv (Fintype.equivFin ι).symm (fun j => z j • y ((Fintype.equivFin ι).symm j))
    (fun j' => z (Fintype.equivFin ι j') • y j') (fun j => by simp)

lemma norm_linY_le {ι : Type*} [Fintype ι] (y : ι → ι → ℂ) (z : Fin (Fintype.card ι) → ℂ) :
    ‖linY y z‖ ≤ (∑ j, ‖y j‖) * ‖z‖ := by
  rw [linY_apply]
  calc ‖∑ j', z (Fintype.equivFin ι j') • y j'‖ ≤ ∑ j', ‖z (Fintype.equivFin ι j') • y j'‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j', ‖z‖ * ‖y j'‖ := Finset.sum_le_sum fun j' _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm z _) (norm_nonneg _)
    _ = (∑ j, ‖y j‖) * ‖z‖ := by rw [← Finset.mul_sum, mul_comm]

lemma linY_surjective {ι : Type*} [Fintype ι] (y : ι → ι → ℂ) (hy : LinearIndependent ℂ y) :
    Function.Surjective (linY y) := by
  have hinj : Function.Injective (linY y) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    rw [linY_apply] at hz
    have h0 := Fintype.linearIndependent_iff.mp hy (fun j' => z (Fintype.equivFin ι j')) hz
    funext j
    simpa using h0 ((Fintype.equivFin ι).symm j)
  have hfr : Module.finrank ℂ (Fin (Fintype.card ι) → ℂ) = Module.finrank ℂ (ι → ℂ) := by simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr
    (f := (linY y : (Fin (Fintype.card ι) → ℂ) →ₗ[ℂ] (ι → ℂ)))).mp hinj

end GridSchwarzCauchy

open GridSchwarzCauchy Metric in
/-- **Schwarz's lemma on a lattice grid, then Cauchy's inequality** (DALAG Prop. 4.7, moved to the grid
`{Σ_j s_j y_j}`). -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (hn : 0 < Fintype.card ι)
    (y : ι → ι → ℂ) (hy : LinearIndependent ℂ y) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ F : (ι → ℂ) → ℂ, AnalyticOnNhd ℂ F Set.univ →
      ∀ (S₀ S₁ M : ℕ) (ρ B : ℝ), 1 ≤ S₁ → 1 ≤ ρ → Fintype.card ι * S₀ ≤ M →
      (∀ k < M, ∀ s : ι → Fin S₁, iteratedFDeriv ℂ k F (∑ j, ((s j : ℕ) : ℂ) • y j) = 0) →
      (∀ w : ι → ℂ, ‖w‖ ≤ c * S₁ * ρ → ‖F w‖ ≤ B) →
      ∀ (s : ι → Fin S₁) (L : Fin M → ι),
        ‖iteratedFDeriv ℂ M F (∑ j, ((s j : ℕ) : ℂ) • y j) (fun l => Pi.single (L l) 1)‖ ≤
          M.factorial * (Fintype.card ι * ρ⁻¹ ^ (S₀ * S₁) * B) := by
  classical
  set n := Fintype.card ι with hn_def
  obtain ⟨cinv, hcinv0, hcinv⟩ :=
    ContinuousLinearMap.exists_preimage_norm_le (linY y) (linY_surjective y hy)
  set cy : ℝ := ∑ j, ‖y j‖ with hcy_def
  have hcy : 0 ≤ cy := Finset.sum_nonneg fun j _ => norm_nonneg _
  set c₉ : ℝ := cinv * (cy + 1) + 1 with hc₉
  have hc₉1 : 1 ≤ c₉ := by
    have : 0 ≤ cinv * (cy + 1) := by positivity
    linarith
  have h3n : (3 : ℝ) ≤ 3 ^ n := by
    calc (3 : ℝ) = 3 ^ 1 := by ring
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  refine ⟨(cy + 1) * (2 * 3 ^ n) * c₉, ?_, ?_⟩
  · calc (1 : ℝ) ≤ 1 * (2 * 1) * 1 := by norm_num
      _ ≤ (cy + 1) * (2 * 3 ^ n) * c₉ := by gcongr <;> linarith
  intro F hFan S₀ S₁ M ρ B hS₁ hρ hnM hmin hFbound s' L'
  have hS₁' : (1 : ℝ) ≤ S₁ := by exact_mod_cast hS₁
  have hρpos : 0 < ρ := by linarith
  set q : (ι → Fin S₁) → (ι → ℂ) := fun s => ∑ j, ((s j : ℕ) : ℂ) • y j with hq_def
  have hqnorm : ∀ s, ‖q s‖ ≤ S₁ * cy := by
    intro s
    calc ‖q s‖ ≤ ∑ j, ‖((s j : ℕ) : ℂ) • y j‖ := norm_sum_le _ _
      _ ≤ ∑ j, (S₁ : ℝ) * ‖y j‖ := Finset.sum_le_sum fun j _ => by
          rw [norm_smul, Complex.norm_natCast]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast (s j).2.le) (norm_nonneg _)
      _ = S₁ * cy := by rw [← Finset.mul_sum]
  /- `f = F ∘ A` on the Cartesian grid `{0, …, S₁ - 1}ⁿ`, with radii `r' = c₉ S₁`, `R' = 2·3ⁿ ρ r'`. -/
  set f : (Fin n → ℂ) → ℂ := fun z => F (linY y z) with hf_def
  have hfan : AnalyticOnNhd ℂ f Set.univ := fun z _ =>
    (hFan (linY y z) trivial).comp ((linY y).analyticAt z)
  set Eg : Fin n → Finset ℂ := fun _ => (Finset.range S₁).image (fun j : ℕ => (j : ℂ)) with hEg
  have hEcard : ∀ i, (Eg i).card = S₁ := by
    intro i
    rw [hEg, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  set r' : ℝ := c₉ * S₁ with hr'_def
  have hr'pos : 0 < r' := by positivity
  have hEr : ∀ i, ∀ ζ ∈ Eg i, ‖ζ‖ ≤ r' := by
    intro i ζ hζ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hζ
    rw [Complex.norm_natCast]
    have : (j : ℝ) ≤ S₁ := by exact_mod_cast (Finset.mem_range.mp hj).le
    calc (j : ℝ) ≤ 1 * S₁ := by linarith
      _ ≤ r' := by rw [hr'_def]; gcongr
  set R' : ℝ := 2 * 3 ^ n * ρ * r' with hR'_def
  have hR' : 5 * r' ≤ R' := by
    rw [hR'_def]
    have h6 : (6 : ℝ) ≤ 2 * 3 ^ n * ρ := by
      calc (6 : ℝ) = 2 * 3 * 1 := by norm_num
        _ ≤ 2 * 3 ^ n * ρ := by gcongr
    have := mul_le_mul_of_nonneg_right h6 hr'pos.le
    linarith
  have hR'0 : 0 ≤ R' := by linarith
  have hMf : ∀ z ∈ closedBall (0 : Fin n → ℂ) R', ‖f z‖ ≤ B := by
    intro z hz
    rw [mem_closedBall_zero_iff] at hz
    apply hFbound
    have e : (cy + 1) * (2 * 3 ^ n) * c₉ * S₁ * ρ = (cy + 1) * R' := by
      rw [hR'_def, hr'_def]; ring
    rw [e]
    calc ‖linY y z‖ ≤ cy * ‖z‖ := norm_linY_le y z
      _ ≤ cy * R' := mul_le_mul_of_nonneg_left hz hcy
      _ ≤ (cy + 1) * R' := mul_le_mul_of_nonneg_right (by linarith) hR'0
  have hvanf : ∀ ζ : Fin n → ℂ, (∀ i, ζ i ∈ Eg i) → ∀ k < n * S₀, iteratedFDeriv ℂ k f ζ = 0 := by
    intro ζ hζ k hk
    have hζ' : ∀ i, ∃ j, j < S₁ ∧ (j : ℂ) = ζ i := by
      intro i
      obtain ⟨j, hj, h⟩ := Finset.mem_image.mp (hζ i)
      exact ⟨j, Finset.mem_range.mp hj, h⟩
    choose sζ hsζ hsζeq using hζ'
    set s'' : ι → Fin S₁ := fun j' => ⟨sζ (Fintype.equivFin ι j'), hsζ _⟩ with hs''
    have hAζ : linY y ζ = q s'' := by
      rw [linY_apply, hq_def]
      exact Finset.sum_congr rfl fun j' _ => by rw [hs'', ← hsζeq]
    have hcomp : f = F ∘ linY y := rfl
    rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (linY y) (hFan.contDiff (n := ⊤)) ζ
      (by exact_mod_cast le_top), hAζ, hmin k (lt_of_lt_of_le hk hnM) s'']
    ext v
    simp
  have hSch := Transcendence.cartesian_schwarz hn f hfan Eg hEcard hr'pos hEr hR' hMf hvanf
  have hratio : 2 * 3 ^ n * r' / R' = ρ⁻¹ := by
    rw [hR'_def]; field_simp
  /- `|F| ≤ n ρ^{-S₀S₁} B` on the unit polydisc around `s'y`, then Cauchy's inequality there. -/
  have hFsmall : ∀ w ∈ closedBall (q s') 1, ‖F w‖ ≤ n * ρ⁻¹ ^ (S₀ * S₁) * B := by
    intro w hw
    obtain ⟨z, hz, hzn⟩ := hcinv w
    have hw' : ‖w‖ ≤ S₁ * cy + 1 := by
      rw [mem_closedBall, dist_eq_norm] at hw
      have := norm_add_le (q s') (w - q s')
      have h2 := hqnorm s'
      simp only [add_sub_cancel] at this
      linarith
    have hzr : z ∈ closedBall (0 : Fin n → ℂ) r' := by
      rw [mem_closedBall_zero_iff]
      calc ‖z‖ ≤ cinv * ‖w‖ := hzn
        _ ≤ cinv * (S₁ * cy + 1) := mul_le_mul_of_nonneg_left hw' hcinv0.le
        _ ≤ r' := by
            rw [hr'_def, hc₉]
            have : cinv * (S₁ * cy + 1) ≤ cinv * ((cy + 1) * S₁) := by
              apply mul_le_mul_of_nonneg_left _ hcinv0.le
              have e : (cy + 1) * (S₁ : ℝ) = S₁ * cy + S₁ := by ring
              rw [e]; linarith
            have e : (cinv * (cy + 1) + 1) * (S₁ : ℝ) = cinv * ((cy + 1) * S₁) + S₁ := by ring
            rw [e]; linarith
    have := hSch z hzr
    rw [hratio] at this
    rw [← hz]
    exact this
  have hCau' := Transcendence.polydisc_cauchy hFan (q s') one_pos hFsmall M L'
  rw [one_pow, div_one] at hCau'
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hFbound 0 (by rw [norm_zero]; positivity))
  have hbd0 : 0 ≤ (n : ℝ) * ρ⁻¹ ^ (S₀ * S₁) * B :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (pow_nonneg (inv_nonneg.mpr hρpos.le) _)) hB0
  exact hCau'.trans (mul_le_mul_of_nonneg_right (prod_count_factorial_le L') hbd0)
