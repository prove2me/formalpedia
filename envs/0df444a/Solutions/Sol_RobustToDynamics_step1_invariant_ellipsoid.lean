-- Prove2me | solution 1 for RobustToDynamics.step1_invariant_ellipsoid
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:01:20.600255+00:00
-- url     : https://prove2.me/submissions/052e030f-f99e-4acb-934c-83f1e7697ca5

import Mathlib
import Definitions.Def_RobustToDynamics_ellipsoid

set_option autoImplicit false

open Matrix RobustToDynamics

theorem solution {n : ℕ} (G M : Matrix (Fin n) (Fin n) ℝ)
    (hL : Gᵀ * M * G - M = -1) (hM : M.PosDef) :
    (∀ α : ℝ, Bornology.IsBounded (ellipsoid M α)) ∧
      ∀ α : ℝ, ∀ x ∈ ellipsoid M α,
        G *ᵥ x ∈ ellipsoid M α ∧ ∀ k : ℕ, (G ^ k) *ᵥ x ∈ ellipsoid M α := by
  have hMpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x) := by
    intro x hx
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx
    simpa using this
  have hstep : ∀ (α : ℝ) (x : Fin n → ℝ), x ∈ ellipsoid M α → G *ᵥ x ∈ ellipsoid M α := by
    intro α x hx
    change (G *ᵥ x) ⬝ᵥ (M *ᵥ (G *ᵥ x)) ≤ α
    have h1 : (G *ᵥ x) ⬝ᵥ (M *ᵥ (G *ᵥ x)) = x ⬝ᵥ ((Gᵀ * M * G) *ᵥ x) := by
      symm
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have hGMG : Gᵀ * M * G = M - 1 := by
      ext i j
      have := congr_fun (congr_fun hL i) j
      simp only [Matrix.sub_apply, Matrix.neg_apply] at this ⊢
      linarith
    rw [h1, hGMG, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
    have hxx : 0 ≤ x ⬝ᵥ x := Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    have hxM : x ⬝ᵥ (M *ᵥ x) ≤ α := hx
    linarith
  refine ⟨?_, fun α x hx => ⟨hstep α x hx, ?_⟩⟩
  · intro α
    by_cases hn : n = 0
    · subst hn
      exact Metric.isBounded_iff.mpr ⟨0, fun x _ y _ => by rw [Subsingleton.elim x y, dist_self]⟩
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      let S : Set (Fin n → ℝ) := Metric.sphere 0 1
      have hS_comp : IsCompact S := isCompact_sphere 0 1
      have hS_ne : S.Nonempty := by
        let e0 : Fin n → ℝ := fun _ => 1
        haveI : Nonempty (Fin n) := ⟨⟨0, hn'⟩⟩
        have he0 : ‖e0‖ = 1 := by simp [e0, pi_norm_const]
        exact ⟨e0, by simp [S, he0]⟩
      have hq_cont : Continuous (fun u : Fin n → ℝ => u ⬝ᵥ (M *ᵥ u)) := by
        show Continuous (fun u : Fin n → ℝ => ∑ i, u i * ∑ j, M i j * u j)
        exact continuous_finsetSum _ fun i _ =>
          (continuous_apply i : Continuous fun u : Fin n → ℝ => u i).mul
            (continuous_finsetSum _ fun j _ =>
              continuous_const.mul (continuous_apply j : Continuous fun u : Fin n → ℝ => u j))
      obtain ⟨u₀, hu₀S, hu₀min⟩ := hS_comp.exists_isMinOn hS_ne hq_cont.continuousOn
      have hu₀norm : ‖u₀‖ = 1 := by simpa [S] using hu₀S
      have hu₀ne : u₀ ≠ 0 := fun h => by simp [h] at hu₀norm
      set c := u₀ ⬝ᵥ (M *ᵥ u₀)
      have hc : 0 < c := hMpos u₀ hu₀ne
      refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt (max α 0 / c), fun x hx => ?_⟩
      by_cases hx0 : x = 0
      · subst hx0
        simp only [norm_zero]
        exact Real.sqrt_nonneg _
      · set r := ‖x‖
        have hr : 0 < r := norm_pos_iff.mpr hx0
        let u : Fin n → ℝ := r⁻¹ • x
        have huS : u ∈ S := by
          simp only [S, Metric.mem_sphere, dist_zero_right, u, norm_smul, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hr)]
          exact inv_mul_cancel₀ hr.ne'
        have hcu : c ≤ u ⬝ᵥ (M *ᵥ u) := hu₀min huS
        have hu_qf : u ⬝ᵥ (M *ᵥ u) = r⁻¹ ^ 2 * (x ⬝ᵥ (M *ᵥ x)) := by
          simp only [u, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
          ring
        rw [hu_qf] at hcu
        have hcr2 : c * r ^ 2 ≤ x ⬝ᵥ (M *ᵥ x) := by
          have hr2 : 0 < r ^ 2 := by positivity
          have hmul := mul_le_mul_of_nonneg_right hcu hr2.le
          have hcancel : r⁻¹ ^ 2 * (x ⬝ᵥ (M *ᵥ x)) * r ^ 2 = x ⬝ᵥ (M *ᵥ x) := by
            field_simp
          linarith
        have hxα : x ⬝ᵥ (M *ᵥ x) ≤ max α 0 := le_trans hx (le_max_left α 0)
        have hr_div : r ^ 2 ≤ max α 0 / c := (le_div_iff₀ hc).mpr (by linarith)
        exact (Real.le_sqrt hr.le (by positivity)).mpr hr_div
  · intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact hstep α _ ih
