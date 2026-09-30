-- Prove2me | solution 1 for UnderstandingML.subspace_covering
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T17:43:49.739792+00:00
-- url     : https://prove2.me/submissions/dc303861-4f9f-4c47-8eb8-38a2ecb1258f

import Definitions.Def_UnderstandingML_Covering
import Mathlib.Analysis.InnerProductSpace.PiL2

open MeasureTheory

namespace UnderstandingML.SubspaceCoveringAux

lemma eucNorm_eq_norm {m : ℕ} (v : Fin m → ℝ) : eucNorm v = ‖WithLp.toLp 2 v‖ := by
  rw [EuclideanSpace.norm_eq, eucNorm]
  simp [Real.norm_eq_abs, sq_abs]

/-- Rounding down to the grid `{−c, −c + ε, …, −c + Kε}` with `K = ⌊2c/ε⌋`: a point of `[−c, c]`
is within `ε` of a grid point, from above. -/
lemma exists_grid {c ε y : ℝ} (hε : 0 < ε) (hy : |y| ≤ c) :
    ∃ t : ℕ, t ≤ ⌊2 * c / ε⌋₊ ∧ (y - (-c + ε * t)) ^ 2 ≤ ε ^ 2 := by
  have hyc : 0 ≤ y + c := by linarith [neg_abs_le y]
  refine ⟨⌊(y + c) / ε⌋₊, Nat.floor_mono ?_, ?_⟩
  · gcongr; linarith [le_abs_self y]
  · have h1 : ((⌊(y + c) / ε⌋₊ : ℕ) : ℝ) ≤ (y + c) / ε := Nat.floor_le (by positivity)
    have h2 : (y + c) / ε < ⌊(y + c) / ε⌋₊ + 1 := Nat.lt_floor_add_one _
    have h1' : ε * ⌊(y + c) / ε⌋₊ ≤ y + c := by
      rw [le_div_iff₀ hε] at h1; linarith
    have h2' : y + c < ε * (⌊(y + c) / ε⌋₊ + 1) := by
      rw [div_lt_iff₀ hε] at h2; linarith
    have h3 : 0 ≤ y - (-c + ε * ⌊(y + c) / ε⌋₊) := by linarith
    have h4 : y - (-c + ε * ⌊(y + c) / ε⌋₊) ≤ ε := by linarith
    nlinarith

end UnderstandingML.SubspaceCoveringAux

open UnderstandingML UnderstandingML.SubspaceCoveringAux in
theorem solution {m d : ℕ} (A : Set (Fin m → ℝ)) (V : Submodule ℝ (Fin m → ℝ))
    (hV : Module.finrank ℝ V = d) (hAV : A ⊆ V) (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ a ∈ A, eucNorm a ≤ c) (r : ℝ)
    (hr : 0 < r) :
    ∃ A' : Finset (Fin m → ℝ), IsCover r A A' ∧
      (A'.card : ℝ) ≤ (2 * c * Real.sqrt d / r + 1) ^ d := by
  classical
  -- the subspace inside Euclidean space, and an orthonormal basis of it indexed by `Fin d`
  set W : Submodule ℝ (EuclideanSpace ℝ (Fin m)) :=
    V.map (WithLp.linearEquiv 2 ℝ (Fin m → ℝ)).symm.toLinearMap with hW
  have hWd : Module.finrank ℝ W = d := by
    rw [hW, LinearEquiv.finrank_map_eq, hV]
  have hmemW : ∀ a ∈ A, WithLp.toLp 2 a ∈ W := fun a ha ↦ ⟨a, hAV ha, rfl⟩
  let b : OrthonormalBasis (Fin d) ℝ W := (stdOrthonormalBasis ℝ W).reindex (finCongr hWd)
  -- the grid step
  set ε : ℝ := r / Real.sqrt d with hε
  set K : ℕ := ⌊2 * c / ε⌋₊ with hK
  -- grid points
  let g : (Fin d → Fin (K + 1)) → Fin m → ℝ := fun t ↦
    ((b.repr.symm (WithLp.toLp 2 (fun j ↦ -c + ε * (t j : ℕ))) : W) : EuclideanSpace ℝ (Fin m)).ofLp
  refine ⟨Finset.univ.image g, ?_, ?_⟩
  · intro a ha
    set w : W := ⟨WithLp.toLp 2 a, hmemW a ha⟩
    set y : EuclideanSpace ℝ (Fin d) := b.repr w
    have hy : ‖y‖ ≤ c := by
      rw [LinearIsometryEquiv.norm_map, Submodule.coe_norm, ← eucNorm_eq_norm]
      exact hc a ha
    -- round each coordinate
    have hround : ∀ j : Fin d, ∃ t : Fin (K + 1), (y.ofLp j - (-c + ε * (t : ℕ))) ^ 2 ≤ ε ^ 2 := by
      intro j
      have hd : 0 < d := Fin.pos j
      have hεpos : 0 < ε := div_pos hr (Real.sqrt_pos.2 (by exact_mod_cast hd))
      have hyj : |y.ofLp j| ≤ c := by
        have := PiLp.norm_apply_le y j
        rw [Real.norm_eq_abs] at this
        exact this.trans hy
      obtain ⟨t, htK, ht⟩ := exists_grid hεpos hyj
      exact ⟨⟨t, Nat.lt_succ_of_le htK⟩, ht⟩
    choose t ht using hround
    refine ⟨g t, Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    set z : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j ↦ -c + ε * (t j : ℕ))
    have hnorm : eucNorm (a - g t) = ‖y - z‖ := by
      rw [eucNorm_eq_norm, WithLp.toLp_sub]
      simp only [g, WithLp.toLp_ofLp]
      have : WithLp.toLp 2 a = (w : EuclideanSpace ℝ (Fin m)) := rfl
      rw [this, ← Submodule.coe_sub, ← Submodule.coe_norm, ← LinearIsometryEquiv.norm_map b.repr,
        map_sub, LinearIsometryEquiv.apply_symm_apply]
    rw [hnorm, EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    refine ⟨hr.le, ?_⟩
    calc ∑ j, ‖(y - z).ofLp j‖ ^ 2 ≤ ∑ _j : Fin d, ε ^ 2 := by
          refine Finset.sum_le_sum (fun j _ ↦ ?_)
          rw [Real.norm_eq_abs, sq_abs]
          simpa [z] using ht j
      _ = d * ε ^ 2 := by simp
      _ ≤ r ^ 2 := by
          rcases Nat.eq_zero_or_pos d with hd | hd
          · simp [hd]; positivity
          · rw [hε, div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
            field_simp
            rfl
  · calc (((Finset.univ : Finset (Fin d → Fin (K + 1))).image g).card : ℝ)
        ≤ ((Finset.univ : Finset (Fin d → Fin (K + 1))).card : ℝ) := by
          exact_mod_cast Finset.card_image_le
      _ = ((K : ℝ) + 1) ^ d := by simp
      _ ≤ (2 * c * Real.sqrt d / r + 1) ^ d := by
          gcongr
          have h1 : (K : ℝ) ≤ 2 * c / ε := Nat.floor_le (by
            rw [hε]; positivity)
          have h2 : 2 * c / ε = 2 * c * Real.sqrt d / r := by
            rw [hε, div_div_eq_mul_div]
          linarith
