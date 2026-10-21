-- Prove2me | solution 1 for RestartPD.LPSharp.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T11:40:52.915022+00:00
-- url     : https://prove2.me/submissions/a21f92a0-90c0-47d7-8c24-c1dd085ca84e

import Mathlib
import Definitions.Def_RestartPD_LPSharp_LP
set_option autoImplicit false
open scoped InnerProductSpace Matrix
open RestartPD.LPSharp
namespace LPSharpProof
variable {n m : ℕ}
lemma le_rho (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z w : PDSpace n m)
    (r : ℝ) (hr : 0 < r) (hw : w ∈ Wball lpX Set.univ r z) :
    ((gapAt (lpL A b c) z w / r : ℝ) : EReal) ≤ rho (lpL A b c) lpX Set.univ r z := by
  rw [rho, if_neg hr.ne']
  exact le_iSup_of_le w (le_iSup_of_le hw le_rfl)
lemma rho_nonneg (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (hz : z.1 ∈ lpX)
    (r : ℝ) (hr : 0 < r) : 0 ≤ rho (lpL A b c) lpX Set.univ r z := by
  have hw : z ∈ Wball lpX Set.univ r z := ⟨⟨hz,Set.mem_univ _⟩,by simpa using hr.le⟩
  simpa [gapAt] using le_rho A b c z z r hr hw
lemma gap_shrink (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (z : PDSpace n m) (t : ℝ) :
    gapAt (lpL A b c) z ((1-t) • z) = t * (⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ) := by
  simp only [gapAt,lpL,Prod.smul_fst,Prod.smul_snd,map_smul,real_inner_smul_left,
    real_inner_smul_right]
  rw [real_inner_comm z.2 b]
  ring
end LPSharpProof
theorem solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : 0 < R) (z : PDSpace n m)
    (hz : z ∈ Wball lpX Set.univ R 0) (r : ℝ) (hr : 0 < r) (hrR : r ≤ R) :
    ((max (⟪c, z.1⟫_ℝ - ⟪b, z.2⟫_ℝ) 0 / R : ℝ) : EReal) ≤
      rho (lpL A b c) lpX Set.univ r z := by
  have ht0 : 0 ≤ r/R := (div_pos hr hR).le
  have ht1 : r/R ≤ 1 := (div_le_one hR).2 hrR
  have hn : eucl n m z ≤ R := by simpa only [zero_sub,map_neg_eq_map] using hz.2
  have hw : (1-r/R) • z ∈ Wball lpX Set.univ r z := by
    refine ⟨⟨?_,Set.mem_univ _⟩,?_⟩
    · intro i
      change 0 ≤ (1-r/R) * z.1 i
      exact mul_nonneg (sub_nonneg.mpr ht1) (hz.1.1 i)
    · have he : z - (1-r/R) • z = (r/R) • z := by module
      rw [he,map_smul_eq_mul,Real.norm_of_nonneg ht0]
      calc
        r/R * eucl n m z ≤ r/R * R := mul_le_mul_of_nonneg_left hn ht0
        _ = r := div_mul_cancel₀ r hR.ne'
  have h := LPSharpProof.le_rho A b c z ((1-r/R) • z) r hr hw
  rw [LPSharpProof.gap_shrink] at h
  have he : r/R * (⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ) / r =
      (⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ)/R := by field_simp
  rw [he] at h
  by_cases hg : 0 ≤ ⟪c,z.1⟫_ℝ - ⟪b,z.2⟫_ℝ
  · simpa only [max_eq_left hg] using h
  · simpa only [max_eq_right (le_of_not_ge hg),zero_div,EReal.coe_zero] using
      LPSharpProof.rho_nonneg A b c z hz.1.1 r hr
