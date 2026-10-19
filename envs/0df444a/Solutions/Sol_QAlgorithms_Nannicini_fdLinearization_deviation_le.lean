-- Prove2me | solution 1 for QAlgorithms.Nannicini.fdLinearization_deviation_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T03:26:20.72055+00:00
-- url     : https://prove2.me/submissions/1559366b-4d75-462f-9f36-f59c58103a2e

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
open QAlgorithms

private lemma endpoint_mem {d : ℕ} (η : ℝ) (hη : 0 ≤ η)
    (z : Fin d → ℝ) (j : Fin d) :
    z + η • Pi.single j 1 ∈ ballL1 z η ∧
      z - η • Pi.single j 1 ∈ ballL1 z η := by
  constructor <;> simp [ballL1, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, Pi.single_apply, apply_ite abs, abs_of_nonneg hη]

private lemma convex_ball_upper {d : ℕ} (η : ℝ) (hη : 0 < η) (z : Fin d → ℝ)
    (G : (Fin d → ℝ) → ℝ) (hG : ConvexOn ℝ (ballL1 z η) G)
    (hGz : G z = 0) (B : ℝ) (hB : 0 ≤ B)
    (hp : ∀ j, G (z + η • Pi.single j 1) ≤ B)
    (hm : ∀ j, G (z - η • Pi.single j 1) ≤ B)
    (y : Fin d → ℝ) (hy : y ∈ ballL1 0 η) : G (z + y) ≤ B := by
  classical
  let w : Fin d → ℝ := fun j => |y j| / η
  let v : Fin d → (Fin d → ℝ) := fun j =>
    (if 0 ≤ y j then η else -η) • Pi.single j 1
  have hw (j : Fin d) : 0 ≤ w j := div_nonneg (abs_nonneg _) hη.le
  have hsum : ∑ j, w j ≤ 1 := by
    dsimp [w]
    rw [← Finset.sum_div, div_le_one hη]
    simpa [ballL1] using hy
  have hv (j : Fin d) : z + v j ∈ ballL1 z η := by
    dsimp [v]
    split_ifs
    · exact (endpoint_mem η hη.le z j).1
    · simpa only [neg_smul, sub_eq_add_neg] using (endpoint_mem η hη.le z j).2
  have hvertex (j : Fin d) : G (z + v j) ≤ B := by
    dsimp [v]
    split_ifs
    · exact hp j
    · simpa only [neg_smul, sub_eq_add_neg] using hm j
  have hrepr : ∑ j, w j • v j = y := by
    ext k
    simp only [Finset.sum_apply, Pi.smul_apply, v, Pi.single_apply, smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    dsimp [w]
    split_ifs with h
    · rw [abs_of_nonneg h]
      field_simp
    · rw [abs_of_neg (lt_of_not_ge h)]
      field_simp
  have hrepr' : (1 - ∑ j, w j) • z + ∑ j, w j • (z + v j) = z + y := by
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hrepr]
    module
  have hz : z ∈ ballL1 z η := by simp [ballL1, hη.le]
  have hj := hG.map_add_sum_le (t := Finset.univ) (w := w) (p := fun j => z + v j)
    (v := 1 - ∑ j, w j) (q := z) (fun j _ => hw j) (by ring)
    (fun j _ => hv j) (sub_nonneg.mpr hsum) hz
  rw [hrepr', hGz, smul_zero, zero_add] at hj
  calc
    G (z + y) ≤ ∑ j, w j • G (z + v j) := hj
    _ ≤ ∑ j, w j * B := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hvertex j) (hw j)
    _ = (∑ j, w j) * B := (Finset.sum_mul _ _ _).symm
    _ ≤ B := by nlinarith

theorem solution {d : ℕ} (η : ℝ) (hη : 0 < η) (z : Fin d → ℝ)
    (f : (Fin d → ℝ) → ℝ) (hf : ConvexOn ℝ (ballL1 z η) f)
    (y : Fin d → ℝ) (hy : y ∈ ballL1 0 η) :
    |f (z + y) - f z - ∑ j, fdGradient η f z j * y j| ≤
      2⁻¹ * η ^ 2 * fdLaplacian η f z := by
  classical
  let a := fdGradient η f z
  let G : (Fin d → ℝ) → ℝ := fun u => f u - f z - ∑ j, a j * (u j - z j)
  let c : Fin d → ℝ := fun j =>
    f (z + η • Pi.single j 1) - 2 * f z + f (z - η • Pi.single j 1)
  let B : ℝ := (∑ j, c j) / 2
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hc (j : Fin d) : 0 ≤ c j := by
    obtain ⟨hp, hm⟩ := endpoint_mem η hη.le z j
    have hh := hf.2 hp hm (show (0 : ℝ) ≤ 1/2 by norm_num)
      (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    have heq : (1/2 : ℝ) • (z + η • Pi.single j 1) +
        (1/2 : ℝ) • (z - η • Pi.single j 1) = z := by module
    rw [heq] at hh
    dsimp [c]
    change f z ≤ 1/2 * _ + 1/2 * _ at hh
    linarith
  have hB : 0 ≤ B := div_nonneg (Finset.sum_nonneg fun j _ => hc j) (by norm_num)
  have hcB (j : Fin d) : c j / 2 ≤ B := by
    dsimp [B]
    exact div_le_div_of_nonneg_right
      (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ j)) (by norm_num)
  have hGz : G z = 0 := by simp [G]
  have hG : ConvexOn ℝ (ballL1 z η) G := by
    refine ⟨hf.1, ?_⟩
    intro u hu v hv s t hs ht hst
    have hh := hf.2 hu hv hs ht hst
    have heq : (∑ j, a j * ((s • u + t • v) j - z j)) =
        s * (∑ j, a j * (u j - z j)) + t * (∑ j, a j * (v j - z j)) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [show t = 1 - s by linarith]
      ring
    dsimp [G]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at heq
    rw [heq]
    change f (s • u + t • v) ≤ s * f u + t * f v at hh
    nlinarith [congrArg (fun r : ℝ => r * f z) hst]
  have hGp (j : Fin d) : G (z + η • Pi.single j 1) = c j / 2 := by
    simp only [G, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
      mul_ite, Pi.single_apply, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    dsimp [a, fdGradient, c]
    field_simp
    ring
  have hGm (j : Fin d) : G (z - η • Pi.single j 1) = c j / 2 := by
    simp only [G, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_sub_cancel_left,
      mul_neg, mul_ite, Pi.single_apply, mul_one, mul_zero, Finset.sum_neg_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    dsimp [a, fdGradient, c]
    field_simp
    ring
  have hu (w : Fin d → ℝ) (hw : w ∈ ballL1 0 η) : G (z + w) ≤ B :=
    convex_ball_upper η hη z G hG hGz B hB
      (fun j => (hGp j).trans_le (hcB j)) (fun j => (hGm j).trans_le (hcB j)) w hw
  have hyneg : -y ∈ ballL1 0 η := by simpa [ballL1] using hy
  have hmid := hG.2
    (show z + y ∈ ballL1 z η by simpa [ballL1] using hy)
    (show z + -y ∈ ballL1 z η by simpa [ballL1] using hyneg)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  have heq : (1/2 : ℝ) • (z + y) + (1/2 : ℝ) • (z + -y) = z := by module
  rw [heq, hGz] at hmid
  have habs : |G (z + y)| ≤ B := by
    rw [abs_le]
    have hupper := hu y hy
    have hlower := hu (-y) hyneg
    simp only [smul_eq_mul] at hmid
    constructor <;> linarith
  have hfinal : B = 2⁻¹ * η ^ 2 * fdLaplacian η f z := by
    dsimp [B, c, fdLaplacian]
    simp only [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  rw [hfinal] at habs
  simpa [G, a] using habs
