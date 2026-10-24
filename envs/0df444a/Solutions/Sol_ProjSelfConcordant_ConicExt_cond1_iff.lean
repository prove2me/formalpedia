-- Prove2me | solution 1 for ProjSelfConcordant.ConicExt.cond1_iff
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T07:24:40.372203+00:00
-- url     : https://prove2.me/submissions/6331c28e-9c7e-4f7b-b508-0320f6d3806b

import Mathlib
import Definitions.Def_ProjSelfConcordant_ConicExt_Setting
import Theorems.Thm_ProjSelfConcordant_ConicExt_hessian_third_expansion
import Theorems.Thm_ProjSelfConcordant_ConicExt_hessian_third_homogeneous

open ProjSelfConcordant.ConicExt

namespace Cond1Aux

theorem from_identities {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 0 < ν)
    (hexp : ∀ x ∈ D, ∀ (v : EuclideanSpace ℝ (Fin n)) (a : ℝ),
      dk 2 (homExt ν f) (1, x) (a, v + a • x) =
        ν * (a ^ 2 - 2 * a * dk 1 f x v + dk 2 f x v))
    (hhom : ∀ q ∈ conicExt D, ∀ (h : ℝ × EuclideanSpace ℝ (Fin n)) (t : ℝ),
      0 < t → dk 2 (homExt ν f) (t • q) (t • h) = dk 2 (homExt ν f) q h) :
    ProjCond1 D f ↔ AffCond1 (conicExt D) (homExt ν f) := by
  constructor
  · intro hproj
    have hslice (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D)
        (h : ℝ × EuclideanSpace ℝ (Fin n)) (hh : h ≠ 0) :
        0 < dk 2 (homExt ν f) (1, x) h := by
      let v := h.2 - h.1 • x
      have heq : (h.1, v + h.1 • x) = h := by
        apply Prod.ext
        · rfl
        · dsimp [v]
          exact sub_add_cancel _ _
      have hex := hexp x hx v h.1
      rw [heq] at hex
      rw [hex]
      apply mul_pos hν
      by_cases hv : v = 0
      · have ha : h.1 ≠ 0 := by
          intro ha
          have hb : h.2 = 0 := by simpa only [v, ha, zero_smul, sub_zero] using hv
          exact hh (Prod.ext ha hb)
        have hz1 : dk 1 f x 0 = 0 := (iteratedFDeriv ℝ 1 f x).map_coord_zero (0 : Fin 1) rfl
        have hz2 : dk 2 f x 0 = 0 := (iteratedFDeriv ℝ 2 f x).map_coord_zero (0 : Fin 2) rfl
        simpa only [hv, hz1, hz2, mul_zero, sub_zero, add_zero] using sq_pos_of_ne_zero ha
      · have hpos := hproj x hx v hv
        nlinarith [sq_nonneg (h.1 - dk 1 f x v)]
    intro q hq h hh
    have ht : 0 < q.1⁻¹ := inv_pos.mpr hq.1
    have hscaled : q.1⁻¹ • h ≠ 0 := smul_ne_zero (ne_of_gt ht) hh
    have hnormalize : q.1⁻¹ • q = (1, q.1⁻¹ • q.2) := by
      apply Prod.ext
      · exact inv_mul_cancel₀ (ne_of_gt hq.1)
      · rfl
    have hpos := hslice (q.1⁻¹ • q.2) hq.2 (q.1⁻¹ • h) hscaled
    have heq := hhom q hq h q.1⁻¹ ht
    rw [hnormalize] at heq
    exact heq ▸ hpos
  · intro haff x hx v hv
    let a := dk 1 f x v
    have hslice : ((1 : ℝ), x) ∈ conicExt D := ⟨zero_lt_one, by simpa using hx⟩
    have hnonzero : (a, v + a • x) ≠ (0 : ℝ × EuclideanSpace ℝ (Fin n)) := by
      intro hz
      have ha : a = 0 := congrArg Prod.fst hz
      have hb := congrArg Prod.snd hz
      exact hv (by simpa only [ha, zero_smul, add_zero, Prod.snd_zero] using hb)
    have hpos := haff (1, x) hslice (a, v + a • x) hnonzero
    rw [hexp x hx v a] at hpos
    have hinner : 0 < a ^ 2 - 2 * a * dk 1 f x v + dk 2 f x v :=
      (mul_pos_iff_of_pos_left hν).mp hpos
    dsimp [a] at hinner
    nlinarith

end Cond1Aux

theorem solution {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n)))
    (hDo : IsOpen D) (hDc : Convex ℝ D)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiffOn ℝ 3 f D) (ν : ℝ) (hν : 2 ≤ ν) :
    ProjCond1 D f ↔ AffCond1 (conicExt D) (homExt ν f) := by
  apply Cond1Aux.from_identities D f ν (by linarith)
  · intro x hx v a
    exact (ProjSelfConcordant.ConicExt.hessian_third_expansion D hDo hDc f hf ν x hx v a).1
  · intro q hq h t ht
    exact (ProjSelfConcordant.ConicExt.hessian_third_homogeneous D hDo hDc f hf ν q hq h t ht).1
