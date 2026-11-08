-- Prove2me | solution 1 for Underdogs.eq12_resource_criterion
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:24:16.46585+00:00
-- url     : https://prove2.me/submissions/0319a0f9-92a7-433c-9b98-00cb3c6d5e71

import Mathlib
import Definitions.Def_Underdogs_Params_Standing
import Definitions.Def_Underdogs_Params_posteriorHigh
import Definitions.Def_Underdogs_ofResource

namespace Aux_Underdogs12
open Underdogs MeasureTheory ProbabilityTheory

theorem sumQ (f : Quality → ENNReal) : ∑ q, f q = f Quality.H + f Quality.L := by
  show ∑ q ∈ {Quality.H, Quality.L}, f q = _
  rw [Finset.sum_pair (by simp)]

theorem post_eq (P : Params) (hm : ∀ ω, 0 ≤ P.mass ω) (o1 : Bool) :
    P.posteriorHigh o1 true = P.mass (Quality.H, o1, true) /
      (P.mass (Quality.H, o1, true) + P.mass (Quality.L, o1, true)) := by
  classical
  have hμ : ∀ A : Set (Quality × Bool × Bool),
      P.jointLaw A = ∑ ω, if ω ∈ A then ENNReal.ofReal (P.mass ω) else 0 := by
    intro A
    unfold Params.jointLaw
    rw [Measure.finsetSum_apply]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]
    by_cases hω : ω ∈ A <;> simp [hω]
  have hs : P.jointLaw {ω : Quality × Bool × Bool | ω.2 = (o1, true)} =
      ENNReal.ofReal (P.mass (Quality.H, o1, true)) +
        ENNReal.ofReal (P.mass (Quality.L, o1, true)) := by
    rw [hμ]
    simp only [Fintype.sum_prod_type, sumQ, Fintype.sum_bool]
    cases o1 <;> simp
  have hst : P.jointLaw ({ω : Quality × Bool × Bool | ω.2 = (o1, true)} ∩
      {ω : Quality × Bool × Bool | ω.1 = Quality.H}) =
      ENNReal.ofReal (P.mass (Quality.H, o1, true)) := by
    rw [hμ]
    simp only [Fintype.sum_prod_type, sumQ, Fintype.sum_bool]
    cases o1 <;> simp
  unfold Params.posteriorHigh
  rw [ProbabilityTheory.cond_apply ((Set.toFinite _).measurableSet), hs, hst,
    ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (hm _), ENNReal.toReal_ofReal (hm _), inv_mul_eq_div]

end Aux_Underdogs12

open Underdogs in
theorem solution (g : ℝ → ℝ → ℝ) (l h r1 r2 r3 : ℝ)
    (hP : (ofResource g l h r1 r2 r3).Standing) :
    ((ofResource g l h r1 r2 r3).posteriorHigh false true >
        (ofResource g l h r1 r2 r3).posteriorHigh true true ↔
      g l r1 / g h r1 * ((1 - g l r2) / (1 - g h r2)) < g l r3 / g h r3 * (g l r2 / g h r2)) ∧
    (g l r1 / g h r1 * ((1 - g l r2) / (1 - g h r2)) < g l r3 / g h r3 * (g l r2 / g h r2) ↔
      g h r2 / (1 - g h r2) * (g l r1 / g h r1) < g l r2 / (1 - g l r2) * (g l r3 / g h r3)) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩, ⟨e1, e2⟩, ⟨f1, f2⟩⟩ := hP
  simp only [ofResource] at a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2
  have hm : ∀ ω, 0 ≤ (ofResource g l h r1 r2 r3).mass ω := by
    rintro ⟨q, o1, o2⟩
    unfold Params.mass
    simp only [ofResource]
    apply mul_nonneg (mul_nonneg (by norm_num) ?_) ?_ <;> split_ifs <;> linarith
  rw [gt_iff_lt, Aux_Underdogs12.post_eq _ hm, Aux_Underdogs12.post_eq _ hm]
  simp only [Params.mass, ofResource, eq_self_iff_true, reduceCtorEq, Bool.false_eq_true,
    ↓reduceIte, if_true, if_false]
  set ph := g h r2
  set pl := g l r2
  set phS := g h r3
  set plS := g l r3
  set phF := g h r1
  set plF := g l r1
  have u1 : 0 < 1 - ph := by linarith
  have u2 : 0 < 1 - pl := by linarith
  have A1 : 0 < 1 / 2 * (1 - ph) * phF := by
    have := mul_pos u1 e1; linarith
  have A2 : 0 < 1 / 2 * (1 - pl) * plF := by
    have := mul_pos u2 f1; linarith
  have A3 : 0 < 1 / 2 * ph * phS := by
    have := mul_pos a1 c1; linarith
  have A4 : 0 < 1 / 2 * pl * plS := by
    have := mul_pos b1 d1; linarith
  simp only [div_mul_div_comm]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  rw [div_lt_div_iff₀ (mul_pos e1 u1) (mul_pos c1 a1)]
  rw [div_lt_div_iff₀ (mul_pos u1 e1) (mul_pos u2 c1)]
  constructor
  · constructor <;> intro hh <;> nlinarith
  · constructor <;> intro hh <;> nlinarith
