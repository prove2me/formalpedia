-- Prove2me | solution 1 for ThreeSum.LightArray.linear_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:32:17.578129+00:00
-- url     : https://prove2.me/submissions/41246dfe-3256-4bb8-a2a3-2ef42086c2ae

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSum_LightArray
import Theorems.Thm_ThreeSum_LightArray_source_read_cast
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_wrote_done
set_option autoImplicit false
open ThreeSum ThreeSum.LightArray
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightArray
theorem _root_.solution {p : ℕ} (hp : P[p]? = some linearBody) {μ : ℕ → ℤ} {srcA srcB dst n : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space) (hD : dst + n ≤ lim.space)
    (hsepA : SourceSafe srcA dst n) (hsepB : SourceSafe srcB dst n) (hmul : ∀ i < n, |c * μ (srcB + i)| ≤ lim.word)
    (hsum : ∀ i < n, |μ (srcA + i) + c * μ (srcB + i)| ≤ lim.word) :
    Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧ SameOutside μ μ' dst n :=
  by
  refine
    .of_body hp
      (Ends.pass (fun i => μ (srcA + i) + c * μ (srcB + i)) (fun i hi => ?_)
        ⟨fun i hi => wrote_done (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hi, by
          ( try refine _root_.Light.SameOn.cell ?_
            intro x_p2m_8281323148958538213 hx_p2m_8281323148958538213
            first
            | ((  repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_11195913957009464594);
                      (try have := h_p2m_11195913957009464594 x_p2m_8281323148958538213 (by omega));
                      revert h_p2m_11195913957009464594)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            |
              (simp [] at hx_p2m_8281323148958538213;
                ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_15502519283113465476);
                      (try have := h_p2m_15502519283113465476 x_p2m_8281323148958538213 (by omega));
                      revert h_p2m_15502519283113465476)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            | ( ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_16163416212241906931);
                      (try have := h_p2m_16163416212241906931 x_p2m_8281323148958538213 (by omega));
                      revert h_p2m_16163416212241906931)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                            its condition K x does not follow from the hypotheses."))⟩
        hw hD rfl rfl (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, linearTime]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [linearTime] <;>
              first
              | omega
              | (ring_nf; omega))))
  have hrA := source_read_cast (μ := μ) (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hsepA hi
  have hrB := source_read_cast (μ := μ) (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hsepB hi
  have hm := abs_le.mp (hmul i hi)
  have hs := abs_le.mp (hsum i hi)
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrA, hrB] <;> omega)
end ThreeSum.LightArray
