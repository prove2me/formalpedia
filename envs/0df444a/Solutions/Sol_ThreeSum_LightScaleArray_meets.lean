-- Prove2me | solution 1 for ThreeSum.LightScaleArray.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:31:24.101777+00:00
-- url     : https://prove2.me/submissions/a9d11c32-8a5e-4282-a12b-78d12952a6a3

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightScaleArray
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_ThreeSum_LightArray_source_read_cast
set_option autoImplicit false
open ThreeSum ThreeSum.LightScaleArray
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightScaleArray
theorem _root_.solution {p src dst n : ℕ} {c : ℤ} {μ : ℕ → ℤ} (hp : P[p]? = some body) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + n ≤ lim.space) (hdst : dst + n ≤ lim.space) (hsep : SourceSafe src dst n)
    (hword : ∀ i < n, |c * μ (src + i)| ≤ lim.word) :
    Meets lim P p d [src, dst, n, c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst + i) = c * μ (src + i)) ∧ SameOutside μ μ' dst n) :=
  by
  refine
    .of_body hp
      (Ends.pass (fun i => c * μ (src + i)) (fun i hi => ?_)
        ⟨fun i hi => wrote_done (f := fun i => c * μ (src + i)) hi, by
          ( try refine _root_.Light.SameOn.cell ?_
            intro x_p2m_1423531246074501831 hx_p2m_1423531246074501831
            first
            | ((  repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_12651208506955202130);
                      (try have := h_p2m_12651208506955202130 x_p2m_1423531246074501831 (by omega));
                      revert h_p2m_12651208506955202130)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            |
              (simp [] at hx_p2m_1423531246074501831;
                ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_8919650475027972705);
                      (try have := h_p2m_8919650475027972705 x_p2m_1423531246074501831 (by omega));
                      revert h_p2m_8919650475027972705)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            | ( ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_14957693892183795725);
                      (try have := h_p2m_14957693892183795725 x_p2m_1423531246074501831 (by omega));
                      revert h_p2m_14957693892183795725)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                            its condition K x does not follow from the hypotheses."))⟩
        hw hdst rfl rfl (hT := by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, time]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [time] <;>
              first
              | omega
              | (ring_nf; omega))))
  have hr := source_read_cast (μ := μ) (f := fun i => c * μ (src + i)) hsep hi
  have hv := abs_le.mp (hword i hi)
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr] <;> omega)
end ThreeSum.LightScaleArray
