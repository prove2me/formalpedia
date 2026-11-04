-- Prove2me | solution 1 for ThreeSum.LightTernaryProduct.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:31:28.008757+00:00
-- url     : https://prove2.me/submissions/95667cc7-7aea-4960-b020-5bec2dacf15b

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryProduct
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_ThreeSum_LightArray_source_read_cast
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryProduct
open Light ThreeSum.LightArray
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryProduct
theorem _root_.solution {p a b dst n U V : ℕ} (hprog : P[p]? = some body) (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + n ≤ lim.space) (hb : b + n ≤ lim.space) (hdst : dst + n ≤ lim.space) (hsepA : SourceSafe a dst n)
    (hsepB : SourceSafe b dst n) (hA : ∀ j < n, |μ (a + j)| ≤ U) (hB : ∀ j < n, |μ (b + j)| ≤ V)
    (hword : (U : ℤ) * (V : ℤ) ≤ lim.word) :
    Meets lim P p d [a, b, dst, n] μ (time n)
      (fun _ μ' => (∀ j < n, μ' (dst + j) = μ (a + j) * μ (b + j)) ∧ SameOutside μ μ' dst n) :=
  by
  apply Meets.of_body hprog
  unfold body time
  refine
    Ends.pass (fun j => μ (a + j) * μ (b + j)) (fun j hj => ?_)
      ⟨fun j hj => wrote_done (f := fun j => μ (a + j) * μ (b + j)) hj, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_13949945568761573396 hx_p2m_13949945568761573396
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9146430557733125380);
                    (try have := h_p2m_9146430557733125380 x_p2m_13949945568761573396 (by omega));
                    revert h_p2m_9146430557733125380)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_13949945568761573396;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_5639388193974934293);
                    (try have := h_p2m_5639388193974934293 x_p2m_13949945568761573396 (by omega));
                    revert h_p2m_5639388193974934293)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_169112293001390194);
                    (try have := h_p2m_169112293001390194 x_p2m_13949945568761573396 (by omega));
                    revert h_p2m_169112293001390194)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
      hw hdst rfl rfl (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
  have hrA := source_read_cast (μ := μ) (f := fun j => μ (a + j) * μ (b + j)) hsepA hj
  have hrB := source_read_cast (μ := μ) (f := fun j => μ (a + j) * μ (b + j)) hsepB hj
  have hprod : |μ (a + j) * μ (b + j)| ≤ (U : ℤ) * (V : ℤ) :=
    by
    rw [abs_mul]
    exact mul_le_mul (hA j hj) (hB j hj) (abs_nonneg _) (Int.natCast_nonneg _)
  have hbounds := abs_le.mp (hprod.trans hword)
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrA, hrB] <;> omega)
end ThreeSum.LightTernaryProduct
