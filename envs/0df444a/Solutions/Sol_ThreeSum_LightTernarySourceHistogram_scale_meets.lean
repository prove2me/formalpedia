-- Prove2me | solution 1 for ThreeSum.LightTernarySourceHistogram.scale_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:28.26004+00:00
-- url     : https://prove2.me/submissions/87b1a026-b5ca-4377-9621-9641382c6db6

import Definitions.Def_Submission_ThreeSum_LightTernarySourceKeys
import Definitions.Def_Submission_ThreeSum_LightTernarySourceHistogram
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_ThreeSum_LightArray_source_read_cast
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernarySourceHistogram
open Light ThreeSum.LightArray ThreeSum.LightSubsetAddress
set_option maxHeartbeats 2000000
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernarySourceHistogram
theorem _root_.solution {p base n U : ℕ} (hp : P[p]? = some scaleBody) (μ : ℕ → ℤ) (weight : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase : base + n ≤ lim.space) (hvalues : ∀ j < n, |μ (base + j)| ≤ U)
    (hweight : (weight : ℤ) ≤ lim.word) (hword : (weight : ℤ) * (U : ℤ) ≤ lim.word) :
    Meets lim P p d [base, n, weight] μ (scaleTime n)
      (fun _ μ' => (∀ j < n, μ' (base + j) = (weight : ℤ) * μ (base + j)) ∧ SameOutside μ μ' base n) :=
  by
  apply Meets.of_body hp
  unfold scaleBody scaleTime
  refine
    Ends.pass (fun j => (weight : ℤ) * μ (base + j)) (fun j hj => ?_)
      ⟨fun j hj => wrote_done (f := fun j => (weight : ℤ) * μ (base + j)) hj, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_14957693892183795725 hx_p2m_14957693892183795725
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_283536084893174559);
                    (try have := h_p2m_283536084893174559 x_p2m_14957693892183795725 (by omega));
                    revert h_p2m_283536084893174559)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_14957693892183795725;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_7381761724271039138);
                    (try have := h_p2m_7381761724271039138 x_p2m_14957693892183795725 (by omega));
                    revert h_p2m_7381761724271039138)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_11195913957009464594);
                    (try have := h_p2m_11195913957009464594 x_p2m_14957693892183795725 (by omega));
                    revert h_p2m_11195913957009464594)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
      hw hbase rfl rfl (hT := by
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
  have hread :=
    source_read_cast (μ := μ) (f := fun j => (weight : ℤ) * μ (base + j)) (show SourceSafe base base n from Or.inl rfl)
      hj
  have hprod : |(weight : ℤ) * μ (base + j)| ≤ (weight : ℤ) * (U : ℤ) :=
    by
    rw [abs_mul, abs_of_nonneg (Int.natCast_nonneg weight)]
    exact mul_le_mul_of_nonneg_left (hvalues j hj) (Int.natCast_nonneg weight)
  have hb := abs_le.mp (hprod.trans hword)
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread] <;> omega)
end ThreeSum.LightTernarySourceHistogram
