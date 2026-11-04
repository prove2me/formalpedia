-- Prove2me | solution 1 for ThreeSum.LightReportingGather.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:01:03.165199+00:00
-- url     : https://prove2.me/submissions/ee228fbb-4371-4b7e-ad31-8d43af0757ad

import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightReportingFilter.mem_selected
attribute [local simp] ThreeSum.LightReportingFilter.selected_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingGather
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingGather
theorem _root_.solution {μ : ℕ → ℤ} {p indices src dst t n d : ℕ} (hp : P[p]? = some body) (index : ℕ → ℕ)
    (value : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hindices : indices + t ≤ lim.space) (hsrc : src + n ≤ lim.space)
    (hdst : dst + t ≤ lim.space) (hsepI : Apart indices t dst t) (hsepS : Apart src n dst t)
    (hindex : ∀ i < t, index i < n) (hreadI : ∀ i < t, μ (indices + i) = (index i : ℤ))
    (hreadS : ∀ i < n, μ (src + i) = value i) (hword : ∀ i < n, |value i| ≤ lim.word) :
    Meets lim P p d [indices, src, dst, t, n] μ (time t)
      (fun _ ν => (∀ i < t, ν (dst + i) = value (index i)) ∧ SameOutside μ ν dst t) :=
  by
  refine
    .of_body hp
      (Ends.pass (fun i => value (index i)) (fun i hi => ?_)
        ⟨fun i hi => wrote_done (f := fun i => value (index i)) hi, by
          ( try refine _root_.Light.SameOn.cell ?_
            intro x_p2m_8919650475027972705 hx_p2m_8919650475027972705
            first
            | ((  repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9452156437725958651);
                      (try have := h_p2m_9452156437725958651 x_p2m_8919650475027972705 (by omega));
                      revert h_p2m_9452156437725958651)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            |
              (simp [] at hx_p2m_8919650475027972705;
                ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_283536084893174559);
                      (try have := h_p2m_283536084893174559 x_p2m_8919650475027972705 (by omega));
                      revert h_p2m_283536084893174559)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            | ( ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_7381761724271039138);
                      (try have := h_p2m_7381761724271039138 x_p2m_8919650475027972705 (by omega));
                      revert h_p2m_7381761724271039138)
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
  have hidx := hindex i hi
  have hreadIdx : wrote μ dst (fun i => value (index i)) i ((indices : ℤ) + (i : ℤ)).toNat = (index i : ℤ) :=
    by
    have hc : ((indices : ℤ) + (i : ℤ)).toNat = indices + i := by simp
    rw [hc]
    exact (wrote_rest (by rcases hsepI with h | h <;> omega)).trans (hreadI i hi)
  have hreadIdxNat : wrote μ dst (fun i => value (index i)) i (indices + i) = (index i : ℤ) :=
    (wrote_rest (by rcases hsepI with h | h <;> omega)).trans (hreadI i hi)
  have hreadVal : wrote μ dst (fun i => value (index i)) i ((src : ℤ) + (index i : ℤ)).toNat = value (index i) :=
    by
    have hc : ((src : ℤ) + (index i : ℤ)).toNat = src + index i := by simp
    rw [hc]
    exact (wrote_rest (by rcases hsepS with h | h <;> omega)).trans (hreadS _ hidx)
  have hreadValNat : wrote μ dst (fun i => value (index i)) i (src + index i) = value (index i) :=
    (wrote_rest (by rcases hsepS with h | h <;> omega)).trans (hreadS _ hidx)
  have hv := abs_le.mp (hword _ hidx)
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadIdx, hreadIdxNat, hreadVal, hreadValNat] <;>
      omega)
end ThreeSum.LightReportingGather
