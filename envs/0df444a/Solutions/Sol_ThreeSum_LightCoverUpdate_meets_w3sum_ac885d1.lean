-- Prove2me | solution 1 for ThreeSum.LightCoverUpdate.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:09.440194+00:00
-- url     : https://prove2.me/submissions/b13cf338-9ec8-4a9b-911b-4f047ce99c07

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightCoverUpdate
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverUpdate
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightCoverUpdate
theorem _root_.solution {p : ℕ} (hp : P[p]? = some body) {μ : ℕ → ℤ} {row activePtr n : ℕ} (cover active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hrow : row + n ≤ lim.space) (hactive : activePtr + n ≤ lim.space)
    (hsep : Apart row n activePtr n) (hread : ∀ j < n, μ (row + j) = (cover j : ℤ))
    (hreadActive : ∀ j < n, μ (activePtr + j) = (active j : ℤ)) (hcover : ∀ j < n, cover j ≤ 1)
    (hact : ∀ j < n, active j ≤ 1) (hword : (1 : ℤ) ≤ lim.word) :
    Meets lim P p d [row, activePtr, n] μ (time n)
      (fun _ μ' =>
        (∀ j < n, μ' (activePtr + j) = ((active j * (1 - cover j) : ℕ) : ℤ)) ∧ SameOutside μ μ' activePtr n) :=
  by
  have he (j : ℕ) (hj : j < n) : ((active j * (1 - cover j) : ℕ) : ℤ) = (active j : ℤ) * (1 - (cover j : ℤ)) :=
    by
    rw [Nat.cast_mul, Nat.cast_sub (hcover j hj)]
    norm_num
  refine
    Meets.of_body hp
      (Ends.pass (fun j => (active j : ℤ) * (1 - (cover j : ℤ))) (fun j hj => ?_)
        ⟨fun j hj =>
          (wrote_done (μ := μ) (dst := activePtr) (f := fun j => (active j : ℤ) * (1 - (cover j : ℤ))) hj).trans
            (he j hj).symm,
          by
          ( try refine _root_.Light.SameOn.cell ?_
            intro x_p2m_5839408668684879090 hx_p2m_5839408668684879090
            first
            | ((  repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_12331174817228662740);
                      (try have := h_p2m_12331174817228662740 x_p2m_5839408668684879090 (by omega));
                      revert h_p2m_12331174817228662740)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            |
              (simp [] at hx_p2m_5839408668684879090;
                ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_5403297131883402289);
                      (try have := h_p2m_5403297131883402289 x_p2m_5839408668684879090 (by omega));
                      revert h_p2m_5403297131883402289)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            | ( ( repeat
                    ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_6816054536980055908);
                      (try have := h_p2m_6816054536980055908 x_p2m_5839408668684879090 (by omega));
                      revert h_p2m_6816054536980055908)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                            its condition K x does not follow from the hypotheses."))⟩
        hw hactive rfl rfl (hT := by
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
  have hr :
    wrote μ activePtr (fun j => (active j : ℤ) * (1 - (cover j : ℤ))) j ((row : ℤ) + (j : ℤ)).toNat = μ (row + j) :=
    by
    have hc : ((row : ℤ) + (j : ℤ)).toNat = row + j := by simp
    rw [hc]
    exact wrote_rest (by omega)
  have ha :
    wrote μ activePtr (fun j => (active j : ℤ) * (1 - (cover j : ℤ))) j ((activePtr : ℤ) + (j : ℤ)).toNat =
      μ (activePtr + j) :=
    by
    have hc : ((activePtr : ℤ) + (j : ℤ)).toNat = activePtr + j := by simp
    rw [hc]
    exact wrote_rest (by omega)
  have hrNat : wrote μ activePtr (fun j => (active j : ℤ) * (1 - (cover j : ℤ))) j (row + j) = μ (row + j) :=
    wrote_rest (by omega)
  have haNat :
    wrote μ activePtr (fun j => (active j : ℤ) * (1 - (cover j : ℤ))) j (activePtr + j) = μ (activePtr + j) :=
    wrote_rest (by omega)
  have hrc := hread j hj
  have hac := hreadActive j hj
  have hc := hcover j hj
  have hav := hact j hj
  have hcZ : (0 : ℤ) ≤ 1 - (cover j : ℤ) ∧ 1 - (cover j : ℤ) ≤ 1 := by omega
  have hpZ : (0 : ℤ) ≤ (active j : ℤ) * (1 - (cover j : ℤ)) ∧ (active j : ℤ) * (1 - (cover j : ℤ)) ≤ 1 :=
    by
    constructor
    · exact mul_nonneg (Int.natCast_nonneg _) hcZ.1
    · exact (mul_le_mul (by exact_mod_cast hav : (active j : ℤ) ≤ 1) hcZ.2 hcZ.1 (by norm_num)).trans (by norm_num)
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr, ha, hrNat, haNat, hrc, hac] <;> omega)
end ThreeSum.LightCoverUpdate
