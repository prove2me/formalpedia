-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentAccumulate.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:28:14.525075+00:00
-- url     : https://prove2.me/submissions/82a78633-ab4c-4426-b8f0-ddee6a733419

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentAccumulate
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_ThreeSum_LightArray_source_read
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentAccumulate
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentAccumulate
theorem _root_.solution {p dst src count U : ℕ} (hmain : P[p]? = some body) (μ : ℕ → ℤ) (accum channel : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + count ≤ lim.space) (hsrc : src + count ≤ lim.space)
    (hsep : LightArray.SourceSafe src dst count) (haccum : ∀ i < count, μ (dst + i) = accum i)
    (hchannel : ∀ i < count, μ (src + i) = channel i)
    (hbounded : ∀ i < count, |accum i| ≤ (U : ℤ) ∧ |channel i| ≤ (U : ℤ)) (hword : 2 * (U : ℤ) ≤ lim.word) :
    Meets lim P p d [dst, src, count] μ (time count)
      (fun _ ν => (∀ i < count, ν (dst + i) = accum i + channel i) ∧ SameOutside μ ν dst count) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.pass (fun i => accum i + channel i) ?round
      ⟨fun i hi => by dsimp only; exact wrote_done hi, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_6167504098718151841 hx_p2m_6167504098718151841
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_3206524611924492242);
                    (try have := h_p2m_3206524611924492242 x_p2m_6167504098718151841 (by omega));
                    revert h_p2m_3206524611924492242)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_6167504098718151841;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_547304534646509777);
                    (try have := h_p2m_547304534646509777 x_p2m_6167504098718151841 (by omega));
                    revert h_p2m_547304534646509777)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9146430557733125380);
                    (try have := h_p2m_9146430557733125380 x_p2m_6167504098718151841 (by omega));
                    revert h_p2m_9146430557733125380)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
      hw hdst rfl rfl
  case round =>
    intro i hi
    have hrA :=
      LightArray.source_read (μ := μ) (f := fun i => accum i + channel i)
        (show LightArray.SourceSafe dst dst count from Or.inl rfl) hi
    have hrB := LightArray.source_read (μ := μ) (f := fun i => accum i + channel i) hsep hi
    have hA := haccum i hi
    have hB := hchannel i hi
    have hmemA : wrote μ dst (fun k => accum k + channel k) i (dst + i) = accum i := hrA.trans hA
    have hmemB : wrote μ dst (fun k => accum k + channel k) i (src + i) = channel i := hrB.trans hB
    have hbounds := hbounded i hi
    have hU : (U : ℤ) ≤ lim.word := by omega
    have hsum : |accum i + channel i| ≤ lim.word :=
      (abs_add_le _ _).trans ((add_le_add hbounds.1 hbounds.2).trans (by omega))
    have hs := abs_le.mp hsum
    have ha := abs_le.mp hbounds.1
    have hb := abs_le.mp hbounds.2
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrA, hrB, hA, hB, hmemA, hmemB] <;> omega)
end ThreeSum.LightTernaryMomentAccumulate
