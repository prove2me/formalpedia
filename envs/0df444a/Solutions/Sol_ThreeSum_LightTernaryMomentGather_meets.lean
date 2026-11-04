-- Prove2me | solution 1 for ThreeSum.LightTernaryMomentGather.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:32.879392+00:00
-- url     : https://prove2.me/submissions/abc14b8a-551e-40eb-8b84-c992e67e3725

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryMomentGather
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
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryMomentGather
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightTernaryMomentGather
theorem _root_.solution {p matrix count row scratch terms U : ℕ} (hmain : P[p]? = some body) (μ : ℕ → ℤ) (M : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hr : row < count) (hbefore : matrix + terms * count ≤ scratch)
    (hspace : scratch + terms ≤ lim.space) (hread : ∀ k < terms, μ (matrix + k * count + row) = M k)
    (hbound : ∀ k < terms, |M k| ≤ (U : ℤ)) (hword : (U : ℤ) ≤ lim.word) :
    Meets lim P p d [matrix, count, row, scratch, terms] μ (time terms)
      (fun _ ν => (∀ k < terms, ν (scratch + k) = M k) ∧ SameOutside μ ν scratch terms) :=
  by
  apply Meets.of_body hmain
  unfold body time
  refine
    Ends.pass M ?round
      ⟨fun k hk => by dsimp only; exact wrote_done hk, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_15716175634531661341 hx_p2m_15716175634531661341
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_14070580791908125866);
                    (try have := h_p2m_14070580791908125866 x_p2m_15716175634531661341 (by omega));
                    revert h_p2m_14070580791908125866)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_15716175634531661341;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_12178889891776247892);
                    (try have := h_p2m_12178889891776247892 x_p2m_15716175634531661341 (by omega));
                    revert h_p2m_12178889891776247892)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_3206524611924492242);
                    (try have := h_p2m_3206524611924492242 x_p2m_15716175634531661341 (by omega));
                    revert h_p2m_3206524611924492242)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
      hw hspace rfl rfl
  case round =>
    intro k hk
    have hm := Nat.mul_le_mul_right count (show k + 1 ≤ terms by omega)
    simp only [Nat.add_mul, one_mul] at hm
    have haddr : matrix + k * count + row < scratch := by omega
    have hcur : wrote μ scratch M k (matrix + k * count + row) = M k := (wrote_rest (Or.inl haddr)).trans (hread k hk)
    have hC : (count : ℤ) ≤ lim.word := by
      have hh : count ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hmul : (k : ℤ) * (count : ℤ) ≤ lim.word :=
      by
      have hh : k * count ≤ lim.space := by omega
      have hhZ : (k : ℤ) * (count : ℤ) ≤ (lim.space : ℤ) := by exact_mod_cast hh
      exact hhZ.trans hw
    have hval := abs_le.mp (hbound k hk)
    have hnat : ((matrix : ℤ) + (k : ℤ) * (count : ℤ) + (row : ℤ)).toNat = matrix + k * count + row := by norm_cast
    ( (try have := _root_.Light.Std.space_le (by assumption))
      (try have := _root_.Light.Std.const_le (by assumption))
      simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcur, hnat] <;> omega)
end ThreeSum.LightTernaryMomentGather
