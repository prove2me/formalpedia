-- Prove2me | solution 1 for ThreeSum.LightBandPartition.lower_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:29:26.333943+00:00
-- url     : https://prove2.me/submissions/ab3bc907-9938-4c2d-bd93-4ce6b428320f

import Definitions.Def_Submission_ThreeSum_BandPartition
import Definitions.Def_Submission_ThreeSum_LightSmallDivide
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Copy
import Definitions.Def_Submission_ThreeSum_LightBandPartition
import Definitions.Def_WeightedCache3SUM_Alias_231e42e414403f8e
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_Light_wrote_done
import Theorems.Thm_Light_wrote_rest
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPartition
open Light ThreeSum.BandPartition
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandPartition
theorem _root_.solution {p src dst n g d : ℕ} (hp : P[p]? = some lowerBody) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g) (hsrc : src + n ≤ dst) (hdst : dst + size n g ≤ lim.space)
    (hread : ∀ i < n, μ (src + i) = f i) :
    Meets lim P p d [src, dst, size n g, g] μ (lowerTime (size n g))
      (fun _ μ' => (∀ i < size n g, μ' (dst + i) = f (start g i)) ∧ SameOutside μ μ' dst (size n g)) :=
  by
  apply Meets.of_body hp
  unfold lowerBody
  refine
    Ends.pass (fun i => f (start g i)) (fun i hi => ?_)
      ⟨fun i hi => by exact wrote_done (μ := μ) (dst := dst) (f := fun i => f (start g i)) hi, by
        ( try refine _root_.Light.SameOn.cell ?_
          intro x_p2m_11942631147979316701 hx_p2m_11942631147979316701
          first
          | ((  repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_15716175634531661341);
                    (try have := h_p2m_15716175634531661341 x_p2m_11942631147979316701 (by omega));
                    revert h_p2m_15716175634531661341)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          |
            (simp [] at hx_p2m_11942631147979316701;
              ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_9316579308682453010);
                    (try have := h_p2m_9316579308682453010 x_p2m_11942631147979316701 (by omega));
                    revert h_p2m_9316579308682453010)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
          | ( ( repeat
                  ((with_reducible rename _root_.Light.SameOn _ _ _ => h_p2m_6167504098718151841);
                    (try have := h_p2m_6167504098718151841 x_p2m_11942631147979316701 (by omega));
                    revert h_p2m_6167504098718151841)
                intros
                try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
              fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                          SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                          its condition K x does not follow from the hypotheses."))⟩
      hw hdst rfl rfl (hT := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lowerTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [lowerTime] <;>
            first
            | omega
            | (ring_nf; omega)))
  have hidx : i * g < n := start_lt hg hi
  have haddr : ((src : ℤ) + (i : ℤ) * (g : ℤ)).toNat = src + i * g := by rw [← Nat.cast_mul, toNat_natCast_add_natCast]
  have hr : wrote μ dst (fun i => f (start g i)) i (src + i * g) = f (start g i) :=
    by
    rw [wrote_rest (by omega)]
    exact hread _ hidx
  have hmulN : (0 : ℤ) ≤ (i : ℤ) * (g : ℤ) := by positivity
  have hmulBound : (i : ℤ) * (g : ℤ) < (n : ℤ) := by exact_mod_cast hidx
  ( (try have := _root_.Light.Std.space_le (by assumption))
    (try have := _root_.Light.Std.const_le (by assumption))
    simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haddr, hr] <;> omega)
end ThreeSum.LightBandPartition
