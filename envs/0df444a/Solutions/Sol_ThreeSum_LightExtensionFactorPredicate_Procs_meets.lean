-- Prove2me | solution 1 for ThreeSum.LightExtensionFactorPredicate.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:20.897614+00:00
-- url     : https://prove2.me/submissions/72808eb5-d8a4-4661-ae8e-e50cafe33740

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorCheck
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightCoefficientDecode_meets
import Theorems.Thm_ThreeSum_LightExtensionFactorCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Definitions.Def_WeightedCache3SUM_Alias_e6a24ed55341e959
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightExtensionFactorPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
attribute [local instance] ThreeSum.LightExtensionFactorPredicate._p2m_local_instance_595e8f8b6a_7
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionFactorPredicate
namespace Procs
theorem _root_.solution {main ctx u v : ℕ} (S : Procs P main) (C : Layout) (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 4 < lim.depth) (hp : 1 < C.p) (he : 0 < C.degree)
    (hed : C.degree < C.dim) (H : Seg μ ctx (header C)) (hctx : ctx + 7 ≤ C.left)
    (hpow : C.powers + (2 * C.dim + 1) ≤ C.left) (htarget : C.target + 2 * C.dim ≤ C.left)
    (hleft : C.left + 2 * C.dim ≤ C.right) (hspace : C.right + 2 * C.dim ≤ lim.space)
    (hpowRead : ∀ i ≤ 2 * C.dim, μ (C.powers + i) = ((C.p ^ i : ℕ) : ℤ))
    (hfRead : ∀ i < 2 * C.dim, μ (C.target + i) = (f i : ℤ)) (hword : (word C u v : ℤ) ≤ lim.word) :
    Meets lim P main depth [u, v, ctx] μ (time C u v) (fun z ν => z = result C f u v ∧ Kept μ ν C.left) :=
  by
  have h0 := H 0 (by simp [header])
  have h1 := H 1 (by simp [header])
  have h2 := H 2 (by simp [header])
  have h3 := H 3 (by simp [header])
  have h4 := H 4 (by simp [header])
  have h5 := H 5 (by simp [header])
  have h6 := H 6 (by simp [header])
  simp only [header, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6
  have ha0 : ((ctx : ℤ) + 0).toNat = ctx + 0 := by omega
  have ha1 : ((ctx : ℤ) + 1).toNat = ctx + 1 := by omega
  have ha2 : ((ctx : ℤ) + 2).toNat = ctx + 2 := by omega
  have ha3 : ((ctx : ℤ) + 3).toNat = ctx + 3 := by omega
  have ha4 : ((ctx : ℤ) + 4).toNat = ctx + 4 := by omega
  have ha5 : ((ctx : ℤ) + 5).toNat = ctx + 5 := by omega
  have ha6 : ((ctx : ℤ) + 6).toNat = ctx + 6 := by omega
  have hpeAddr : ((C.powers : ℤ) + (C.degree : ℤ)).toNat = C.powers + C.degree := by omega
  have hpgAddr : ((C.powers : ℤ) + (C.dim : ℤ) - (C.degree : ℤ)).toNat = C.powers + (C.dim - C.degree) := by omega
  have hpe := hpowRead C.degree (by omega)
  have hpg := hpowRead (C.dim - C.degree) (by omega)
  have hwCore :
    (LightExtensionFactorCheck.word C.dim C.degree C.p (u + C.p ^ C.degree) (v + C.p ^ (C.dim - C.degree)) : ℤ) ≤
      lim.word :=
    by unfold word at hword; omega
  have hpowMax : ((C.p ^ (2 * C.dim + 1) : ℕ) : ℤ) ≤ lim.word :=
    by
    unfold LightExtensionFactorCheck.word LightCoefficientDecode.word at hwCore
    omega
  have hpeWord : ((C.p ^ C.degree : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega) (by omega))).trans hpowMax
  have hpgWord : ((C.p ^ (C.dim - C.degree) : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega) (by omega))).trans hpowMax
  have huWord : (u : ℤ) ≤ lim.word := by
    unfold LightExtensionFactorCheck.word LightCoefficientDecode.word at hwCore
    omega
  have hvWord : (v : ℤ) ≤ lim.word := by
    unfold LightExtensionFactorCheck.word LightCoefficientDecode.word at hwCore
    omega
  have hpWord : (C.p : ℤ) ≤ lim.word := by
    unfold LightExtensionFactorCheck.word LightCoefficientDecode.word at hwCore
    omega
  have hupWord : ((u + C.p ^ C.degree : ℕ) : ℤ) ≤ lim.word := by
    unfold LightExtensionFactorCheck.word LightCoefficientDecode.word at hwCore; omega
  have hvpWord : ((v + C.p ^ (C.dim - C.degree) : ℕ) : ℤ) ≤ lim.word := by
    unfold LightExtensionFactorCheck.word LightCoefficientDecode.word at hwCore; omega
  have hupInt : (u : ℤ) + (C.p : ℤ) ^ C.degree ≤ lim.word := by exact_mod_cast hupWord
  have hvpInt : (v : ℤ) + (C.p : ℤ) ^ (C.dim - C.degree) ≤ lim.word := by exact_mod_cast hvpWord
  have hpeIntNonneg : 0 ≤ (C.p : ℤ) ^ C.degree := by positivity
  have hpgIntNonneg : 0 ≤ (C.p : ℤ) ^ (C.dim - C.degree) := by positivity
  apply Meets.of_body S.mainBody
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (C.p ^ C.degree : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get, h0, h1, h2, h3, ha0, ha1, ha2, ha3,
            hpeAddr, hpe]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [get, h0, h1, h2, h3, ha0, ha1, ha2, ha3, hpeAddr, hpe] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, get, h0, h1, h2, h3, ha0, ha1, ha2, ha3,
            hpeAddr, hpe] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (C.p ^ (C.dim - C.degree) : ℕ) ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get, h0, h1, h2, h3, ha0, ha1, ha2, ha3,
            hpgAddr, hpg]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [get, h0, h1, h2, h3, ha0, ha1, ha2, ha3, hpgAddr, hpg] <;>
            first
            | omega
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, get, h0, h1, h2, h3, ha0, ha1, ha2, ha3,
            hpgAddr, hpg] <;>
          omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.iteLast ?_ ?_
      (by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
      (by
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [get] <;>
              first
              | omega
              | (ring_nf; omega)))
  · intro hu
    have hu' : u < C.p ^ C.degree := by exact_mod_cast (show (u : ℤ) < ((C.p ^ C.degree : ℕ) : ℤ) from hu)
    refine
      Ends.iteLast ?_ ?_
        (by (
            (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
        (by
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [get] <;>
                first
                | omega
                | (ring_nf; omega)))
    · intro hv
      have hv' : v < C.p ^ (C.dim - C.degree) := by
        exact_mod_cast (show (v : ℤ) < ((C.p ^ (C.dim - C.degree) : ℕ) : ℤ) from hv)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        first
        |
          refine
            _root_.Light.Ends.callToThen
              ((S.coreProcs.meets (depth := depth + 1) μ f hw (by omega) hp he hed hpow htarget hleft hspace hpowRead
                  hfRead hwCore)
                _ (by omega))
              ?_ ?_ ?_ ?_
        |
          refine
            _root_.Light.Ends.callToThen
              (S.coreProcs.meets (depth := depth + 1) μ f hw (by omega) hp he hed hpow htarget hleft hspace hpowRead
                hfRead hwCore)
              ?_ ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get, hupInt,
                hvpInt, h0, h1, h2, h3, h4, h5, h6, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightExtensionFactorCheck.time]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [get, hupInt, hvpInt, h0, h1, h2, h3, h4, h5, h6, ha0, ha1, ha2, ha3, ha4, ha5, ha6,
                  LightExtensionFactorCheck.time] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 => omega
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, get, hupInt, hvpInt, h0, h1, h2, h3, h4, h5,
                h6, ha0, ha1, ha2, ha3, ha4, ha5, ha6, LightExtensionFactorCheck.time] <;>
              omega)
        on_goal -1 => (rintro z ν ⟨hz, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
      exact ⟨by simpa [result, hu', hv'] using hz, hkeep⟩
    · intro hv
      have hv' : ¬v < C.p ^ (C.dim - C.degree) := by
        exact_mod_cast (show ¬(v : ℤ) < ((C.p ^ (C.dim - C.degree) : ℕ) : ℤ) from hv)
      focus
        ((first
            | refine _root_.Light.Ends.seqSelf ?_
            | refine _root_.Light.Ends.skipLast ?_);
          repeat
            with_unfolding_none
              first
              | refine _root_.Light.Ends.seqAssoc ?_
              | refine _root_.Light.Ends.skipThen ?_)
        refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
        on_goal -1 =>
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [get] <;>
                first
                | omega
                | (ring_nf; omega))
        on_goal -1 =>
          ( (try have := _root_.Light.Std.space_le (by assumption))
            (try have := _root_.Light.Std.const_le (by assumption))
            simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, get] <;> omega)
        try with_unfolding_none refine _root_.Light.Ends.skip ?_
      exact ⟨by simp [result, hv'], SameOn.refl⟩
  · intro hu
    have hu' : ¬u < C.p ^ C.degree := by exact_mod_cast (show ¬(u : ℤ) < ((C.p ^ C.degree : ℕ) : ℤ) from hu)
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
      on_goal -1 =>
        first
        | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
              _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get]
            first
            | omega
            | (ring_nf; omega))
        | omega
        |
          (simp [get] <;>
              first
              | omega
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, get] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨by simp [result, hu'], SameOn.refl⟩
end Procs
end ThreeSum.LightExtensionFactorPredicate
