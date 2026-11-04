-- Prove2me | solution 1 for ThreeSum.LightExtensionQuotientPredicate.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:08:00.958395+00:00
-- url     : https://prove2.me/submissions/fc63d1dc-9255-472a-9f64-45f1eb2bab8d

import Mathlib.Tactic.ClearExcept
import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Theorems.Thm_ThreeSum_LightExtensionQuotientPredicate_header_kept
import Theorems.Thm_Light_Meets_of_body
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
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_meets
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_LightPolynomialProductArray_meets
import Theorems.Thm_ThreeSum_LightPolynomialProductCheck_meets
import Theorems.Thm_ThreeSum_LightPolynomialQuotientCheck_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimeAddArray_meets
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
open ThreeSum ThreeSum.LightExtensionQuotientPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionQuotientPredicate
namespace Procs
theorem _root_.solution {main ctx u v : ℕ} (S : Procs P main) (C : Layout) (μ : ℕ → ℤ) (x y f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : depth + 4 < lim.depth) (hp : 1 < C.p) (H : Seg μ ctx (header C))
    (hctx : ctx + 10 ≤ C.h) (hpowers : C.powers + (2 * C.dim + 1) ≤ C.h)
    (hpowRead : ∀ e ≤ 2 * C.dim, μ (C.powers + e) = ((C.p ^ e : ℕ) : ℤ)) (ha : C.a + C.dim ≤ C.h)
    (hb : C.b + C.dim ≤ C.h) (hf : C.modulus + (C.dim + 1) ≤ C.h) (hh : C.h + C.dim ≤ C.remainder)
    (hr : C.remainder + 2 * C.dim ≤ C.productWork) (hprod : C.productWork + 2 * C.dim ≤ C.sumWork)
    (hspace : C.sumWork + 2 * C.dim ≤ lim.space) (hxRead : ∀ i < C.dim, μ (C.a + i) = (x i : ℤ))
    (hyRead : ∀ i < C.dim, μ (C.b + i) = (y i : ℤ)) (hfRead : ∀ i < C.dim + 1, μ (C.modulus + i) = (f i : ℤ))
    (hxBound : ∀ i < C.dim, x i < C.p) (hyBound : ∀ i < C.dim, y i < C.p) (hfBound : ∀ i < C.dim + 1, f i < C.p)
    (hword : (word C.dim C.p u v : ℤ) ≤ lim.word) :
    Meets lim P main depth [u, v, ctx] μ (time C.dim C.p u v) (fun z ν => z = result C x y f u v ∧ Kept μ ν C.h) :=
  by
  have h0 := H 0 (by simp [header])
  have h1 := H 1 (by simp [header])
  have h2 := H 2 (by simp [header])
  have h3 := H 3 (by simp [header])
  have h4 := H 4 (by simp [header])
  have h5 := H 5 (by simp [header])
  have h6 := H 6 (by simp [header])
  have h7 := H 7 (by simp [header])
  have h8 := H 8 (by simp [header])
  have h9 := H 9 (by simp [header])
  simp only [header, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hwH : (LightCoefficientDecode.word C.dim C.p u 0 1 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hwR : (LightCoefficientDecode.word (2 * C.dim) C.p v 0 1 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hwCore : (LightPolynomialQuotientCheck.word C.dim C.p : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hu : (u : ℤ) ≤ lim.word := by unfold LightCoefficientDecode.word at hwH; omega
  have hv : (v : ℤ) ≤ lim.word := by unfold LightCoefficientDecode.word at hwR; omega
  have h2d : (2 * (C.dim : ℤ)) ≤ lim.word := by unfold LightCoefficientDecode.word at hwR; omega
  have hpWord : (C.p : ℤ) ≤ lim.word := by unfold LightCoefficientDecode.word at hwR; omega
  have hdWord : (C.dim : ℤ) ≤ lim.word := by unfold LightCoefficientDecode.word at hwH; omega
  have htwo : (2 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have headerAddress (i : ℕ) : ((ctx : ℤ) + (i : ℤ)).toNat = ctx + i := by omega
  have ha0 : ((ctx : ℤ) + 0).toNat = ctx + 0 := by omega
  have ha1 : ((ctx : ℤ) + 1).toNat = ctx + 1 := by omega
  have ha2 : ((ctx : ℤ) + 2).toNat = ctx + 2 := by omega
  have ha3 : ((ctx : ℤ) + 3).toNat = ctx + 3 := by omega
  have ha4 : ((ctx : ℤ) + 4).toNat = ctx + 4 := by omega
  have ha5 : ((ctx : ℤ) + 5).toNat = ctx + 5 := by omega
  have ha6 : ((ctx : ℤ) + 6).toNat = ctx + 6 := by omega
  have ha7 : ((ctx : ℤ) + 7).toNat = ctx + 7 := by omega
  have ha8 : ((ctx : ℤ) + 8).toNat = ctx + 8 := by omega
  have ha9 : ((ctx : ℤ) + 9).toNat = ctx + 9 := by omega
  have p2m_decode_depth : depth + 1 + 1 < lim.depth := by omega
  have p2m_core_depth : depth + 1 + 3 < lim.depth := by omega
  have p2m_p_le : 1 ≤ C.p := by omega
  have p2m_pos_p : 0 < C.p := Nat.zero_lt_of_lt hp
  have p2m_h_space : C.h + C.dim ≤ lim.space := by omega
  have p2m_r_space : C.remainder + 2 * C.dim ≤ lim.space := by omega
  have p2m_pow_h_space : C.powers + (C.dim + 1) ≤ lim.space := by omega
  have p2m_pow_r_space : C.powers + (2 * C.dim + 1) ≤ lim.space := by omega
  have p2m_sep_h : C.powers + (C.dim + 1) ≤ C.h := by omega
  have p2m_sep_r : C.powers + (2 * C.dim + 1) ≤ C.remainder := by omega
  have p2m_a_core : C.a + C.dim ≤ C.productWork := by omega
  have p2m_b_core : C.b + C.dim ≤ C.productWork := by omega
  have p2m_h_core : C.h + C.dim ≤ C.productWork := by omega
  have p2m_f_core : C.modulus + (C.dim + 1) ≤ C.productWork := by omega
  have p2m_h_le_r : C.h ≤ C.remainder := by omega
  have p2m_h_le_core : C.h ≤ C.productWork := by omega
  have p2m_dim_le_two : C.dim ≤ 2 * C.dim := by omega
  have p2m_pow_addr (e : ℕ) (he : e ≤ 2 * C.dim) : C.powers + e < C.h :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le he) C.powers) hpowers
  have p2m_a_addr (i : ℕ) (hi : i < C.dim) : C.a + i < C.h := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi C.a) ha
  have p2m_b_addr (i : ℕ) (hi : i < C.dim) : C.b + i < C.h := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi C.b) hb
  have p2m_f_addr (i : ℕ) (hi : i < C.dim + 1) : C.modulus + i < C.h :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi C.modulus) hf
  have p2m_h_addr (i : ℕ) (hi : i < C.dim) : C.h + i < C.remainder := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi C.h) hh
  have p2m_keep_r (a : ℕ) (ha : a < C.h) : a < C.remainder := Nat.lt_of_lt_of_le ha p2m_h_le_r
  have p2m_keep_core (a : ℕ) (ha : a < C.h) : a < C.productWork := Nat.lt_of_lt_of_le ha p2m_h_le_core
  have p2m_coords_h (i : ℕ) (hi : i < C.dim) : 0 + 1 * i < C.dim := by simpa using hi
  have p2m_coords_r (i : ℕ) (hi : i < 2 * C.dim) : 0 + 1 * i < 2 * C.dim := by simpa using hi
  apply Meets.of_body S.mainBody
  unfold body time
  have p2m_call_1 :=
    (LightCoefficientDecode.meets (d := depth + 1) (W := C.dim) (p := C.p) (k := u) (powers := C.powers) (start := 0)
      (stride := 1) (dst := C.h) (n := C.dim) S.decodeBody S.digitBody S.divideBody hw p2m_decode_depth p2m_p_le
      p2m_h_space p2m_pow_h_space (Or.inl p2m_sep_h) hwH p2m_coords_h
      (fun e he => hpowRead e (he.trans p2m_dim_le_two)))
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (p2m_call_1 _ (by (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega))) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen p2m_call_1 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get, headerAddress, ha0, ha1, ha2, ha3, ha4,
            ha5, ha6, ha7, ha8, ha9, h0, h1, h2, h6, LightCoefficientDecode.time, LightPolynomialQuotientCheck.time]
          first
          | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
          | (ring_nf; (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)))
      | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
      |
        (simp [get, headerAddress, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, h0, h1, h2, h6,
              LightCoefficientDecode.time, LightPolynomialQuotientCheck.time] <;> first
            | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
            | (ring_nf; (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)))
    on_goal -1 => (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, get, headerAddress, ha0, ha1, ha2, ha3, ha4,
            ha5, ha6, ha7, ha8, ha9, h0, h1, h2, h6, LightCoefficientDecode.time, LightPolynomialQuotientCheck.time] <;> (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega))
    on_goal -1 => (rintro z₁ μ₁ ⟨hValues, keep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have keepH : Kept μ μ₁ C.h := fun a ha => keep₁ a (Or.inl ha)
  have H₁ := header_kept H hctx keepH
  have hh0 := H₁ 0 (by simp [header])
  have hh1 := H₁ 1 (by simp [header])
  have hh2 := H₁ 2 (by simp [header])
  have hh7 := H₁ 7 (by simp [header])
  simp only [header, List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at hh0 hh1 hh2 hh7
  have pow₁ (e : ℕ) (he : e ≤ 2 * C.dim) : μ₁ (C.powers + e) = ((C.p ^ e : ℕ) : ℤ) :=
    (keepH _ (p2m_pow_addr e he)).trans (hpowRead e he)
  have p2m_call_2 :=
    (LightCoefficientDecode.meets (d := depth + 1) (W := 2 * C.dim) (p := C.p) (k := v) (powers := C.powers) (start :=
      0) (stride := 1) (dst := C.remainder) (n := 2 * C.dim) S.decodeBody S.digitBody S.divideBody hw p2m_decode_depth
      p2m_p_le p2m_r_space p2m_pow_r_space (Or.inl p2m_sep_r) hwR p2m_coords_r pow₁)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (p2m_call_2 _ (by (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega))) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen p2m_call_2 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get, headerAddress, ha0, ha1, ha2, ha3, ha4,
            ha5, ha6, ha7, ha8, ha9, hh0, hh1, hh2, hh7, LightCoefficientDecode.time, LightPolynomialQuotientCheck.time]
          first
          | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
          | (ring_nf; (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)))
      | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
      |
        (simp [get, headerAddress, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, hh0, hh1, hh2, hh7,
              LightCoefficientDecode.time, LightPolynomialQuotientCheck.time] <;> first
            | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
            | (ring_nf; (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)))
    on_goal -1 => (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, get, headerAddress, ha0, ha1, ha2, ha3, ha4,
            ha5, ha6, ha7, ha8, ha9, hh0, hh1, hh2, hh7, LightCoefficientDecode.time,
            LightPolynomialQuotientCheck.time] <;> (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega))
    on_goal -1 => (rintro z₂ μ₂ ⟨rValues, keep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have keepR : Kept μ₁ μ₂ C.h := fun a ha => keep₂ a (Or.inl (p2m_keep_r a ha))
  have H₂ := header_kept H₁ hctx keepR
  have hhh0 := H₂ 0 (by simp [header])
  have hhh1 := H₂ 1 (by simp [header])
  have hhh3 := H₂ 3 (by simp [header])
  have hhh4 := H₂ 4 (by simp [header])
  have hhh5 := H₂ 5 (by simp [header])
  have hhh6 := H₂ 6 (by simp [header])
  have hhh7 := H₂ 7 (by simp [header])
  have hhh8 := H₂ 8 (by simp [header])
  have hhh9 := H₂ 9 (by simp [header])
  simp only [header, List.getElem_cons_zero, List.getElem_cons_succ,
    Nat.add_zero] at hhh0 hhh1 hhh3 hhh4 hhh5 hhh6 hhh7 hhh8 hhh9
  have x₂ (i : ℕ) (hi : i < C.dim) : μ₂ (C.a + i) = (x i : ℤ) :=
    (keepR _ (p2m_a_addr i hi)).trans ((keepH _ (p2m_a_addr i hi)).trans (hxRead i hi))
  have y₂ (i : ℕ) (hi : i < C.dim) : μ₂ (C.b + i) = (y i : ℤ) :=
    (keepR _ (p2m_b_addr i hi)).trans ((keepH _ (p2m_b_addr i hi)).trans (hyRead i hi))
  have f₂ (i : ℕ) (hi : i < C.dim + 1) : μ₂ (C.modulus + i) = (f i : ℤ) :=
    (keepR _ (p2m_f_addr i hi)).trans ((keepH _ (p2m_f_addr i hi)).trans (hfRead i hi))
  have h₂ (i : ℕ) (hi : i < C.dim) : μ₂ (C.h + i) = (digits C.p u i : ℤ) :=
    by
    rw [keep₂ _ (Or.inl (p2m_h_addr i hi))]
    simpa [digits] using hValues i hi
  have r₂ (i : ℕ) (hi : i < 2 * C.dim) : μ₂ (C.remainder + i) = (digits C.p v i : ℤ) := by
    simpa [digits] using rValues i hi
  have digBound (code i : ℕ) : digits C.p code i < C.p := Nat.mod_lt _ p2m_pos_p
  have p2m_call_3 :=
    (S.coreProcs.meets (depth := depth + 1) μ₂ x y (digits C.p u) f (digits C.p v) hw p2m_core_depth hp p2m_a_core
      p2m_b_core p2m_h_core p2m_f_core hr hprod hspace x₂ y₂ h₂ f₂ r₂ hxBound hyBound (fun i _ => digBound u i) hfBound
      (fun i _ => digBound v i) hwCore)
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    | refine _root_.Light.Ends.callToThen (p2m_call_3 _ (by (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega))) ?_ ?_ ?_ ?_
    | refine _root_.Light.Ends.callToThen p2m_call_3 ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, get, headerAddress, ha0, ha1, ha2, ha3, ha4,
            ha5, ha6, ha7, ha8, ha9, hhh0, hhh1, hhh3, hhh4, hhh5, hhh6, hhh7, hhh8, hhh9, LightCoefficientDecode.time,
            LightPolynomialQuotientCheck.time]
          first
          | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
          | (ring_nf; (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)))
      | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
      |
        (simp [get, headerAddress, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, hhh0, hhh1, hhh3, hhh4, hhh5, hhh6,
              hhh7, hhh8, hhh9, LightCoefficientDecode.time, LightPolynomialQuotientCheck.time] <;> first
            | (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
            | (ring_nf; (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)))
    on_goal -1 => (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega)
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, get, headerAddress, ha0, ha1, ha2, ha3, ha4,
            ha5, ha6, ha7, ha8, ha9, hhh0, hhh1, hhh3, hhh4, hhh5, hhh6, hhh7, hhh8, hhh9, LightCoefficientDecode.time,
            LightPolynomialQuotientCheck.time] <;> (clear * - hw hd hp hctx hpowers ha hb hf hh hr hprod hspace hu hv h2d hpWord hdWord htwo p2m_decode_depth p2m_core_depth p2m_p_le p2m_pos_p p2m_h_space p2m_r_space p2m_pow_h_space p2m_pow_r_space p2m_sep_h p2m_sep_r p2m_a_core p2m_b_core p2m_h_core p2m_f_core p2m_h_le_r p2m_h_le_core p2m_dim_le_two; omega))
    on_goal -1 => (rintro z ν ⟨hz, hkeep⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine ⟨hz, ?_⟩
  intro a ha
  change ν a = μ a
  rw [hkeep _ (p2m_keep_core a ha), keepR _ ha, keepH _ ha]
end Procs
end ThreeSum.LightExtensionQuotientPredicate
