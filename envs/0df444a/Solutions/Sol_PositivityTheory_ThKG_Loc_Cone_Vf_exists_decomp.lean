-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:18:45.407929+00:00
-- url     : https://prove2.me/submissions/0fae64d6-db3a-4003-af56-b8c34f9bd97f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_mapc_zero
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_mapc_smul
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_adj_unit
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_skew_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
variable {c} {J : Matrix β β A}
namespace PositivityTheory.ThKG.Loc.Cone.Vf
theorem _root_.solution {Ji b b' f' : Matrix β β A} (hJ : J * Ji = 1) (k : UG c J) (b1 : Adj c J b b') (b2 : Adj c J b' b)
    (hb : b + b' = -1) (hf : (1 + (1 - (k.1 : Matrix β β A)) * b) * f' = 1) {ε : A} (he : ε * ε = ε) (hc : c ε = ε)
    (hm : ε • (1 - (k.1 : Matrix β β A)) = 1 - (k.1 : Matrix β β A)) (gd : UG c (dbl J))
    (hgd : (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A) = fromBlocks k.1 0 0 1) :
    ∃ (s n p : UG c (dbl J)) (t : GL β A), s * s = 1 ∧ gd = s * n * s * p ∧
      (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * SS ε * Ci b ∧
      (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 (-(f' * (1 - (k.1 : Matrix β β A)))) 0 1 * Ci b ∧
      ((n⁻¹).1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 (f' * (1 - (k.1 : Matrix β β A))) 0 1 * Ci b ∧
      (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * ((1 : GL β A) : Matrix β β A) ∧
      (p.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (t : Matrix β β A) ∧
      (t : Matrix β β A) = 1 + b * (1 - (k.1 : Matrix β β A)) ∧ ((t⁻¹ : GL β A) : Matrix β β A) = 1 - b * (f' * (1 - (k.1 : Matrix β β A))) := by
  have hk : (k.1 : Matrix β β A) * ((k⁻¹).1 : Matrix β β A) = 1 := k.1.mul_inv
  have sk := skew_alt hJ hk (adj_unit k) (by simpa using adj_unit k⁻¹) b1 b2 hb hf
  set m : Matrix β β A := 1 - k.1 with hmd
  set T := -(f' * m) with hT
  have e0 : ε * (1 - ε) = 0 := by rw [mul_sub, he, mul_one, sub_self]
  have e0' : (1 - ε) * ε = 0 := by rw [mul_comm, e0]
  have e1 : (1 - ε) * (1 - ε) = 1 - ε := by rw [sub_mul, one_mul, e0, sub_zero]
  have hS : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * SS ε = 1 := by
    rw [SS, fromBlocks_multiply, ← fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hSu : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 * (SS ε : Matrix (β ⊕ β) (β ⊕ β) A).map c =
      fromBlocks 0 J J 0 := by
    rw [SS, fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply]
    simp only [mapc_smul, mapc_one, map_sub, map_one, hc, transpose_smul, transpose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, zero_add, add_zero, smul_smul, e0, e0', e1, he, ← add_smul]
    simp
  have hU : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 (f' * m) 0 1 = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one, hT]; simp
  have hUu : (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A)ᵀ * fromBlocks 0 J J 0 *
      (fromBlocks 1 T 0 1 : Matrix (β ⊕ β) (β ⊕ β) A).map c = fromBlocks 0 J J 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply, mapc_one, mapc_zero]
    simp only [transpose_one, transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, Matrix.mul_one, add_zero, zero_add]
    rw [add_comm (J * _), sk]
  have hf' : f' * (1 + m * b) = 1 := mul_eq_one_comm.1 hf
  have hTt : T * (1 + b * m) = -m := by
    have : T * (1 + b * m) = -(f' * (1 + m * b) * m) := by rw [hT]; noncomm_ring
    rw [this, hf', Matrix.one_mul]
  have ht : (1 - b * (f' * m)) * (1 + b * m) = 1 := by
    have : (1 - b * (f' * m)) * (1 + b * m) = 1 + b * m + b * (T * (1 + b * m)) := by rw [hT]; noncomm_ring
    rw [this, hTt]; noncomm_ring
  let s := mkU b1 hb _ _ hS hSu
  let n := mkU b1 hb _ _ hU hUu
  have hs : (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * SS ε * Ci b := rfl
  have hn : (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 T 0 1 * Ci b := rfl
  have hεT : ε • T = T := by rw [hT, smul_neg, ← Matrix.mul_smul, hm]
  have hεT' : (1 - ε) • T = 0 := by rw [sub_smul, one_smul, hεT, sub_self]
  have hL : (SS ε : Matrix (β ⊕ β) (β ⊕ β) A) * fromBlocks 1 T 0 1 * SS ε = fromBlocks 1 0 T 1 := by
    rw [SS, fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, smul_zero, add_zero, hεT, hεT',
      zero_add, Matrix.add_mul, smul_add, smul_smul, e0, e0', e1, he, zero_smul, ← add_smul]
    simp
  have hD : Ci b * (diagCols β : Matrix (β ⊕ β) β A) = (fromRows 1 0 : Matrix (β ⊕ β) β A) := by
    rw [Ci, diagCols, fromBlocks_mul_fromRows]; simp
  have hD' : CC b * (fromRows 1 0 : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) := by
    rw [CC, diagCols, fromBlocks_mul_fromRows]; simp
  refine ⟨s, n, (s * n * s)⁻¹ * gd, ⟨1 + b * m, 1 - b * (f' * m), mul_eq_one_comm.1 ht, ht⟩, ?_, by group, hs, hn, rfl, ?_, ?_,
    rfl, rfl⟩
  · refine Subtype.ext (Units.ext ?_)
    exact s.1.mul_inv
  · rw [hn, Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b), fromBlocks_mul_fromRows]
    simpa using hD'
  · have e : ((s * n * s).1 : Matrix (β ⊕ β) (β ⊕ β) A) = CC b * fromBlocks 1 0 T 1 * Ci b := by
      change (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (n.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (s.1 : Matrix (β ⊕ β) (β ⊕ β) A) = _
      rw [hs, hn, ← hL]
      calc CC b * SS ε * Ci b * (CC b * fromBlocks 1 T 0 1 * Ci b) * (CC b * SS ε * Ci b)
          = CC b * (SS ε * (Ci b * CC b) * fromBlocks 1 T 0 1 * (Ci b * CC b) * SS ε) * Ci b := by noncomm_ring
        _ = _ := by rw [Ci_CC, Matrix.mul_one, Matrix.mul_one]
    have e2 : (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = ((s * n * s).1 : Matrix (β ⊕ β) (β ⊕ β) A) * ((diagCols β : Matrix (β ⊕ β) β A) * (1 + b * m)) := by
      rw [e, hgd, ← Matrix.mul_assoc _ (diagCols β : Matrix (β ⊕ β) β A), Matrix.mul_assoc _ (Ci b), hD, Matrix.mul_assoc (CC b), fromBlocks_mul_fromRows, CC,
        fromBlocks_mul_fromRows, fromRows_mul, diagCols, fromBlocks_mul_fromRows]
      congr 1
      · have : (1 * (1 * 1 + 0 * 0) + (1 + b) * (T * 1 + 1 * 0)) * (1 + b * m) = 1 + b * m + (1 + b) * (T * (1 + b * m)) := by
          noncomm_ring
        rw [this, hTt, hmd]; noncomm_ring
      · have : (1 * (1 * 1 + 0 * 0) + b * (T * 1 + 1 * 0)) * (1 + b * m) = 1 + b * m + b * (T * (1 + b * m)) := by
          noncomm_ring
        rw [this, hTt]; noncomm_ring
    change (((s * n * s)⁻¹).1 : Matrix (β ⊕ β) (β ⊕ β) A) * (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A) * (diagCols β : Matrix (β ⊕ β) β A) = (diagCols β : Matrix (β ⊕ β) β A) * (1 + b * m)
    rw [Matrix.mul_assoc _ (gd.1 : Matrix (β ⊕ β) (β ⊕ β) A), e2, ← Matrix.mul_assoc]
    have : (((s * n * s)⁻¹).1 : Matrix (β ⊕ β) (β ⊕ β) A) * ((s * n * s).1 : Matrix (β ⊕ β) (β ⊕ β) A) = 1 := (s * n * s).1.inv_mul
    rw [this, Matrix.one_mul]
end PositivityTheory.ThKG.Loc.Cone.Vf
