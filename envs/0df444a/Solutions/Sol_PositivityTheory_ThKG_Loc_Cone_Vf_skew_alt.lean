-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.skew_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:53.529966+00:00
-- url     : https://prove2.me/submissions/94655f56-5338-4163-b628-4260dc12083a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_mapc_zero
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_Adj_one
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_Adj_add
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_Adj_sub
import Theorems.Thm_PositivityTheory_ThKG_Loc_Cone_Vf_Adj_mul

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
theorem _root_.solution {Ji k k' b b' f' : Matrix β β A} (hJ : J * Ji = 1) (hk : k * k' = 1) (a1 : Adj c J k k') (a2 : Adj c J k' k)
    (b1 : Adj c J b b') (b2 : Adj c J b' b) (hb : b + b' = -1) (hf : (1 + (1 - k) * b) * f' = 1) :
    (-(f' * (1 - k)))ᵀ * J + J * (-(f' * (1 - k))).map c = 0 := by
  set m := 1 - k with hm
  set m' := 1 - k' with hm'
  set T := -(f' * m) with hT
  have hJ' : Ji * J = 1 := mul_eq_one_comm.1 hJ
  have am : Adj c J m m' := Adj.one.sub a1
  have am' : Adj c J m' m := Adj.one.sub a2
  have af : Adj c J (1 + m * b) (1 + b' * m') := Adj.one.add (am.mul b1)
  have af' : Adj c J (1 + b' * m') (1 + m * b) := Adj.one.add (b2.mul am')
  set f := 1 + m * b with hfd
  set g := 1 + b' * m' with hg
  have hfT : f * T = -m := by rw [hT, Matrix.mul_neg, ← Matrix.mul_assoc, hf, Matrix.one_mul]
  have z : f * m' + m * g = 0 := by
    have e : m * m' = m + m' := by
      rw [hm, hm', Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hk]; simp; abel
    have : f * m' + m * g = m' + m + m * (b + b') * m' := by rw [hfd, hg]; noncomm_ring
    rw [this, hb, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, e]; abel
  have e1 : Tᵀ * J * g.map c = -(J * m'.map c) := by
    rw [Matrix.mul_assoc, ← af, ← Matrix.mul_assoc, ← transpose_mul, hfT, transpose_neg, Matrix.neg_mul, am]
  have e2 : gᵀ * J * T.map c = -(J * m.map c) := by
    rw [af', Matrix.mul_assoc, ← mapc_mul, hfT, mapc_neg, Matrix.mul_neg]
  have e3 : gᵀ * (Tᵀ * J + J * T.map c) * g.map c = 0 := by
    have : gᵀ * (Tᵀ * J + J * T.map c) * g.map c = gᵀ * (Tᵀ * J * g.map c) + gᵀ * J * T.map c * g.map c := by noncomm_ring
    rw [this, e1, e2, Matrix.mul_neg, ← Matrix.mul_assoc, af', Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← mapc_mul,
      ← mapc_mul, ← neg_add, ← Matrix.mul_add, ← mapc_add, z, mapc_zero, Matrix.mul_zero, neg_zero]
  have hf' : f' * f = 1 := mul_eq_one_comm.1 hf
  have l : J * f'.map c * Ji * gᵀ = 1 := by
    have : gᵀ = J * f.map c * Ji := by rw [← af', Matrix.mul_assoc, hJ, Matrix.mul_one]
    rw [this]
    calc J * f'.map c * Ji * (J * f.map c * Ji) = J * (f'.map c * (Ji * J) * f.map c) * Ji := by noncomm_ring
      _ = 1 := by rw [hJ', Matrix.mul_one, ← mapc_mul, hf', mapc_one, Matrix.mul_one, hJ]
  have r : g.map c * (Ji * f'ᵀ * J) = 1 := by
    have : g.map c = Ji * (fᵀ * J) := by rw [af, ← Matrix.mul_assoc, hJ', Matrix.one_mul]
    rw [this]
    calc Ji * (fᵀ * J) * (Ji * f'ᵀ * J) = Ji * (fᵀ * (J * Ji) * f'ᵀ) * J := by noncomm_ring
      _ = 1 := by rw [hJ, Matrix.mul_one, ← transpose_mul, hf', transpose_one, Matrix.mul_one, hJ']
  calc Tᵀ * J + J * T.map c = (J * f'.map c * Ji * gᵀ) * (Tᵀ * J + J * T.map c) * (g.map c * (Ji * f'ᵀ * J)) := by
        rw [l, r, Matrix.one_mul, Matrix.mul_one]
    _ = J * f'.map c * Ji * (gᵀ * (Tᵀ * J + J * T.map c) * g.map c) * (Ji * f'ᵀ * J) := by noncomm_ring
    _ = 0 := by rw [e3, Matrix.mul_zero, Matrix.zero_mul]
end PositivityTheory.ThKG.Loc.Cone.Vf
