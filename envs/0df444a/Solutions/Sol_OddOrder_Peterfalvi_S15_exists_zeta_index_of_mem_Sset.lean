-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.exists_zeta_index_of_mem_Sset
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:26:38.187209+00:00
-- url     : https://prove2.me/submissions/bfb012b9-a4d7-47f0-8d48-ade8222282a1

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndTGrid.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid

-- ===== OddOrder/Peterfalvi/S15_SAndTGrid.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Every family member is an enumerated `ζ_k` with `k ≠ ind1H`** — the converse of
`TypeICoherent78Data.zeta_mem_Sset`.  The `cover` field supplies an index `k` with
`ζ_k = Ind θ' = φ`; `k = ind1H` is impossible since `Ind 1_H` is real while the nontrivial
induced irreducible `Ind θ'` is not (odd order, Peterfalvi (1.1)). -/
theorem _root_.solution [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ dataL.typeIHyp.Sset) :
    ∃ k : Fin (dataL.n + 1), k ≠ dataL.ind1H ∧ dataL.zeta k = φ := by
  have := dataL.kernelIn_normal
  obtain ⟨θ', hθ'ne, hφeq⟩ := hφ
  obtain ⟨k, hk⟩ := dataL.cover θ'
  have hk' : ClassFunction.induce dataL.kernelIn (dataL.θ k : ClassFunction _ ℂ)
      = ClassFunction.induce dataL.kernelIn (θ' : ClassFunction _ ℂ) := hk
  refine ⟨k, ?_, hk'.trans hφeq.symm⟩
  -- `k = ind1H` would identify the non-real `Ind θ'` with the real `Ind 1_H`.
  rintro rfl
  have hind1 : ClassFunction.induce dataL.kernelIn (dataL.θ dataL.ind1H : ClassFunction _ ℂ)
      = ClassFunction.induce dataL.kernelIn
          (trivialClassFunction ↥dataL.kernelIn) := by
    rw [dataL.triv]
    rfl
  have hreal : ClassFunction.IsReal
      (ClassFunction.induce dataL.kernelIn (dataL.θ dataL.ind1H : ClassFunction _ ℂ)) := by
    rw [hind1]
    change (ClassFunction.induce dataL.kernelIn (trivialClassFunction _)).conj = _
    rw [conj_induce]
    exact congrArg _ trivialClassFunction_isReal
  rw [hk'] at hreal
  -- `Ind θ'` is a nontrivial irreducible (Frobenius), hence not real in odd order
  have hirr : IsIrreducibleCharacter
      (ClassFunction.induce dataL.kernelIn (θ' : ClassFunction _ ℂ)) :=
    isIrreducibleCharacter_induce_of_frobeniusGroup dataL.hFrob θ' hθ'ne
  have hodd_L : Odd (Nat.card ↥L) :=
    _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)
  have hK_ne_top : dataL.kernelIn ≠ ⊤ := by
    intro hKtop
    refine dataL.hFrob.ne_bot_complement (le_bot_iff.mp ?_)
    have hdisj := dataL.hFrob.isComplement.disjoint
    rw [show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = dataL.kernelIn from rfl, hKtop]
      at hdisj
    simpa using hdisj.le_bot
  have hidx : 1 < (dataL.kernelIn).index := Subgroup.one_lt_index_of_ne_top hK_ne_top
  obtain ⟨di, hdi_pos, hdi⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ'
  have hne_triv : (⟨ClassFunction.induce dataL.kernelIn (θ' : ClassFunction _ ℂ), hirr⟩ :
      IrreducibleCharacter ↥L) ≠ trivialIrreducibleCharacter _ := by
    intro h
    have hcf : ClassFunction.induce dataL.kernelIn (θ' : ClassFunction _ ℂ)
        = trivialClassFunction ↥L := by
      have h2 := congrArg Subtype.val h
      simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter] using h2
    have hone : ((dataL.kernelIn).index : ℂ) * (di : ℂ) = 1 := by
      rw [← hdi, ← ClassFunction.induce_apply_one dataL.kernelIn (θ' : ClassFunction _ ℂ),
        hcf, trivialClassFunction_apply]
    have : (dataL.kernelIn).index * di = 1 := by exact_mod_cast hone
    have h1 : (dataL.kernelIn).index = 1 := by
      rcases Nat.eq_one_of_mul_eq_one_right this with h; omega
    omega
  exact not_isReal_of_ne_trivial_of_odd_card' hodd_L hne_triv hreal

end OddOrder.Peterfalvi.S15
