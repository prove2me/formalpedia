-- Prove2me | solution 1 for OddOrder.Peterfalvi.S15.coh_extension_sub_zeta0_eq_typeIBetaL_sub
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:26:36.613142+00:00
-- url     : https://prove2.me/submissions/278dfa04-bc2d-4017-9c18-94739c6e0311

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Theorems.Thm_OddOrder_Peterfalvi_S15_exists_zeta_index_of_mem_Sset

-- ===== OddOrder/Peterfalvi/S15_SAndT.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`φ`-invariance identity** for the (13.19.c) dichotomy: for a degree-`e` member
`φ ∈ 𝓛`, the coherent-image difference equals the `β_L^τ` difference,
`φ^{τ₁} − ζ_0^{τ₁} = β_L^τ(ζ_0) − β_L^τ(φ)`.  Both sides are `τ₁(φ − ζ_0)`: `φ = ζ_k` with
`d_k = 1` (equal degree, `exists_zeta_index_of_mem_Sset` + `zeta_deg`), so `φ − ζ_0` is
`A(L)`-supported (`psi_support`), where the coherent extension agrees with `τ = typeIHyp.tau`
(`extends_on_supported`); and `β_L^τ(ζ_0) − β_L^τ(φ) = τ(Ind − ζ_0) − τ(Ind − φ) = τ(φ − ζ_0)`
by linearity.  This is the sole bridge from the `ζ_0`-based parity core/case bounds to the
producer's arbitrary degree-`e` `φ`. -/
theorem _root_.solution [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (dataL : OddOrder.Peterfalvi.S16.TypeICoherent78Data L)
    (φ : ClassFunction ↥L ℂ) (hφ : φ ∈ dataL.typeIHyp.Sset)
    (hdeg : φ 1 = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)) :
    dataL.coh.extension φ - dataL.coh.extension (dataL.zeta 0)
      = typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ := by
  classical
  have := dataL.kernelIn_normal
  obtain ⟨k, hk_ne, hkφ⟩ := exists_zeta_index_of_mem_Sset hG dataL hφ
  -- `ζ_0(1) = e`, hence `d_k = 1` (equal degree).
  have hζ01 : dataL.zeta 0 (1 : ↥L) = (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
    rw [show dataL.zeta 0 (1 : ↥L)
        = ClassFunction.induce dataL.kernelIn (dataL.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
      dataL.deg0]
    congr 2
    show (dataL.typeIHyp.typeI.typeF.H).subgroupOf L = (maxNilpotentNormalHall L).subgroupOf L
    rw [dataL.typeIHyp.typeI.typeF.H_eq]
  have hidx_ne : (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
  have hdk1 : dataL.d k = 1 := by
    have hzk := dataL.zeta_deg k
    rw [hkφ, hdeg, hζ01] at hzk
    have hmul : dataL.d k * (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ)
        = 1 * (((maxNilpotentNormalHall L).subgroupOf L).index : ℂ) := by
      rw [one_mul]; exact hzk.symm
    exact mul_right_cancel₀ hidx_ne hmul
  -- `φ − ζ_0 ∈ zSupportedSpan 𝓛 A`.
  have hmem : (φ - dataL.zeta 0) ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan dataL.typeIHyp.Sset dataL.typeIHyp.A := by
    refine (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff).mpr
      ⟨Submodule.sub_mem _ (Submodule.subset_span hφ)
        (Submodule.subset_span (dataL.zeta_mem_Sset (Ne.symm dataL.ind1H_ne_zero))), ?_⟩
    have hval : φ - dataL.zeta 0 = dataL.zeta k - dataL.d k • dataL.zeta 0 := by
      rw [hkφ, hdk1, one_smul]
    rw [hval]
    exact dataL.psi_support hG k
  -- Both sides equal `τ(φ − ζ_0)`.
  have hR : dataL.coh.extension φ - dataL.coh.extension (dataL.zeta 0)
      = dataL.typeIHyp.tau (φ - dataL.zeta 0) := by
    rw [← map_sub]; exact dataL.coh.extends_on_supported _ hmem
  have hL : typeIBetaL dataL.typeIHyp (dataL.zeta 0) - typeIBetaL dataL.typeIHyp φ
      = dataL.typeIHyp.tau (φ - dataL.zeta 0) := by
    simp only [typeIBetaL]
    rw [← map_sub]
    congr 1
    abel
  rw [hR, hL]

end OddOrder.Peterfalvi.S15
