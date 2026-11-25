-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ImageArith_of_found_2974011bfbbf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:02:04.380271+00:00
-- url     : https://prove2.me/submissions/52208383-b473-4d75-a97d-15a471629b64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsBlockTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_ContractRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsAlgebraicAdjoinRangeIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ImageArith
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiProjPrime_iff_45652a79ccb6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_ContractRelevant_isMultiProjPrime_comap_rename_bb5f689a2f30
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TrdegAdjoin_ringKrullDim_quotient_ker_39672f46aed5


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GroundTheory.Heights₂.Heights
namespace ImageArith
theorem _root_.solution (hBT : BlockTrdeg.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d' hK hbm hP'
  classical
  obtain ⟨-, hMP', hHor', hdim'⟩ := hP'

  have hMP : IsMultiProjPrime (imageZ v P') := by
    rw [← Bridge.isMultiProjPrime_iff] at hMP' ⊢
    exact FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := κ) (g := v) hbm.2.2.1 hbm.1 hbm.2.1
      (fun w hw ↦ hbm.2.2.2 w hw |>.imp fun _ h ↦ h) hMP'

  have hHor : IsHorizontal (imageZ v P') := by
    refine (Ideal.ext fun a ↦ ?_).trans hHor'
    simp only [imageZ, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]

  have : (P').IsPrime := hMP'.1
  set A' := MRing ι' ⧸ P'
  set L := FractionRing A'
  have hinj : Function.Injective (algebraMap ℤ A') := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at ha
    have h' : a ∈ (P').comap (C : ℤ →+* MRing ι') := ha
    rw [show (P').comap (C : ℤ →+* MRing ι') = ⊥ from hHor'] at h'
    exact (Submodule.mem_bot ℤ).mp h'
  have : CharZero A' := charZero_of_injective_algebraMap hinj
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective A' L)
  set φ' : MRing ι' →+* L := (algebraMap A' L).comp (Ideal.Quotient.mk P')
  have hker' : RingHom.ker φ' = P' := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A' L),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  set φ : MRing ι →+* L := φ'.comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
  have hker : RingHom.ker φ = imageZ v P' := by
    rw [← RingHom.comap_ker, hker']
    rfl

  obtain ⟨s', hs', hd'⟩ := TrdegAdjoin.ringKrullDim_quotient_ker φ'
  obtain ⟨s, hs, hd⟩ := TrdegAdjoin.ringKrullDim_quotient_ker φ
  rw [hker'] at hd'
  rw [hker] at hd
  have hφX : (Set.range fun p : Σ k, ι k ↦ φ (X p)) = Set.range fun p ↦ φ' (X (v p)) := by
    simp [φ]
  rw [hφX] at hs

  have h1 := hBT K ι K' ι' κ v P' L φ' hbm hMP' hker'
  rw [hs, hs'] at h1
  have h2 := @hBT Empty _ (fun k ↦ k.elim) (fun k ↦ k.elim) K _ ι _ (fun k ↦ k.elim) (fun p ↦ p.1.elim)
    (imageZ v P') L _ _ φ
    ⟨fun a ↦ a.elim, fun p ↦ p.1.elim, fun p ↦ p.1.elim, fun q ⟨a, _⟩ ↦ a.elim⟩ hMP hker
  rw [hφX, hs] at h2
  simp only [Fintype.card_empty, Nat.sub_zero] at h2
  have h1' : s + (Fintype.card K' - Fintype.card K) ≤ s' := by exact_mod_cast h1
  have h2' : Fintype.card K ≤ s := by
    have := le_trans (self_le_add_left _ _) h2
    exact_mod_cast this
  have hKK : Fintype.card K ≤ Fintype.card K' := Fintype.card_le_of_injective κ hbm.1
  rw [hdim'] at hd'
  have h3 : d' + Fintype.card K' = s' + 1 := by exact_mod_cast hd'
  refine ⟨s + 1 - Fintype.card K, by omega, hK, hMP, hHor, ?_⟩
  rw [hd]
  have : s + 1 - Fintype.card K + Fintype.card K = s + 1 := by omega
  rw [this]
  push_cast
  rfl
end ImageArith
end GroundTheory.Heights₂.Heights
