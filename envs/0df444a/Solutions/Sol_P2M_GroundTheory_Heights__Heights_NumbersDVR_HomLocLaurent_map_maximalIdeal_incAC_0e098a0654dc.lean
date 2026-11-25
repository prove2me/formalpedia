-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_map_maximalIdeal_incAC_0e098a0654dc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:10:34.57251+00:00
-- url     : https://prove2.me/submissions/77c89814-dbb5-4c39-bd9b-67db817c99a5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpFibreDegreeCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDivCycleHomLocLaurent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HomLocLaurent_incAC_isLocalHom_02e2103e1a9e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
open GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
variable [Fintype K] {P W : Ideal (MRing ι R)} [P.IsPrime] [W.IsPrime]
variable (T : ∀ k, ι k) (hPW : P ≤ W) (hT : ∀ k, (X ⟨k, T k⟩ : MRing ι R) ∉ W)
include hT
namespace GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
theorem _root_.solution [IsLocalRing (homLocRing P W)] (hWh : IsMultiHomogIdeal W) :
    letI := (algQC hPW).toAlgebra
    haveI := wbar_isPrime hPW
    haveI := locC_isLocalization hPW
    haveI := IsLocalization.AtPrime.isLocalRing (locC hPW) (W.map (Ideal.Quotient.mk P))
    (IsLocalRing.maximalIdeal (homLocRing P W)).map (incAC hPW) =
      IsLocalRing.maximalIdeal (locC hPW) := by
  letI := (algQC hPW).toAlgebra
  haveI := wbar_isPrime hPW
  haveI := locC_isLocalization hPW
  haveI := IsLocalization.AtPrime.isLocalRing (locC hPW) (W.map (Ideal.Quotient.mk P))
  haveI := incAC_isLocalHom T hPW hT
  have hne : ∀ {g : MRing ι R}, g ∉ W → fr P g ≠ 0 := fun hg => fr_ne_zero fun h => hg (hPW h)
  have hunit : ∀ {g : MRing ι R}, g ∉ W →
      IsUnit (algQC hPW (Ideal.Quotient.mk P g)) := fun hg =>
    (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mpr
      fun h => hg ((Ideal.mem_quotient_iff_mem hPW).mp h)
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun h => (IsLocalRing.mem_maximalIdeal _).mp hx (isUnit_of_map_unit _ _ h)
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (W.map (Ideal.Quotient.mk P)) (locC hPW),
      Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap]
    conv => rw [← sum_weightedHomogeneousComponent (w := blockWeight ι) w]
    refine finsum_induction (fun q => ((algQC hPW).comp
        (Ideal.Quotient.mk P)) q ∈ (IsLocalRing.maximalIdeal (homLocRing P W)).map (incAC hPW))
      (by rw [RingHom.map_zero]; exact zero_mem _)
      (fun x y hx hy => by rw [RingHom.map_add]; exact add_mem hx hy)
      fun b => ?_
    set wb := weightedHomogeneousComponent (blockWeight ι) b w
    have hwb : IsMultiHomog wb b := weightedHomogeneousComponent_isWeightedHomogeneous b w
    have hwbW : wb ∈ W := hWh w hw b
    set c : homLocRing P W := ⟨fr P wb / fr P (tpow T b), frac_mem hwb (isMultiHomog_tpow T b)
      (tpow_not_mem T hT b)⟩
    have hce : ((algQC hPW).comp (Ideal.Quotient.mk P)) wb =
        incAC hPW c * algQC hPW (Ideal.Quotient.mk P (tpow T b)) := by
      apply Subtype.ext
      change fr P wb = fr P wb / fr P (tpow T b) * fr P (tpow T b)
      rw [div_mul_cancel₀ _ (hne (tpow_not_mem T hT b))]
    rw [hce]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hc
    have hu : IsUnit (((algQC hPW).comp (Ideal.Quotient.mk P)) wb) := by
      rw [hce]; exact (hc.map _).mul (hunit (tpow_not_mem T hT b))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (locC hPW) (W.map (Ideal.Quotient.mk P)) _).mp hu
      (Ideal.mem_map_of_mem _ hwbW)
end GroundTheory.Heights₂.Heights.NumbersDVR.HomLocLaurent
