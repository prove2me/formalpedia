-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_ampleRing_6d2cad07e10d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:10.770709+00:00
-- url     : https://prove2.me/submissions/993d4dd8-bb69-4d7b-8fae-afaa0198aaa9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrictionPowers
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_res_exists_mul_mem_pow_f29f9a78302a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_mul_d12ec9174181
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_chartRing_sub_ampleChart_80ef58d2b323
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_ampleChart_pow_e61756f6a50e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_xProd_ne_zero_02420b01a7e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_res_exists_pow_mul_mem_chartRing_806e14e20021

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (H : LineBundle S x) {σ b : Ω} {J : Chart x}
    (hb : b ∈ ampleRing H.toSubSystem 1 σ)
    (hbJ : ∀ I : Chart x, ∃ e : ℕ,
      b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card) ∈ ampleChart H.toSubSystem 1 σ I)
    {z : Ω} (hz : z ∈ ampleChart H.toSubSystem 1 σ J) :
    ∃ E : ℕ, b ^ E * z ∈ ampleRing H.toSubSystem 1 σ := by
  have hloc : ∀ I : Chart x, ∃ E : ℕ, b ^ E * z ∈ ampleChart H.toSubSystem 1 σ I := by
    intro I
    have hIK : I.1 ⊆ (resUnionChart x I J).1 := Finset.subset_union_left
    have hJK : J.1 ⊆ (resUnionChart x I J).1 := Finset.subset_union_right
    obtain ⟨n, hn⟩ := hz
    rw [one_mul] at hn
    have hnK := (H.pow n).mono J (resUnionChart x I J) hJK _ hn
    obtain ⟨a, ha, haz⟩ := H.res_exists_mul_mem_pow hIK n hnK
    have haz' : (a : Ω) * z ∈ ampleChart H.toSubSystem 1 σ I :=
      ⟨n, by rw [one_mul, mul_assoc]; exact haz⟩
    obtain ⟨v, hv⟩ := ha.exists_right_inv
    have hav : (a : Ω) * (v : Ω) = 1 := congrArg Subtype.val hv
    obtain ⟨M, hM⟩ := res_exists_pow_mul_mem_chartRing I J v.2
    obtain ⟨e, he⟩ := hbJ I
    refine ⟨e * M, ?_⟩
    have hxI := res_xProd_ne_zero I
    have hxJ := res_xProd_ne_zero J
    have htt : (xProd J ^ I.1.card / xProd I ^ J.1.card) *
        (xProd I ^ J.1.card / xProd J ^ I.1.card) = 1 := by
      field_simp
    have key : b ^ (e * M) * z = ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) *
        (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) := by
      have : ((xProd J ^ I.1.card / xProd I ^ J.1.card) ^ M * (v : Ω)) *
          (b ^ e * (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * ((a : Ω) * z) =
          ((xProd J ^ I.1.card / xProd I ^ J.1.card) *
            (xProd I ^ J.1.card / xProd J ^ I.1.card)) ^ M * b ^ (e * M) * ((a : Ω) * v) * z := by
        ring
      rw [this, htt, hav]; ring
    rw [key]
    exact res_ampleChart_mul (res_ampleChart_mul (res_chartRing_sub_ampleChart hM) (res_ampleChart_pow he M)) haz'
  choose E hE using hloc
  refine ⟨Finset.univ.sup E, Set.mem_iInter.mpr fun I => ?_⟩
  have hle : E I ≤ Finset.univ.sup E := Finset.le_sup (Finset.mem_univ I)
  have hbI : b ∈ ampleChart H.toSubSystem 1 σ I := Set.mem_iInter.mp hb I
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact res_ampleChart_mul (res_ampleChart_pow hbI _) (hE I)
end GroundTheory.Heights₂.Heights.Kleiman
