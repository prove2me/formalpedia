-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FlatLocalRegularElement_iterate_65cb9cc80ded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:31:31.541804+00:00
-- url     : https://prove2.me/submissions/6ad2f70b-a735-4573-8ff0-8dcf5ba4be3d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularSequence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFlatLocalRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFlatLocalRegularSequence

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open IsLocalRing RingTheory.Sequence Pointwise
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FlatLocalRegularElement
theorem _root_.solution (h : FlatLocalRegularElement.Statement)
    {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    (hA : IsNoetherianRing A) (hB : IsNoetherianRing B) (hl : IsLocalHom (algebraMap A B))
    (ys : List B) (hys : ∀ y ∈ ys, y ∈ maximalIdeal B)
    (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    (hfin : Module.Finite B M) (hflat : Module.Flat A M)
    (hreg : IsWeaklyRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) ys) :
    IsWeaklyRegular M ys ∧ Module.Flat A (M ⧸ (Ideal.ofList ys • (⊤ : Submodule B M))) := by
  induction ys generalizing M with
  | nil =>
    refine ⟨IsWeaklyRegular.nil B M, ?_⟩
    have e : (M ⧸ (Ideal.ofList ([] : List B) • (⊤ : Submodule B M))) ≃ₗ[B] M :=
      Submodule.quotEquivOfEqBot _ (by rw [Ideal.ofList_nil, Submodule.bot_smul])
    exact Module.Flat.of_linearEquiv (e.restrictScalars A)
  | cons y ys ih =>
    rw [isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hyM, hflat'⟩ := h A B hA hB hl M hfin hflat y (hys y List.mem_cons_self) hreg.1
    have hfin' : Module.Finite B (QuotSMulTop y M) := inferInstance
    obtain ⟨h1, h2⟩ := ih (fun z hz => hys z (List.mem_cons_of_mem _ hz)) (QuotSMulTop y M) hfin' hflat'
      (((quotSMulTopQuotIdealSMulTopEquiv _ y).isWeaklyRegular_congr ys).mp hreg.2)
    refine ⟨(isWeaklyRegular_cons_iff M y ys).mpr ⟨hyM, h1⟩, ?_⟩
    have : Module.Flat A (QuotSMulTop y M ⧸ (Ideal.ofList ys • (⊤ : Submodule B (QuotSMulTop y M)))) := h2
    exact Module.Flat.of_linearEquiv
      ((Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M y ys).restrictScalars A)
end FlatLocalRegularElement
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
