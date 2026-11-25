-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CauchyBinetAlt_sum_reindex_e19d84f6339c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:28.56832+00:00
-- url     : https://prove2.me/submissions/1d5d12c4-285c-4d58-994a-2718b3921089

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCauchyBinet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Finset Equiv
open GroundTheory.Heights₂.Heights.CauchyBinetAlt
variable {R : Type*} [CommRing R] {j N : ℕ}
namespace GroundTheory.Heights₂.Heights.CauchyBinetAlt
theorem _root_.solution {M : Type*} [AddCommMonoid M] (g : (Fin j → Fin N) → M)
    (hg : ∀ p, ¬ Function.Injective p → g p = 0) :
    ∑ p, g p = ∑ I : {I : Finset (Fin N) // I.card = j}, ∑ w : Perm (Fin j),
      g (I.1.orderEmbOfFin I.2 ∘ w) := by
  rw [← Finset.sum_filter_of_ne (p := Function.Injective)
    (fun p _ h => by_contra fun hp => h (hg p hp))]
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij (fun x _ => x.1.1.orderEmbOfFin x.1.2 ∘ x.2) ?_ ?_ ?_ ?_
  · rintro ⟨I, w⟩ _
    simp only [mem_filter, mem_univ, true_and]
    exact (I.1.orderEmbOfFin I.2).injective.comp w.injective
  · rintro ⟨I, w⟩ _ ⟨J, w'⟩ _ h
    simp only at h
    have key : ∀ (K : {I : Finset (Fin N) // I.card = j}) (v : Perm (Fin j)) (x : Fin N),
        x ∈ K.1 ↔ ∃ a, (K.1.orderEmbOfFin K.2 ∘ v) a = x := by
      intro K v x
      rw [← Finset.mem_coe, ← range_orderEmbOfFin K.1 K.2, Set.mem_range]
      exact ⟨fun ⟨a, ha⟩ => ⟨v.symm a, by simpa using ha⟩, fun ⟨a, ha⟩ => ⟨v a, ha⟩⟩
    have hIJ : I = J := by
      apply Subtype.ext
      ext x
      rw [key I w x, key J w' x, h]
    subst hIJ
    have hw : w = w' := Equiv.ext fun a => (I.1.orderEmbOfFin I.2).injective (congrFun h a)
    rw [hw]
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    have hI : (univ.image p).card = j := by
      rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]
    let w0 : Fin j → Fin j := fun a =>
      ((univ.image p).orderIsoOfFin hI).symm ⟨p a, mem_image_of_mem p (mem_univ a)⟩
    have hw0 : Function.Injective w0 := by
      intro a b hab
      exact hp (congrArg Subtype.val (((univ.image p).orderIsoOfFin hI).symm.injective hab))
    refine ⟨(⟨univ.image p, hI⟩, Equiv.ofBijective w0 (Finite.injective_iff_bijective.mp hw0)),
      mem_univ _, ?_⟩
    funext a
    show ((univ.image p).orderEmbOfFin hI) (w0 a) = p a
    rw [← coe_orderIsoOfFin_apply]
    simp only [w0, OrderIso.apply_symm_apply]
  · intro x _
    rfl
end GroundTheory.Heights₂.Heights.CauchyBinetAlt
