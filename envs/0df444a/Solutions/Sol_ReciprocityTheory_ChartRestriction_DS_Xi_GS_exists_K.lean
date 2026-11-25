-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Xi.GS.exists_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:13.258127+00:00
-- url     : https://prove2.me/submissions/e64ba0fa-2974-4ebe-a19c-0f79cf850125

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_FixOfPerp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_ExistsKmat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_HE
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_HE_adj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Xi_GS_fix_of_perp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Xi ReciprocityTheory.ChartRestriction.DS.Xi.GS
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
variable {k r : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GS
theorem _root_.solution (hk : 1 ≤ k) (c u : Fin (r + 1) → EE k r) (hc : Orthonormal ℂ c) (hu : Orthonormal ℂ u)
    (hci : ∀ a b, inner ℂ (c a) (HE k r (c b)) = 0) (hui : ∀ a b, inner ℂ (u a) (HE k r (u b)) = 0) :
    ∃ κL : EE k r ≃ₗᵢ[ℂ] EE k r, (∀ a, κL (c a) = u a) ∧ ∀ x, κL (HE k r x) = HE k r (κL x) := by
  have hF : ∀ w : Fin (r + 1) → EE k r, Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      Orthonormal ℂ (Sum.elim w (fun a => HE k r (w a))) := by
    intro w hw hwi
    rw [orthonormal_iff_ite] at hw ⊢
    rintro (a | a) (b | b)
    · simp [hw]
    · simp [hwi]
    · simp [HE_adj, hwi]
    · simp [HE_adj, HE_HE, hw]
  have hcard : Module.finrank ℂ (EE k r) = Fintype.card ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) := by
    simp; omega
  have hres : ∀ w : Fin (r + 1) ⊕ Fin (r + 1) → EE k r, Orthonormal ℂ w →
      Orthonormal ℂ ((Set.range (Sum.inl : _ → (Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1))).restrict
        (Sum.elim w 0)) := by
    intro w hw
    rw [orthonormal_iff_ite] at hw ⊢
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    change inner ℂ (w p) (w q) = _
    rw [hw p q]
    by_cases hpq : p = q
    · subst hpq; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg hpq, if_neg]; intro h; exact hpq (Sum.inl_injective (congrArg Subtype.val h))
  obtain ⟨bP, hbP⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF c hc hci))
  obtain ⟨bQ, hbQ⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard (hres _ (hF u hu hui))
  have hP : ∀ p, bP (Sum.inl p) = Sum.elim c (fun a => HE k r (c a)) p := fun p => hbP _ ⟨p, rfl⟩
  have hQ : ∀ p, bQ (Sum.inl p) = Sum.elim u (fun a => HE k r (u a)) p := fun p => hbQ _ ⟨p, rfl⟩
  set κL := bP.repr.trans bQ.repr.symm with hκL
  have hκb : ∀ i, κL (bP i) = bQ i := fun i => by simp [hκL]
  have hc1 : ∀ a, κL (c a) = u a := fun a => by
    have := hκb (Sum.inl (Sum.inl a)); rwa [hP, hQ] at this
  have hc2 : ∀ a, κL (HE k r (c a)) = HE k r (u a) := fun a => by
    have := hκb (Sum.inl (Sum.inr a)); rwa [hP, hQ] at this
  have hfix : ∀ (b : OrthonormalBasis ((Fin (r + 1) ⊕ Fin (r + 1)) ⊕ Fin (k - 1)) ℂ (EE k r))
      (w : Fin (r + 1) → EE k r), Orthonormal ℂ w → (∀ a b, inner ℂ (w a) (HE k r (w b)) = 0) →
      (∀ p, b (Sum.inl p) = Sum.elim w (fun a => HE k r (w a)) p) →
      ∀ j, HE k r (b (Sum.inr j)) = b (Sum.inr j) := by
    intro b w hw hwi hb j
    refine fix_of_perp w hw hwi _ (fun a => ?_) (fun a => ?_)
    · have := hb (Sum.inl a); simp only [Sum.elim_inl] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
    · have := hb (Sum.inr a); simp only [Sum.elim_inr] at this
      rw [← this]; exact b.orthonormal.2 (by simp)
  refine ⟨κL, hc1, fun x => ?_⟩
  have key : (κL.toLinearEquiv.toLinearMap).comp (HE k r) = (HE k r).comp κL.toLinearEquiv.toLinearMap := by
    refine bP.toBasis.ext fun i => ?_
    simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rcases i with (a | a) | j
    · rw [hP, Sum.elim_inl, hc2, hc1]
    · rw [hP, Sum.elim_inr, HE_HE, hc1, hc2, HE_HE]
    · rw [hfix bP c hc hci hP j, hκb, hfix bQ u hu hui hQ j]
  simpa using LinearMap.congr_fun key x
end ReciprocityTheory.ChartRestriction.DS.Xi.GS
