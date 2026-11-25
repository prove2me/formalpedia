-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.reesChart_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:34:45.091031+00:00
-- url     : https://prove2.me/submissions/0722ca3c-0107-4d0b-83f1-98abc9f14965

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WChartsB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ} (g : Fin m → R)
    (j : Fin m) (hj : φ (g j) ∈ nonZeroDivisors S) (c : Fin m → S) (hc : ∀ k, φ (g k) = c k * φ (g j)) :
    ∃ ψ : FinalTheorems.reesChart g j →+* S, ψ.comp (algebraMap R (FinalTheorems.reesChart g j)) = φ := by
  let S' := Localization.Away (φ (g j))
  have hinj : Function.Injective (algebraMap S S') :=
    IsLocalization.injective S' (Submonoid.powers_le.2 hj)
  let L : Localization.Away (g j) →+* S' := IsLocalization.Away.map _ _ φ (g j)
  have hL : ∀ r, L (algebraMap R _ r) = algebraMap S S' (φ r) := fun r =>
    IsLocalization.map_eq _ _
  have key : ∀ x ∈ FinalTheorems.reesChart g j, L x ∈ (algebraMap S S').range := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      refine ⟨c k, ?_⟩
      have hu : IsUnit (algebraMap S S' (φ (g j))) := IsLocalization.Away.algebraMap_isUnit _
      apply hu.mul_left_injective
      have := congrArg L (IsLocalization.mk'_spec (Localization.Away (g j)) (g k)
        (⟨g j, Submonoid.mem_powers _⟩ : Submonoid.powers (g j)))
      rw [map_mul, hL, hL] at this
      show algebraMap S S' (c k) * _ = L _ * _
      rw [← map_mul, ← hc]; exact this.symm
    | algebraMap r => exact ⟨φ r, (hL r).symm⟩
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  let F : FinalTheorems.reesChart g j →+* (algebraMap S S').range :=
    (L.comp (FinalTheorems.reesChart g j).val.toRingHom).codRestrict _ (fun x => key x.1 x.2)
  let E : S ≃+* (algebraMap S S').range :=
    RingEquiv.ofBijective (algebraMap S S').rangeRestrict
      ⟨fun a b h => hinj (congrArg Subtype.val h), (algebraMap S S').rangeRestrict_surjective⟩
  refine ⟨E.symm.toRingHom.comp F, ?_⟩
  ext r
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [RingEquiv.symm_apply_eq]
  apply Subtype.ext
  simp [F, E, hL]
  try rfl
end ReciprocityTheory.AnForm.R
