-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConstantsDescend_agree_on_adjoin_74205cd88afe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:54:43.449496+00:00
-- url     : https://prove2.me/submissions/003d4d99-9683-4d1f-b4c9-3a2b65f0c383

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConstantsDescend
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConstantsDescend

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
theorem _root_.solution {Ω : Type*} [Field Ω] [CharZero Ω] (R T : Subalgebra ℤ Ω) (A : Subalgebra ℚ Ω)
    (B : Subalgebra A Ω) (hRA : ∀ r ∈ R, r ∈ A) (θ : Ω) (hθB : θ ∈ B)
    (hTθ : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ {θ})
    (H : ∀ w w' : ↥(R ⊔ T) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom)
    (w w' : B →+* ℂ) (hw : w.comp (algebraMap A B) = w'.comp (algebraMap A B)) :
    ∀ x ∈ Algebra.adjoin ℚ (T : Set Ω), x ∈ (RingHom.eqLocus w w').map B.val.toRingHom := by
  have hTB : ∀ t ∈ T, t ∈ B := fun t ht =>
    (Algebra.adjoin_le (Set.singleton_subset_iff.2 hθB) : Algebra.adjoin ℚ {θ} ≤ B.restrictScalars ℚ) (hTθ t ht)
  have hsub : ∀ x ∈ R ⊔ T, x ∈ B := by
    have : R ⊔ T ≤ B.restrictScalars ℤ :=
      sup_le (fun r hr => B.algebraMap_mem (⟨r, hRA r hr⟩ : A)) (fun t ht => hTB t ht)
    exact fun x hx => this hx
  let ι : ↥(R ⊔ T) →+* B := ((R ⊔ T).val : ↥(R ⊔ T) →ₐ[ℤ] Ω).toRingHom.codRestrict B fun x => hsub x.1 x.2
  have hR' : (w.comp ι).comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
      (w'.comp ι).comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom := by
    ext ⟨r, hr⟩
    exact RingHom.congr_fun hw (⟨r, hRA r hr⟩ : A)
  have hT' := H _ _ hR'
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem t ht =>
    refine Subring.mem_map.2 ⟨⟨t, hTB t ht⟩, ?_, rfl⟩
    exact RingHom.congr_fun hT' ⟨t, ht⟩
  | algebraMap q =>
    refine Subring.mem_map.2 ⟨algebraMap A B (algebraMap ℚ A q), RingHom.congr_fun hw _, ?_⟩
    exact (B.val.commutes _).trans (IsScalarTower.algebraMap_apply ℚ A Ω q).symm
  | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
  | mul x y _ _ hx hy => exact Subring.mul_mem _ hx hy
end GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend
