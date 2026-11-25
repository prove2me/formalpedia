-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_of_exact_45ae9e3bf583
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:55:40.356943+00:00
-- url     : https://prove2.me/submissions/8d3660fe-376f-4563-a45e-399f3df1ef0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_QuotTransSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PQuotTrans
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_subsingleton_H_one_iff_d33e1da7ed0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_QuotTrans_d_one_d_zero_c859ff409e3f

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
universe u v w
open GroundTheory.Heights₂.Heights.Kleiman.QuotTrans
variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
namespace GroundTheory.Heights₂.Heights.Kleiman.QuotTrans
theorem _root_.solution {A B C : Cell U → Type v}
    [∀ I, AddCommGroup (A I)] [∀ I, Module R (A I)] [∀ I, AddCommGroup (B I)] [∀ I, Module R (B I)]
    [∀ I, AddCommGroup (C I)] [∀ I, Module R (C I)]
    {ρA : ∀ I J : Cell U, I.1 ⊆ J.1 → A I →ₗ[R] A J} {ρB : ∀ I J : Cell U, I.1 ⊆ J.1 → B I →ₗ[R] B J}
    {ρC : ∀ I J : Cell U, I.1 ⊆ J.1 → C I →ₗ[R] C J}
    (ι : ∀ I, A I →ₗ[R] B I) (π : ∀ I, B I →ₗ[R] C I)
    (hι : ∀ I J h m, ι J (ρA I J h m) = ρB I J h (ι I m))
    (hπ : ∀ I J h m, π J (ρB I J h m) = ρC I J h (π I m))
    (hinj : ∀ I, Function.Injective (ι I)) (hsurj : ∀ I, Function.Surjective (π I))
    (hex : ∀ I b, π I b = 0 → ∃ a, ι I a = b)
    (hρB : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : B I),
      ρB J K h' (ρB I J h m) = ρB I K (h.trans h') m)
    (hA : Subsingleton (Cech.H A ρA 1)) (hC : Subsingleton (Cech.H C ρC 1)) :
    Subsingleton (Cech.H B ρB 1) := by
  rw [subsingleton_H_one_iff] at hA hC ⊢
  intro z hz
  have hπd := Cech.mapC_d (R := R) (G := B) (G' := C) π hπ
  have hιd := Cech.mapC_d (R := R) (G := A) (G' := B) ι hι

  obtain ⟨wc, hwc⟩ := hC (Cech.mapC (R := R) (G := B) (G' := C) π 1 z) (by rw [← hπd, hz, map_zero])
  choose w hw using fun I : Cech.Idx U 0 => hsurj I.1 (wc I)
  have hmw : Cech.mapC (R := R) (G := B) (G' := C) π 0 w = wc := funext hw
  have hr : Cech.mapC (R := R) (G := B) (G' := C) π 1 (z - Cech.d B ρB 0 w) = 0 := by
    rw [map_sub, hπd 0, hmw, hwc, sub_self]

  choose g hg using fun J : Cech.Idx U 1 => hex J.1 _ (congrFun hr J)
  have hg' : Cech.mapC (R := R) (G := A) (G' := B) ι 1 g = z - Cech.d B ρB 0 w := funext hg
  have hdg : Cech.d A ρA 1 g = 0 := by
    have h2 : Cech.mapC (R := R) (G := A) (G' := B) ι (1 + 1) (Cech.d A ρA 1 g) = 0 := by
      rw [hιd 1 g, hg', map_sub, hz, d_one_d_zero hρB, sub_zero]
    funext J
    exact hinj J.1 ((congrFun h2 J).trans (map_zero (ι J.1)).symm)
  obtain ⟨v, hv⟩ := hA g hdg
  refine ⟨w + Cech.mapC (R := R) (G := A) (G' := B) ι 0 v, ?_⟩
  rw [map_add, ← hιd, hv, hg', add_sub_cancel]
end GroundTheory.Heights₂.Heights.Kleiman.QuotTrans
