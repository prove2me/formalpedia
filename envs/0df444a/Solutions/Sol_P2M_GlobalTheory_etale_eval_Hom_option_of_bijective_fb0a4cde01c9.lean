-- Prove2me | solution 1 for P2M_GlobalTheory_etale_eval_Hom_option_of_bijective_fb0a4cde01c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:32.418449+00:00
-- url     : https://prove2.me/submissions/02c4cf3c-6ed9-42fe-9c20-8b7908326927

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtalePolynomialSubstitution
import Theorems.Thm_GlobalTheory_etale_mvPolynomial_map_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial
namespace GlobalTheory
theorem _root_.solution {k A R N : Type} [CommRing k] [CommRing A] [CommRing R] (α : k →+* A) (t : A) (f : A →+* R) (n : N → R) {d : ℕ} (e : Fin (d + 1) ≃ Option N)
    (hg : (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t)).Etale) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom f n)) : (MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n)).Etale := by
  let ι : MvPolynomial (Fin (d+1)) k →+* MvPolynomial N (MvPolynomial (Fin 1) k) :=
    eval₂Hom (C.comp C) (fun j => (e j).elim (C (X 0)) X)
  let κ : MvPolynomial N (MvPolynomial (Fin 1) k) →+* MvPolynomial (Fin (d+1)) k :=
    eval₂Hom (eval₂Hom C (fun _ => X (e.symm none))) (fun i => X (e.symm (some i)))
  have h1 : κ.comp ι = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι, κ]
    · intro j
      obtain ⟨o, rfl⟩ := e.symm.surjective j
      cases o <;> simp [ι, κ]
  have h2 : ι.comp κ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro r; simp [ι, κ]
      · intro j
        obtain rfl : j = 0 := Subsingleton.elim _ _
        simp [ι, κ]
    · intro j
      simp [ι, κ]
  have hι : Function.Bijective ι :=
    Function.bijective_iff_has_inverse.2 ⟨κ, fun x => DFunLike.congr_fun h1 x, fun x => DFunLike.congr_fun h2 x⟩
  have key : MvPolynomial.eval₂Hom (f.comp α) (fun j => (e j).elim (f t) n) =
      (MvPolynomial.eval₂Hom f n).comp ((MvPolynomial.map (MvPolynomial.eval₂Hom α (fun _ : Fin 1 => t))).comp ι) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ι]
    · intro j
      obtain ⟨o, rfl⟩ := e.symm.surjective j
      cases o <;> simp [ι]
  rw [key]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hι) (etale_mvPolynomial_map_of_etale _ hg))
    (RingHom.Etale.of_bijective hΦ)
end GlobalTheory
