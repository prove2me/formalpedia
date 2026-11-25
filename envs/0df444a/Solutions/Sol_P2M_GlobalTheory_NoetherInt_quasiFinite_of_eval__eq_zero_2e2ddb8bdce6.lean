-- Prove2me | solution 1 for P2M_GlobalTheory_NoetherInt_quasiFinite_of_eval__eq_zero_2e2ddb8bdce6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:44.996146+00:00
-- url     : https://prove2.me/submissions/67c8110b-5ff0-45ff-8ddf-560781e6dcb3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsQuasiFinitePolynomialMap
import Theorems.Thm_GlobalTheory_NoetherInt_quasiFinite_quotient_of_isUnit_coeff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NoetherInt
open Polynomial
namespace GlobalTheory.NoetherInt
theorem _root_.solution {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (t : T)
    (h : (eval₂RingHom φ t).QuasiFinite) (G : R[X]) (hG : eval₂ φ t G = 0) (k : ℕ)
    (hc : IsUnit (G.coeff k)) : φ.QuasiFinite := by
  have hker : ∀ a ∈ Ideal.span {G}, eval₂RingHom φ t a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hG]
  let ψ : (R[X] ⧸ Ideal.span {G}) →+* T := Ideal.Quotient.lift _ (eval₂RingHom φ t) hker
  have h1 : ψ.comp (Ideal.Quotient.mk (Ideal.span {G})) = eval₂RingHom φ t := by
    ext <;> simp [ψ]
  have h2 : ψ.QuasiFinite := RingHom.QuasiFinite.of_comp (g := Ideal.Quotient.mk (Ideal.span {G}))
    (h1 ▸ h)
  have h3 : (algebraMap R (R[X] ⧸ Ideal.span {G})).QuasiFinite :=
    RingHom.quasiFinite_algebraMap.2 (quasiFinite_quotient_of_isUnit_coeff G k hc)
  have h4 : ψ.comp (algebraMap R (R[X] ⧸ Ideal.span {G})) = φ := by
    ext a
    simp [ψ, IsScalarTower.algebraMap_apply R R[X] (R[X] ⧸ Ideal.span {G})]
  exact h4 ▸ h2.comp h3
end GlobalTheory.NoetherInt
