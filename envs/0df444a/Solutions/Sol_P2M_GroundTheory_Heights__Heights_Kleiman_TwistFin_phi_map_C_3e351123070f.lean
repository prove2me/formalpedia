-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_map_C_3e351123070f
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:35.486927+00:00
-- url     : https://prove2.me/submissions/d8cf4d32-dc00-412a-a1ea-9379ea5e6ee6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistFiniteness_PsiOfIsHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_phi_X_e9b8826858c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistFin_algebraMap_LA_e2e747c45c95
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_cone_of_isHomogeneous_046c5887f5b7


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
open MvPolynomial AddMonoidAlgebra
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.TwistFin
variable {Ω : Type w} [Field Ω] {N r : ℕ}
variable (x : Fin (N + 1) → Ω) (η : Fin (r + 1) → Ω)
variable (S : Type u) [CommRing S] [Algebra S Ω]
namespace GroundTheory.Heights₂.Heights.Kleiman.TwistFin
theorem _root_.solution {f : Poly S N} {e : ℕ} (hf : f.IsHomogeneous e) :
    phi x η S (MvPolynomial.map (C : S →+* Sy S r) f) = single ((e : ℤ), (0 : ℤ)) (aeval x f) := by
  have key : (phi x η S).comp (MvPolynomial.map (C : S →+* Sy S r)) =
      (kapT (Ω := Ω)).toRingHom.comp (cone (S := S) x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.coe_comp, Function.comp_apply, map_C, phi_C]
      change psi η S (C a) = kapT ((cone (S := S) x) (C a))
      rw [psi, aeval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, Polynomial.algebraMap_apply, kapT,
        Polynomial.aeval_C, coe_algebraMap, Function.comp_apply, algebraMap_LA, Algebra.algebraMap_self,
        RingHom.id_apply]
      rfl
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, map_X, phi_X]
      change _ = kapT (coneGen x (X i))
      rw [coneGen, aeval_X, kapT, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, coe_algebraMap,
        Function.comp_apply, single_mul_single]
      simp
  have := congrArg (fun g => g f) key
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  rw [this]
  change kapT (cone (S := S) x f) = _
  rw [cone_of_isHomogeneous x hf, kapT, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    coe_algebraMap, Function.comp_apply, single_pow, single_mul_single]
  simp [MvPolynomial.aeval_def]
end GroundTheory.Heights₂.Heights.Kleiman.TwistFin
