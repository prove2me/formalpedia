-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inr_8f0acfaa3c65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:12.425823+00:00
-- url     : https://prove2.me/submissions/ab08cbc9-bd09-4c81-a1ee-90a90fe51e84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K]
namespace GroundTheory.Heights₂.Heights.Vertical.SecBFinite
theorem _root_.solution (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    specHom e n v (rename Sum.inr g) =
      C (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (parIdx e n) g)) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, rename_C, specHom, eval₂Hom_C, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v),
      MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq, C_add]
  | mul_X p ij hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp, C_mul, rename_X, rename_X]
    congr 1
    simp [specHom, parY]
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
