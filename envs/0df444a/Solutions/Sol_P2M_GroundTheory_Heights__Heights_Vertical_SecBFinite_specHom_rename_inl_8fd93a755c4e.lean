-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_specHom_rename_inl_8fd93a755c4e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:10.481179+00:00
-- url     : https://prove2.me/submissions/355b60f8-4733-46e1-a9df-655755eeeae0

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
    (p : MvPolynomial (Fin n) (𝓞 K)) :
    specHom e n v (rename Sum.inl p) = MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) p := by
  rw [specHom, coe_eval₂Hom, eval₂_rename, Sum.elim_comp_inl]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [eval₂_add, hp, hq, map_add]
  | mul_X p i hp => rw [eval₂_mul, hp, eval₂_X, map_mul, map_X]
end GroundTheory.Heights₂.Heights.Vertical.SecBFinite
