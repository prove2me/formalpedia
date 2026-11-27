-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isFrobAt_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:27:55.03554+00:00
-- url     : https://prove2.me/submissions/911e1c31-142c-405e-8b05-0bc9ac66c559

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_SUnitGalois_GalSmulAsIdeal
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_IsFrobAtMulOfMemInertiaGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1
open scoped Pointwise
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable {K L}
variable (v : HeightOneSpectrum (𝓞 K)) (Q Q' : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal]
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution (hv : IsUnramifiedIn K v L) (τ τ' : L ≃ₐ[K] L) (h : IsFrobAt K L τ Q)
    (h' : IsFrobAt K L τ' Q) : τ = τ' := by
  have : Algebra.IsUnramifiedAt (𝓞 K) Q :=
    Ideal.ramificationIdx_eq_one_iff.mp (hv Q inferInstance inferInstance)
  have e := h.eq_of_isUnramifiedAt h' Q.primeCompl_le_nonZeroDivisors
  apply (galRestrict (𝓞 K) K L (𝓞 L)).injective
  exact AlgEquiv.ext fun x => DFunLike.congr_fun e x
end ReciprocityTheory.DiscreteGroups.GlobalClassField
