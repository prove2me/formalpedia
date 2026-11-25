-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagLineDegreeProof_subst_homog_eac77d32653b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:06:49.961559+00:00
-- url     : https://prove2.me/submissions/7e8629f0-edcf-4e79-bd35-98a37dc14fef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagLineDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PSplitRelDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagLineDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
theorem _root_.solution {K : Type*} [DecidableEq K] {ι : K → Type} {M : ℕ} {F : Type*} [CommRing F]
    (m : ℕ) (A : Fin M → MRing ι F) (hA : ∀ l, IsMultiHomog (A l) (fun _ => m))
    {h : MRing (bundleIdx ι M) F} {D : Option K → ℕ} (hh : IsMultiHomog h D) :
    IsMultiHomog (aeval (substVar A) h) (fun k => D (some k) + D none * m) := by
  let L : (Option K → ℕ) →+ (K → ℕ) :=
    { toFun := fun d k => d (some k) + d none * m
      map_zero' := by funext k; simp
      map_add' := by intro d d'; funext k; simp only [Pi.add_apply]; ring }
  have hω : ∀ p, IsMultiHomog (substVar A p) (L (blockWeight (bundleIdx ι M) p)) := by
    rintro ⟨o, i⟩
    cases o with
    | none =>
      have : L (blockWeight (bundleIdx ι M) ⟨none, i⟩) = fun _ => m := by
        funext k; simp [L, blockWeight]
      rw [this]; exact hA i
    | some k =>
      have : L (blockWeight (bundleIdx ι M) ⟨some k, i⟩) = blockWeight ι ⟨k, i⟩ := by
        funext k'; simp [L, blockWeight, Pi.single_apply]
      rw [this]; exact isWeightedHomogeneous_X F _ _
  have hD : (fun k => D (some k) + D none * m) = L D := rfl
  rw [hD, h.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro μ hμ
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
  have := (isWeightedHomogeneous_C (blockWeight ι) (coeff μ h)).mul (IsWeightedHomogeneous.prod
    μ.support (fun v => substVar A v ^ μ v) (fun v => μ v • L (blockWeight _ v))
    (fun v _ => (hω v).pow (μ v)))
  rw [zero_add] at this
  have e : L D = ∑ i ∈ μ.support, μ i • L (blockWeight _ i) := by
    rw [← hh (mem_support_iff.mp hμ), Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [e]
  exact this
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagLineDegreeProof
