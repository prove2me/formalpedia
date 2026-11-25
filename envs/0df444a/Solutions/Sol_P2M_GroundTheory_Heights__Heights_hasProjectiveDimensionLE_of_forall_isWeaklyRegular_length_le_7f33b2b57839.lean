-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_of_forall_isWeaklyRegular_length_le_7f33b2b57839
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:52:08.272528+00:00
-- url     : https://prove2.me/submissions/ad215f2f-d809-4836-9d8c-5287d9f005ca

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AuslanderBuchsbaumDepthBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular_aff001e5abe6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_hasProjectiveDimensionLT_of_quotSMulTop_588b6ec3e228
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_length_le_of_isWeaklyRegular_quotient_span_singleton_aecea1ce41b2
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_hasProjectiveDimensionLT_quotSMulTop


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open IsLocalRing CategoryTheory RingTheory.Sequence Ideal
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R],
      (∀ rs : List R, (∀ r ∈ rs, r ∈ maximalIdeal R) → IsWeaklyRegular R rs → rs.length ≤ d) →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (k : ℕ),
        HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1) →
          HasProjectiveDimensionLE (ModuleCat.of R M) d := by
  induction d with
  | zero =>
    intro R _ _ _ hd M _ _ _ k hM
    refine hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular (fun y hy hy' ↦ ?_) M k hM
    have := hd [y] (by simpa using hy) ((isWeaklyRegular_singleton_iff R y).mpr hy')
    simp at this
  | succ d ih =>
    intro R _ _ _ hd M _ _ _ k hM
    by_cases hex : ∃ y ∈ maximalIdeal R, IsSMulRegular R y
    swap
    · push Not at hex
      have := hasProjectiveDimensionLE_zero_of_forall_not_isSMulRegular hex M k hM
      exact hasProjectiveDimensionLT_of_ge _ (0 + 1) (d + 1 + 1) (by omega)
    obtain ⟨x, hx, hxR⟩ := hex
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (R ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (R ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hd' := length_le_of_isWeaklyRegular_quotient_span_singleton hx hxR d hd
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hproj : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hproj).mp
        (hasProjectiveDimensionLT_of_ge _ (k + 1) (k + 1 + 1) (by omega))
    have hxF : IsSMulRegular (Fin n → R) x := by
      intro a b h
      funext i
      exact hxR (congrFun h i)
    have hxK : IsSMulRegular K x := fun a b h ↦ Subtype.ext (hxF (congrArg Subtype.val h))
    have hKx := GroundTheory.Arith.SchemeCoh.hasProjectiveDimensionLT_quotSMulTop hxR k K hxK hK
    have : Module.Finite (R ⧸ span {x}) (QuotSMulTop x K) :=
      Module.Finite.of_restrictScalars_finite R _ _
    have hKx' := ih (R ⧸ span {x}) hd' (QuotSMulTop x K) k hKx
    have hK2 := hasProjectiveDimensionLT_of_quotSMulTop hx hxR d K hxK hKx'
    exact (hS.hasProjectiveDimensionLT_X₃_iff d hproj).mpr hK2
end GroundTheory.Heights₂.Heights
