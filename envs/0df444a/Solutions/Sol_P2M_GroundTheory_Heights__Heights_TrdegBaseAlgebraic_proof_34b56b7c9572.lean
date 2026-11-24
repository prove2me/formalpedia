-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TrdegBaseAlgebraic_proof_34b56b7c9572
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:51.177641+00:00
-- url     : https://prove2.me/submissions/0bc90c44-06ed-4572-a84e-cdd354fbb180

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsTrdegBaseAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PTrdegBaseAlgebraic

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
open Cardinal
namespace GroundTheory.Heights₂.Heights
namespace TrdegBaseAlgebraic
theorem _root_.solution : TrdegBaseAlgebraic.Statement := by
  intro F K Ω _ _ _ _ _ _ _ hKF ι z
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F Ω, A = Algebra.adjoin F (Set.range z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subalgebra K Ω, B = Algebra.adjoin K (Set.range z) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hAB : ∀ w ∈ A, w ∈ B := by
    intro w hw
    rw [hA] at hw
    rw [hB]
    induction hw using Algebra.adjoin_induction with
    | mem w hw => exact Algebra.subset_adjoin hw
    | algebraMap c =>
      rw [IsScalarTower.algebraMap_apply F K Ω c]
      exact Subalgebra.algebraMap_mem _ _
    | add u v _ _ hu hv => exact Subalgebra.add_mem _ hu hv
    | mul u v _ _ hu hv => exact Subalgebra.mul_mem _ hu hv

  let i : A →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis F A
  let x : t → B := fun a => i a
  set C : Subalgebra K B := Algebra.adjoin K (Set.range x) with hC

  have hFC : ∀ r ∈ Algebra.adjoin F (Set.range ((↑) : t → A)), i r ∈ C := by
    intro r hr
    induction hr using Algebra.adjoin_induction with
    | mem r hr =>
      obtain ⟨a, rfl⟩ := hr
      exact Algebra.subset_adjoin ⟨a, rfl⟩
    | algebraMap c =>
      have : i (algebraMap F A c) = algebraMap K B (algebraMap F K c) := by
        apply Subtype.ext
        exact (IsScalarTower.algebraMap_apply F K Ω c)
      rw [this]
      exact C.algebraMap_mem _
    | add r s _ _ hr hs =>
      rw [map_add]
      exact C.add_mem hr hs
    | mul r s _ _ hr hs =>
      rw [map_mul]
      exact C.mul_mem hr hs
  let f : Algebra.adjoin F (Set.range ((↑) : t → A)) →+* C :=
    { toFun := fun r => ⟨i r, hFC r r.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => ((c : B) : Ω)) hab
  have key : ∀ (w : Ω), w ∈ Algebra.adjoin K (Set.range z) →
      ∀ (hw : w ∈ B), IsAlgebraic C (⟨w, hw⟩ : B) := by
    intro w hw'
    induction hw' using Algebra.adjoin_induction with
    | mem w hw' =>
      intro hw
      obtain ⟨m, rfl⟩ := hw'
      have hzA : z m ∈ A := hA ▸ Algebra.subset_adjoin ⟨m, rfl⟩
      have h1 : IsAlgebraic (Algebra.adjoin F (Set.range ((↑) : t → A))) (⟨z m, hzA⟩ : A) :=
        ht.isAlgebraic.isAlgebraic _
      exact h1.ringHom_of_comp_eq f i hf (RingHom.ext fun _ => rfl)
    | algebraMap k =>
      intro hw
      exact (hKF.isAlgebraic k).ringHom_of_comp_eq ((algebraMap K C).comp (algebraMap F K))
        (algebraMap K B) (RingHom.injective _) (RingHom.ext fun _ => rfl)
    | add u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).add (hv (hB ▸ hv'))
    | mul u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).mul (hv (hB ▸ hv'))
  have alg : Algebra.IsAlgebraic C B := ⟨fun b => key b.1 (hB ▸ b.2) b.2⟩
  calc Algebra.trdeg K B ≤ #(Set.range x) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range x)
    _ ≤ #t := Cardinal.mk_range_le
    _ = Algebra.trdeg F A := ht.cardinalMk_eq_trdeg
end TrdegBaseAlgebraic
end GroundTheory.Heights₂.Heights
