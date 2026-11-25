-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.exists_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:57:48.806236+00:00
-- url     : https://prove2.me/submissions/703f826a-b8fb-4c10-9920-b4a28541c742

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_LagrangianStabilizerCharacterTrivial
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
set_option linter.unusedSectionVars false
variable {k : Type} [Field k] [Invertible (2 : k)] {K : Type} [CommRing K] [Algebra k K] {c : K →ₐ[k] K}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
omit [Invertible (2 : k)]
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution {ξ₀ : K} (hq : IsQuad c ξ₀) (ν α : Type) [Fintype ν] [Fintype α] [DecidableEq α] :
    ∃ (r : ℕ) (e : (Fin r → k) ≃ₗ[k] Matrix ν α K), ∀ t : GL α K, ∃ g : GL (Fin r) k,
      (∀ x, e (g.val *ᵥ x) = e x * t.valᵀ) ∧ GeneralLinearGroup.det g =
        Units.map (Algebra.norm k : K →* k) (GeneralLinearGroup.det t) ^ Fintype.card ν := by
  obtain ⟨b, -, -⟩ := hq.basis
  have : Module.Free k K := Module.Free.of_basis b
  have : Module.Finite k K := Module.Finite.of_basis b
  refine ⟨Module.finrank k (Matrix ν α K), (Module.finBasis k (Matrix ν α K)).equivFun.symm, fun t => ?_⟩
  set e := (Module.finBasis k (Matrix ν α K)).equivFun.symm
  let TK : GL α K → Matrix ν α K →ₗ[K] Matrix ν α K := fun s =>
    { toFun := fun x => x * (s : Matrix α α K)ᵀ
      map_add' := fun x y => Matrix.add_mul x y _
      map_smul' := fun a x => Matrix.smul_mul a x _ }
  let F : GL α K → (Fin (Module.finrank k (Matrix ν α K)) → k) →ₗ[k]
      (Fin (Module.finrank k (Matrix ν α K)) → k) := fun s =>
    (e.symm : Matrix ν α K →ₗ[k] _) ∘ₗ (TK s).restrictScalars k ∘ₗ (e.symm.symm : _ →ₗ[k] Matrix ν α K)
  have hF : ∀ s x, F s x = e.symm (e x * (s : Matrix α α K)ᵀ) := fun s x => rfl
  have hinv : ∀ s s' : GL α K, s' * s = 1 → F s' ∘ₗ F s = LinearMap.id := by
    intro s s' hss
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, hF, hF, LinearEquiv.apply_symm_apply, Matrix.mul_assoc,
      ← Matrix.transpose_mul, ← Units.val_mul, hss, Units.val_one, Matrix.transpose_one, Matrix.mul_one,
      LinearEquiv.symm_apply_apply, LinearMap.id_apply]
  let g : GL (Fin (Module.finrank k (Matrix ν α K))) k :=
    ⟨LinearMap.toMatrix' (F t), LinearMap.toMatrix' (F t⁻¹),
      by rw [← LinearMap.toMatrix'_comp, hinv _ _ (mul_inv_cancel t), LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, hinv _ _ (inv_mul_cancel t), LinearMap.toMatrix'_id]⟩
  refine ⟨g, fun x => ?_, ?_⟩
  · change e (LinearMap.toMatrix' (F t) *ᵥ x) = _
    rw [LinearMap.toMatrix'_mulVec, hF, LinearEquiv.apply_symm_apply]
  · have hpi : (Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ TK t ∘ₗ
        (Matrix.ofLinearEquiv K).symm.symm.toLinearMap =
        LinearMap.pi (fun i : ν => (Matrix.toLin' (t : Matrix α α K)).comp (LinearMap.proj i)) := by
      refine LinearMap.ext fun x => funext fun i => funext fun j => ?_
      simp [TK, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
    have hdetK : LinearMap.det (TK t) = Matrix.det (t : Matrix α α K) ^ Fintype.card ν := by
      rw [← LinearMap.det_conj (TK t) (Matrix.ofLinearEquiv K).symm, hpi, LinearMap.det_pi,
        Finset.prod_const, Finset.card_univ, LinearMap.det_toLin']
    ext
    change Matrix.det (LinearMap.toMatrix' (F t)) = _
    rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_restrictScalars, hdetK, map_pow]
    simp
end PositivityTheory.ThK.LinAct
