-- Prove2me | solution 1 for PositivityTheory.KCo.irr_ind
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:57:15.278864+00:00
-- url     : https://prove2.me/submissions/fb7a37f6-45d0-4ce4-ad75-6d02f7ebaa88

import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_TopOfMap
import Theorems.Thm_PositivityTheory_KCo_irr_gen
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_absPow_add
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_of_isUnram
import Theorems.Thm_GlobalTheory_SmGL_isUnram_absPow
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitFlip_IsCoeffRing_inv
import Theorems.Thm_GlobalTheory_SplitFlip_IsRightTranslationIsometric_inv
import Theorems.Thm_GlobalTheory_T_fibre_representation_smooth
import Theorems.Thm_PositivityTheory_KCo_exists_fun


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.KCo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
open scoped TensorProduct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace PositivityTheory.KCo
theorem _root_.solution (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (n t : ℕ) {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ)
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp ((fibRep (Fin n) (Fin n) (Fin t) μ n).comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n) (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) (fibRep (Fin n) (Fin n) (Fin t) μ n)).comp (MonoidHom.inl _ _)) 1 := by
  let τ := fibRep (Fin n) (Fin n) (Fin t) μ n
  let ξ : GL (Fin n) k →* ℂˣ := detChar (Fin n) (μ⁻¹ * absPow k (((Fintype.card (Fin n) : ℂ) + Fintype.card (Fin t)) / 2))
  have hξ : IsSmoothChar ξ := (hμ.inv.mul (isSmoothChar_of_isUnram (isUnram_absPow k _))).detChar
  obtain ⟨l, hs, hl, hk⟩ := exists_fun (k := k) (κ := n) (Fintype.card_fin n).symm hξ
  have hτ : IsSmooth (τ.comp (MonoidHom.inr _ _)) := GlobalTheory.T.fibre_representation_smooth k _ _ _ μ hμ n
  have hτl : ∀ g p₁ p₂ φ, l (τ (g, p₁, p₂) φ) = (μ (GeneralLinearGroup.det p₂) : ℂ) * l φ := by
    intro g p₁ p₂ φ
    change l ((fibChar (Fin n) (Fin n) (Fin t) μ (g, p₁, p₂) : ℂ) • fibBase (Fin n) (Fin n) n (g, p₁) φ) = _
    rw [map_smul, hl, smul_eq_mul, ← mul_assoc]
    congr 1
    have a1 : ∀ (x : kˣ) (s s' s'' : ℂ), s + s' + s'' = 0 → absPow k s x * absPow k s' x * absPow k s'' x = 1 := fun x s s' s'' h => by
      rw [← MonoidHom.mul_apply, ← absPow_add, ← MonoidHom.mul_apply, ← absPow_add, h]
      exact Units.ext (by simp [val_absPow])
    have b1 := congrArg Units.val (a1 (GeneralLinearGroup.det p₁) (-(n : ℂ) / 2) (-(t : ℂ) / 2) (((n : ℂ) + t) / 2) (by ring))
    have b2 := congrArg Units.val (a1 (GeneralLinearGroup.det p₂) (-(n : ℂ) / 2) ((n : ℂ) / 2) 0 (by ring))
    simp only [fibChar, ξ, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, detChar_apply,
      Units.val_mul, MonoidHom.inv_apply, Fintype.card_fin, Units.val_inv_eq_inv_val, Units.val_one, val_absPow, Complex.cpow_zero,
      mul_one] at b1 b2 ⊢
    have n1 := (μ (GeneralLinearGroup.det g)).ne_zero
    have n2 := (μ (GeneralLinearGroup.det p₁)).ne_zero
    have n3 := (absPow k (((n : ℂ) + t) / 2) (GeneralLinearGroup.det g)).ne_zero
    rw [val_absPow] at n3
    simp only [neg_div] at b1 b2
    field_simp
    linear_combination (exp := 1) ((nabs k (GeneralLinearGroup.det p₂) : ℂ) ^ (-((n : ℂ) / 2)) *
      (nabs k (GeneralLinearGroup.det p₂) : ℂ) ^ ((n : ℂ) / 2)) * b1 + b2
  refine irr_gen hB n t hμ hu τ hτ l hs hτl (fun x h0 => ?_) N hR hN
  refine (Submodule.span_le (p := twRel (τ.comp (MonoidHom.inl _ _)) 1)).2 ?_ (hk x h0)
  rintro _ ⟨γ, v, rfl⟩
  have e1 : τ (γ, 1) v = (ξ γ : ℂ) • rightRep (Fin n) (Fin n) n γ v := by
    change (fibChar (Fin n) (Fin n) (Fin t) μ (γ, 1) : ℂ) • fibBase (Fin n) (Fin n) n (γ, 1) v = _
    congr 1
    simp [fibChar, ξ]
  have h : rightRep (Fin n) (Fin n) n γ v - ((ξ⁻¹ γ : ℂˣ) : ℂ) • v =
      ((ξ⁻¹ γ : ℂˣ) : ℂ) • (τ (γ, 1) v - (((1 : GL (Fin n) k →* ℂˣ) γ : ℂˣ) : ℂ) • v) := by
    rw [e1, MonoidHom.one_apply, Units.val_one, one_smul, smul_sub, smul_smul, MonoidHom.inv_apply, Units.inv_mul, one_smul]
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨γ, v, rfl⟩)
end PositivityTheory.KCo
