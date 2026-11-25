-- Prove2me | solution 1 for PositivityTheory.KCo.irr_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:28:06.040505+00:00
-- url     : https://prove2.me/submissions/1dbd081b-66bb-42f3-bd67-9ba1995103bb

import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CoinvariantsFiniteOfSmoothLevi
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibreRepresentationSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_TopOfMap
import Theorems.Thm_PositivityTheory_KCo_top_of_map
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OpenClosedSequences_indSnd_inr
import Theorems.Thm_GlobalTheory_SmGL_IndCoinv_smInd_coinvariants
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_JacquetFiniteLength_two
import Theorems.Thm_GlobalTheory_SmGL_LeviInt_levi_integral_facts
import Theorems.Thm_GlobalTheory_SmGL_exists_open_normalised_subgroup_subset
import Theorems.Thm_GlobalTheory_SmGL_isIrreducible_ofChar
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_deltaHalf
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_comp
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_twist
import Theorems.Thm_GlobalTheory_SmGL_isUnitarisable_ofChar_iff
import Theorems.Thm_GlobalTheory_SplitWeil_Model_secondCountable_and_t2_local_field


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
    (hu : ∀ x, ‖(μ x : ℂ)‖ = 1) {Γ W : Type} [Group Γ] [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Γ × (GL (Fin n) k × GL (Fin t) k)) W) (hτ : IsSmooth (τ.comp (MonoidHom.inr Γ _)))
    (l : W →ₗ[ℂ] ℂ) (hs : Function.Surjective l)
    (hτl : ∀ g p₁ p₂ φ, l (τ (g, p₁, p₂) φ) = (μ (GeneralLinearGroup.det p₂) : ℂ) * l φ)
    (hk : ∀ x, l x = 0 → x ∈ twRel (τ.comp (MonoidHom.inl Γ _)) 1)
    (N : Submodule ℂ (IndSp (two (stdSum (rfl : n + t = n + t)))
      (MonoidHom.comp (τ.comp (MonoidHom.inr _ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom)))
    (hR : twRel ((indSnd (stdSum rfl) τ).comp (MonoidHom.inl _ _)) 1 ≤ N)
    (hN : ∀ h, ∀ f ∈ N, indSnd (stdSum rfl) τ (1, h) f ∈ N) :
    N = ⊤ ∨ N ≤ twRel ((indSnd (stdSum rfl) τ).comp (MonoidHom.inl _ _)) 1 := by
  let e := stdSum (rfl : n + t = n + t)
  obtain ⟨-, -, -, -, -, hcont, hP, -, hPK⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k _ (Fin (n + t)) _ (two e)
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let ρ : Representation ℂ (Levi k (Two (Fin n) (Fin t))) _ :=
    MonoidHom.comp (τ.comp (MonoidHom.inr Γ _)) (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom
  let π₁ := detRep (Fin n) (1 : kˣ →* ℂˣ)
  let π₂ := detRep (Fin t) μ
  let ρD : Representation ℂ (Levi k (Two (Fin n) (Fin t))) (ℂ ⊗[ℂ] ℂ) :=
    (extTensor π₁ π₂).comp (leviTwo k (Fin n) (Fin t)).symm.toMonoidHom
  let q : ρ.IntertwiningMap ρD :=
    { toLinearMap := (TensorProduct.lid ℂ ℂ).symm.toLinearMap ∘ₗ l
      isIntertwining' := fun m => LinearMap.ext fun φ => by
        change (TensorProduct.lid ℂ ℂ).symm (l (τ (1, m false, m true) φ)) =
          extTensor π₁ π₂ (m false, m true) ((TensorProduct.lid ℂ ℂ).symm (l φ))
        rw [hτl]
        simp [π₁, π₂, detRep] }
  have hq : Function.Surjective q := (TensorProduct.lid ℂ ℂ).symm.surjective.comp hs
  have hρ : IsSmooth ρ := isSmooth_comp hτ _ ((continuous_apply false).prodMk (continuous_apply true))
  have hI : (parInd (two e) ρD).IsIrreducible := hB k n t ℂ ℂ π₁ π₂
    ((isSmooth_ofChar_iff _).2 (IsSmoothChar.detChar (by unfold IsSmoothChar; simp))) (isIrreducible_ofChar _)
    ((isUnitarisable_ofChar_iff _).2 fun g => by simp)
    ((isSmooth_ofChar_iff _).2 hμ.detChar) (isIrreducible_ofChar _) ((isUnitarisable_ofChar_iff _).2 fun g => hu _)
  let σ := (twist ρ (deltaHalf k (Two (Fin n) (Fin t)))).comp (leviProj k (two e))
  have hσ : IsSmooth σ := isSmooth_comp (isSmooth_twist hρ (isSmoothChar_deltaHalf k)) _ hcont
  let α : Representation.IntertwiningMap σ ((twist ρD (deltaHalf k (Two (Fin n) (Fin t)))).comp (leviProj k (two e))) :=
    compMap (twistMap q _) _
  let T : Γ → Representation.IntertwiningMap σ σ := fun γ =>
    compMap (twistMap (actFst τ γ) (deltaHalf k (Two (Fin n) (Fin t)))) (leviProj k (two e))
  have hker0 : ∀ x, α x = 0 → x ∈ Submodule.span ℂ {y | ∃ γ z, y = T γ z - z} := by
    intro x hx
    have h0 : l x = 0 := (TensorProduct.lid ℂ ℂ).symm.map_eq_zero_iff.1 hx
    refine (Submodule.span_le (p := Submodule.span ℂ {y | ∃ γ z, y = T γ z - z})).2 ?_ (hk x h0)
    rintro _ ⟨γ, v, rfl⟩
    refine Submodule.subset_span ⟨γ, v, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    rfl
  obtain ⟨-, hker⟩ := GlobalTheory.SmGL.IndCoinv.smInd_coinvariants (GL (Fin (n + t)) k) (parab k (two e)) (KO k _) hP
    GlobalTheory.SplitFlip.isCompact_KO hPK (GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k _) _ _ σ _ hσ α _ T (fun y => hq y) hker0
  let Φ : (parInd (two e) ρ).IntertwiningMap (parInd (two e) ρD) := parIndMap (two e) q
  have hK : ∀ f, Φ f = 0 → f ∈ twRel ((indSnd e τ).comp (MonoidHom.inl _ _)) 1 := fun f hf => by
    refine (Submodule.span_le (p := twRel ((indSnd e τ).comp (MonoidHom.inl _ _)) 1)).2 ?_ (hker f hf)
    rintro _ ⟨γ, z, rfl⟩
    refine Submodule.subset_span ⟨γ, z, ?_⟩
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    congr 1
    refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    show τ (γ, 1) (z.1.1 x) = τ (γ, 1) (z.1.1 (x * 1))
    rw [mul_one]
  let S : Subrepresentation (parInd (two e) ρD) := ⟨N.map Φ.toLinearMap, by
    rintro h _ ⟨f, hf, rfl⟩
    refine ⟨_, hN h f hf, ?_⟩
    rw [indSnd_inr]
    exact Φ.isIntertwining _ _ h f⟩
  rcases hI.eq_bot_or_eq_top S with h | h
  · refine Or.inr fun f hf => hK f ?_
    have : Φ.toLinearMap f ∈ S.toSubmodule := ⟨f, hf, rfl⟩
    rw [h] at this
    exact this
  · exact Or.inl (top_of_map Φ.toLinearMap hK hR (congrArg Subrepresentation.toSubmodule h))
end PositivityTheory.KCo
