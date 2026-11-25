-- Prove2me | solution 1 for PositivityTheory.KCo.exists_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:18.930884+00:00
-- url     : https://prove2.me/submissions/0c3c73ab-9a44-42b4-b8d8-70dea36c4b5d

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteTwistedRankQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_WeilBound_CoreStatements_LocallyConstantCoinvariants_LocConstChar
import Theorems.Thm_PositivityTheory_KCo_common_gen
import Theorems.Thm_PositivityTheory_KCo_locConst_char
import Theorems.Thm_GlobalTheory_CompanionTheory_ThetaGLLen_FullRank_Reached_add
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_mul
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans
import Theorems.Thm_GlobalTheory_SplitFlip_CondLE_mul
import Theorems.Thm_GlobalTheory_SplitFlip_IsCoeffRing_inv
import Theorems.Thm_GlobalTheory_SplitFlip_IsRightTranslationIsometric_inv
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous


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
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen GlobalTheory.CompanionTheory.ThetaGLLen.FullRank Matrix Topology
  MeasureTheory
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a : Type} [Fintype a] [DecidableEq a] {κ : ℕ}
namespace PositivityTheory.KCo
theorem _root_.solution (hκ : κ = Fintype.card a) {ξ : GL a k →* ℂˣ} (hξ : IsSmoothChar ξ) :
    ∃ l : SB (RankIn k a a {κ}) →ₗ[ℂ] ℂ, Function.Surjective l ∧
      (∀ (g p : GL a k) φ, l (fibBase a a κ (g, p) φ) = (ξ p : ℂ) * ((ξ g)⁻¹ : ℂˣ) * l φ) ∧
      ∀ φ, l φ = 0 → φ ∈ twRel (rightRep (k := k) a a κ) ξ⁻¹ := by
  borelize k
  let μ : Measure (GL a k) := GlobalTheory.SplitFlip.haarVol (KO k a)
  have hc := (locConst_char hξ).continuous
  have hint : ∀ φ : SB (RankIn k a a {κ}), Integrable (fun g => φ.1 (rankHomeo hκ g) * (ξ g : ℂ)) μ := fun φ =>
    ((φ.2.1.continuous.comp (rankHomeo hκ).continuous).mul hc).integrable_of_hasCompactSupport
      (φ.2.2.comp_homeomorph (rankHomeo hκ)).mul_right
  let l : SB (RankIn k a a {κ}) →ₗ[ℂ] ℂ :=
    { toFun := fun φ => ∫ g, φ.1 (rankHomeo hκ g) * (ξ g : ℂ) ∂μ
      map_add' := fun φ ψ => by
        rw [← integral_add (hint φ) (hint ψ)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => add_mul _ _ _)
      map_smul' := fun c φ => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun g => mul_assoc _ _ _) }
  have hl : ∀ (g p : GL a k) φ, l (fibBase a a κ (g, p) φ) = (ξ p : ℂ) * ((ξ g)⁻¹ : ℂˣ) * l φ := by
    intro g p φ
    have h1 := integral_mul_left_eq_self (μ := μ) (fun y => φ.1 (rankHomeo hκ y) * (ξ y : ℂ)) p⁻¹
    have h2 := integral_mul_right_eq_self (μ := μ) (fun y => φ.1 (rankHomeo hκ (y * 1)) * (ξ y : ℂ)) g
    have h3 := integral_mul_left_eq_self (μ := μ) (fun y => φ.1 (rankHomeo hκ (y * g)) * (ξ (y * g) : ℂ)) p⁻¹
    simp only [mul_one] at h2
    change ∫ y, _ ∂μ = _ * ∫ y, φ.1 (rankHomeo hκ y) * (ξ y : ℂ) ∂μ
    rw [← h2, ← h3, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e : (fibBase a a κ (g, p) φ).1 (rankHomeo hκ y) = φ.1 (rankHomeo hκ (p⁻¹ * y * g)) := congrArg φ.1 (Subtype.ext rfl)
    simp only [e, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hK : IsClopen (KO k a : Set (GL a k)) := ⟨Subgroup.isClosed_of_isOpen _ GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isOpen_KO⟩
  let f : GL a k → ℂ := fun g => (KO k a : Set (GL a k)).indicator 1 g * ((ξ⁻¹ g : ℂˣ) : ℂ)
  have hf : f ∈ SB (GL a k) := ⟨(LocallyConstant.charFn ℂ hK).2.mul (locConst_char hξ.inv),
    HasCompactSupport.mul_right (HasCompactSupport.intro GlobalTheory.SplitFlip.isCompact_KO fun x hx => Set.indicator_of_notMem hx _)⟩
  let φ₀ : SB (RankIn k a a {κ}) := ⟨f ∘ (rankHomeo hκ).symm, hf.1.comp_continuous (rankHomeo hκ).symm.continuous,
    hf.2.comp_homeomorph _⟩
  have h0 : l φ₀ ≠ 0 := by
    have e : l φ₀ = ∫ g, (KO k a : Set (GL a k)).indicator (fun _ => (1 : ℂ)) g ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only [φ₀, f, Function.comp, Homeomorph.symm_apply_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
      rw [mul_assoc, inv_mul_cancel₀ (ξ g).ne_zero, mul_one]
      rfl
    rw [e, integral_indicator hK.isOpen.measurableSet, setIntegral_const]
    have := (ENNReal.toReal_pos (hK.isOpen.measure_pos μ ⟨1, one_mem _⟩).ne' GlobalTheory.SplitFlip.isCompact_KO.measure_lt_top.ne).ne'
    simpa [Measure.real] using this
  have key : ∀ t w, w ∈ Submodule.span ℂ (Set.range fun g : GL a k => rightRep (k := k) a a κ g t) →
      ∃ s : ℂ, w - s • t ∈ twRel (rightRep (k := k) a a κ) ξ⁻¹ ∧ l w = s * l t := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨g, t, rfl⟩, (hl g 1 t).trans (by simp)⟩
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, e⟩ := hx
      obtain ⟨u, hu, e'⟩ := hy
      exact ⟨s + u, by convert add_mem hs hu using 1; rw [add_smul]; abel, by rw [map_add, e, e', add_mul]⟩
    | smul c x _ hx =>
      obtain ⟨s, hs, e⟩ := hx
      exact ⟨c * s, by convert Submodule.smul_mem _ c hs using 1; rw [smul_sub, smul_smul],
        by rw [map_smul, e, smul_eq_mul, mul_assoc]⟩
  refine ⟨l, fun z => ⟨(z / l φ₀) • φ₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h0]⟩, hl, fun φ hφ => ?_⟩
  obtain ⟨t, h1, h2⟩ := common_gen hκ φ φ₀
  obtain ⟨s, hs, e⟩ := key t φ h1
  obtain ⟨s₀, -, e₀⟩ := key t φ₀ h2
  have ht : l t ≠ 0 := fun h => h0 (by rw [e₀, h, mul_zero])
  rw [(mul_eq_zero.1 (e.symm.trans hφ)).resolve_right ht, zero_smul, sub_zero] at hs
  exact hs
end PositivityTheory.KCo
