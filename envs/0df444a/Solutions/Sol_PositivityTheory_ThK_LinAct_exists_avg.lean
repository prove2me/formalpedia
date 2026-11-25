-- Prove2me | solution 1 for PositivityTheory.ThK.LinAct.exists_avg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:48.275468+00:00
-- url     : https://prove2.me/submissions/d0b5a0ef-14ec-4c56-88d5-b81c912fd7a6

import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_LinearActInt
import Theorems.Thm_PositivityTheory_ThK_LinAct_norm_char
import Theorems.Thm_PositivityTheory_ThK_LinAct_schr_add
import Theorems.Thm_PositivityTheory_ThK_LinAct_schr_comm
import Theorems.Thm_PositivityTheory_ThK_LinAct_exists_section
import Theorems.Thm_PositivityTheory_ThK_LinAct_coeff_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_comp
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous
import Theorems.Thm_GlobalTheory_SplitWeil_secondCountable
import Theorems.Thm_GlobalTheory_WeilM_integral_comp_mulVec
import Theorems.Thm_PositivityTheory_ThKH_Evl_cyc
import Theorems.Thm_PositivityTheory_ThKH_Evl_exists_subgroup
import Theorems.Thm_PositivityTheory_ThKH_Evl_schr_mem
import Theorems.Thm_PositivityTheory_ThKH_Evl_t2Space_local_field_bis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory ValuativeRel Topology Filter PositivityTheory.ThKH.Evl
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.LinAct
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ ι : Type} [Fintype κ] [Fintype ι] {ψ : AddChar k ℂ}
namespace PositivityTheory.ThK.LinAct
theorem _root_.solution [DecidableEq ι] (hc : Continuous ψ) (h1 : ψ ≠ 1) (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ)
    (l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ) (hne : ∃ φ ∈ SB (κ → k), l φ ≠ 0)
    (X : (ι → k) →ₗ[k] (κ → k) × (κ → k)) (hX : ∀ x x', (X x).1 ⬝ᵥ (X x').2 = (X x').1 ⬝ᵥ (X x).2)
    (hXL : ∀ x, X x ∈ large₂ → x = 0) :
    ∃ L : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∃ φ ∈ SB (κ → k), L φ ≠ 0) ∧
      (∀ x, ∀ φ ∈ SB (κ → k), L (schr ψ (X x) φ) = L φ) ∧
      (∀ a ∈ large₂, (∀ x, (X x).1 ⬝ᵥ a.2 = a.1 ⬝ᵥ (X x).2) → ∀ φ ∈ SB (κ → k), L (schr ψ a φ) = L φ) ∧
      ∀ (T : Module.End ℂ ((κ → k) → ℂ)) (g : GL ι k) (a : ℂ), (∀ φ ∈ SB (κ → k), T φ ∈ SB (κ → k)) →
        (∀ x, ∀ φ ∈ SB (κ → k), T (schr ψ (X x) φ) = schr ψ (X (g.val *ᵥ x)) (T φ)) →
        (∀ φ ∈ SB (κ → k), l (T φ) = a * l φ) →
        ∀ φ ∈ SB (κ → k), L (T φ) = ((distribHaarChar k (GeneralLinearGroup.det g) : ℝ) : ℂ) * a * L φ := by
  have := t2Space_local_field_bis (k := k)
  borelize k
  have := GlobalTheory.SplitWeil.secondCountable k
  obtain ⟨S, hSL, hXS⟩ := exists_section large₂ hiso hdim X hXL
  have hS : ∀ y, ∀ φ ∈ SB (κ → k), l (schr ψ (S y) φ) = l φ := fun y => hl _ (hSL y)
  have hF := fun φ hφ => coeff_mem hc h1 l X S hX hS hXS (φ := φ) hφ
  set μ : Measure (ι → k) := Measure.pi fun _ => (Measure.addHaar : Measure k) with hμ
  have hint : ∀ f ∈ SB (ι → k), Integrable f μ := fun f hf => hf.1.continuous.integrable_of_hasCompactSupport hf.2
  let I₀ : SB (ι → k) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f.1 x ∂μ
      map_add' := fun a b => integral_add (hint _ a.2) (hint _ b.2)
      map_smul' := fun c a => integral_smul c a.1 }
  obtain ⟨I, hI⟩ := I₀.exists_extend
  have hI' : ∀ f ∈ SB (ι → k), I f = ∫ x, f x ∂μ := fun f hf => LinearMap.congr_fun hI ⟨f, hf⟩
  let P : ((κ → k) → ℂ) →ₗ[ℂ] ((ι → k) → ℂ) :=
    { toFun := fun φ x => l (schr ψ (X x) φ)
      map_add' := fun a b => funext fun x => by
        rw [Pi.add_apply, ← map_add]; congr 1; funext z; simp [schr, mul_add]
      map_smul' := fun c a => funext fun x => by
        rw [RingHom.id_apply, Pi.smul_apply, ← map_smul]; congr 1; funext z; simp [schr, mul_left_comm] }
  have hL : ∀ φ ∈ SB (κ → k), (I ∘ₗ P) φ = ∫ x, l (schr ψ (X x) φ) ∂μ := fun φ hφ => hI' _ (hF φ hφ)
  refine ⟨I ∘ₗ P, ?_, fun x φ hφ => ?_, fun a ha h φ hφ => ?_, fun T g a hT hg ha φ hφ => ?_⟩
  · by_contra hcon
    push Not at hcon
    obtain ⟨φ, hφ, h0⟩ := hne
    have hz := cyc hc (norm_char hc) h1 (hF φ hφ) (fun h => h0 (by
      have e0 : schr ψ 0 φ = φ := by funext z; simp [schr]
      simpa [e0] using congrFun h 0)) I fun w => by
      have e := hcon _ (schr_mem hc (S w.2) (schr_mem hc (X w.1) hφ))
      have e2 : schr ψ w (fun x => l (schr ψ (X x) φ)) =
          ψ (⅟(2 : k) * (w.1 ⬝ᵥ w.2)) • P (schr ψ (S w.2) (schr ψ (X w.1) φ)) := by
        funext x
        show _ = ψ _ * l (schr ψ (X x) (schr ψ (S w.2) (schr ψ (X w.1) φ)))
        rw [schr_comm, map_smul, hS _ _ (schr_mem hc _ (schr_mem hc _ hφ)), hXS, schr_add (hX _ _), ← map_add, schr,
          AddChar.map_add_eq_mul, smul_eq_mul]
        ring
      rw [e2, map_smul]
      exact smul_eq_zero_of_right _ e
    obtain ⟨U, -, hU⟩ := exists_subgroup (k := k) ι
    have h2 := hz _ hU
    rw [hI' _ hU] at h2
    have h3 := congrArg Complex.re h2
    rw [← RCLike.re_to_complex, ← integral_re (hint _ hU)] at h3
    refine ne_of_gt ?_ h3
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (RCLike.continuous_re.comp hU.1.continuous) (hU.2.comp_left (g := RCLike.re) (map_zero _)) (fun t => ?_) ?_
    · by_cases ht : t ∈ U <;> simp [ht]
    · simp [U.zero_mem]
  · rw [hL _ (schr_mem hc _ hφ), hL _ hφ]
    simp only [schr_add (hX _ _), ← map_add]
    exact integral_add_right_eq_self (fun t => l (schr ψ (X t) φ)) x
  · rw [hL _ (schr_mem hc _ hφ), hL _ hφ]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show l _ = l _
    rw [schr_comm, h, sub_self, AddChar.map_zero_eq_one, one_smul, hl a ha _ (schr_mem hc _ hφ)]
  · rw [hL _ (hT _ hφ), hL _ hφ, ← integral_comp_mulVec _ g, mul_assoc, ← integral_const_mul a]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show l _ = _
    rw [← hg x φ hφ, ha _ (schr_mem hc _ hφ)]
end PositivityTheory.ThK.LinAct
