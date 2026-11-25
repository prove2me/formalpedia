-- Prove2me | solution 1 for PositivityTheory.ThKH.Evl.exists_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:11:03.075355+00:00
-- url     : https://prove2.me/submissions/5390acbb-dfaf-4d75-baaf-d258e07f99d5

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_GoodCharIsLocallyConstant
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_IntegrablePair
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsEqMulApplyZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsInvariantForm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_DualNumberGraphFiltrationIsotropicOfSkew
import Definitions.Def_Development_WeilBound_CoreStatements_LocalThetaKernels_EvlLoc
import Theorems.Thm_PositivityTheory_ThKH_Evl_schr_mem
import Theorems.Thm_PositivityTheory_ThKH_Evl_t2Space_local_field_bis
import Theorems.Thm_PositivityTheory_ThKH_Evl_exists_subgroup
import Theorems.Thm_PositivityTheory_ThKH_Evl_transl
import Theorems.Thm_PositivityTheory_ThKH_Evl_mem_of_orth
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Implements_comp
import Theorems.Thm_GlobalTheory_CompanionTheory_LagFun_exists_param
import Theorems.Thm_GlobalTheory_WeilM_eq_zero_of_mul_invariant
import Theorems.Thm_GlobalTheory_WeilM_isLocallyConstant_addChar
import Theorems.Thm_GlobalTheory_WeilM_nonarch_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix GlobalTheory.WeilM MeasureTheory
open PositivityTheory PositivityTheory.ThKH PositivityTheory.ThKH.Evl
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Invertible (2 : k)]
  {κ : Type} [Fintype κ] {ψ : AddChar k ℂ}
namespace PositivityTheory.ThKH.Evl
theorem _root_.solution (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (h1 : ψ ≠ 1) (large₂ : Submodule k ((κ → k) × (κ → k)))
    (hiso : ∀ w ∈ large₂, ∀ w' ∈ large₂, w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (hdim : Module.finrank k large₂ = Fintype.card κ) :
    ∃ φ₀ : (κ → k) → ℂ, ∀ l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ, (∀ w ∈ large₂, ∀ φ ∈ SB (κ → k), l (schr ψ w φ) = l φ) → l φ₀ = 0 →
      ∀ φ ∈ SB (κ → k), l φ = 0 := by
  classical
  have := t2Space_local_field_bis (k := k)
  have := nonarch_field k
  have hlc := isLocallyConstant_addChar ψ hc
  have hne0 : ∀ x, ψ x ≠ 0 := fun x h => by simpa [h] using hn x
  obtain ⟨n, j, σ, p, hp, hσ, hj⟩ := GlobalTheory.CompanionTheory.LagFun.exists_param large₂
  obtain ⟨U, hUc, hU⟩ := exists_subgroup (k := k) κ
  obtain ⟨V, -, hV⟩ := exists_subgroup (k := k) (Fin n)
  have cj : Continuous j := j.continuous_on_pi
  have cσ : Continuous σ := σ.continuous_on_pi
  have cp : Continuous p := p.continuous_on_pi
  have hce : Topology.IsClosedEmbedding j := Function.LeftInverse.isClosedEmbedding hp cp cj
  set g : (Fin n → k) → ℂ := fun t => ψ (⅟(2 : k) * (j t ⬝ᵥ σ t)) with hg
  have lg : IsLocallyConstant g := hlc.comp_continuous (continuous_const.mul (cj.dotProduct cσ))
  set χ : (κ → k) → ℂ := (U : Set (κ → k)).indicator (fun _ => (1 : ℂ)) with hχ
  let ext : ((Fin n → k) → ℂ) →ₗ[ℂ] ((κ → k) → ℂ) :=
    { toFun := fun f x => (g (p x))⁻¹ * f (p x) * χ (x - j (p x))
      map_add' := fun a b => by funext x; simp only [Pi.add_apply]; ring
      map_smul' := fun a b => by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have ext_apply : ∀ f x, ext f x = (g (p x))⁻¹ * f (p x) * χ (x - j (p x)) := fun _ _ => rfl
  have ext_j : ∀ f t, g t * ext f (j t) = f t := fun f t => by
    rw [ext_apply, hp, sub_self, hχ, Set.indicator_of_mem U.zero_mem, mul_one, mul_inv_cancel_left₀ (hne0 _)]
  have ext_mem : ∀ f ∈ SB (Fin n → k), ext f ∈ SB (κ → k) := fun f hf => by
    refine ⟨(((lg.comp fun z => z⁻¹).comp_continuous cp).mul (hf.1.comp_continuous cp)).mul
      (hU.1.comp_continuous (continuous_id.sub (cj.comp cp))), ?_⟩
    refine HasCompactSupport.intro ((hf.2.prod hUc).image
      (f := fun q : (Fin n → k) × (κ → k) => j q.1 + q.2) ((cj.comp continuous_fst).add continuous_snd)) fun x hx => ?_
    by_contra h
    rw [ext_apply] at h
    have h2 := mul_ne_zero_iff.1 h
    have h3 : x - j (p x) ∈ U := by
      by_contra h4
      exact h2.2 (Set.indicator_of_notMem h4 _)
    exact hx ⟨(p x, x - j (p x)), ⟨subset_tsupport _ (mul_ne_zero_iff.1 h2.1).2, h3⟩, by simp⟩
  have res_mem : ∀ φ ∈ SB (κ → k), (fun t => g t * φ (j t)) ∈ SB (Fin n → k) := fun φ hφ =>
    ⟨lg.mul (hφ.1.comp_continuous cj), (hφ.2.comp_isClosedEmbedding hce).mul_left⟩
  refine ⟨ext ((V : Set (Fin n → k)).indicator fun _ => 1), fun l hl h0 => ?_⟩
  have van : ∀ φ ∈ SB (κ → k), (∀ t, φ (j t) = 0) → l φ = 0 := fun φ hφ hz => by
    refine eq_zero_of_mul_invariant l {f | ∃ y, (0, y) ∈ large₂ ∧ f = fun x => ψ (x ⬝ᵥ y)} ?_ ?_ hφ ?_
    · rintro _ ⟨y, -, rfl⟩
      exact hlc.comp_continuous (continuous_id.dotProduct continuous_const)
    · rintro _ ⟨y, hy, rfl⟩ φ' hφ'
      rw [← hl _ hy φ' hφ']
      congr 1
      funext x
      simp [schr]
    · intro x hx
      have hx' : x - j (p x) ≠ 0 := fun h => hx (by rw [sub_eq_zero.1 h]; exact hz _)
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hx'
      have hi' : (x - j (p x)) i ≠ 0 := hi
      obtain ⟨s, hs⟩ := DFunLike.ne_iff.1 h1
      let f : (κ → k) →ₗ[k] k := (s / (x - j (p x)) i) • (LinearMap.proj i ∘ₗ (LinearMap.id - j ∘ₗ p))
      have hf : ∀ z, z ⬝ᵥ (fun a => f (Pi.single a 1)) = f z := fun z => by
        rw [LinearMap.pi_apply_eq_sum_univ f z, dotProduct]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [smul_eq_mul]
        congr 2
        funext b
        simp [Pi.single_apply, eq_comm]
      refine ⟨_, ⟨fun a => f (Pi.single a 1), mem_of_orth large₂ hiso hdim _ fun w hw => ?_, rfl⟩, ?_⟩
      · obtain ⟨t, ht⟩ := hj w hw
        rw [hf, ← ht]
        simp [f, hp]
      · have : f x = s := by
          show (s / (x - j (p x)) i) * (x - j (p x)) i = s
          exact div_mul_cancel₀ _ hi'
        simpa only [hf, this, AddChar.one_apply] using hs
  have key : ∀ φ ∈ SB (κ → k), l φ = l (ext fun t => g t * φ (j t)) := fun φ hφ => by
    rw [← sub_eq_zero, ← map_sub]
    refine van _ (Submodule.sub_mem _ hφ (ext_mem _ (res_mem φ hφ))) fun t => ?_
    refine mul_left_cancel₀ (hne0 (⅟(2 : k) * (j t ⬝ᵥ σ t))) ?_
    have := ext_j (fun t => g t * φ (j t)) t
    rw [Pi.sub_apply, mul_sub, mul_zero, sub_eq_zero]
    exact this.symm
  have hT := transl hc hn h1 V hV (l ∘ₗ ext) (fun t₁ f hf => by
    have e : (fun t => g t * schr ψ (j t₁, σ t₁) (ext f) (j t)) = fun t => f (t + t₁) := by
      funext t
      rw [← ext_j f (t + t₁)]
      have e3 := hiso _ (hσ t) _ (hσ t₁)
      simp only [hg, schr, map_add, ← mul_assoc, ← AddChar.map_add_eq_mul, add_dotProduct, dotProduct_add] at e3 ⊢
      congr 2
      have h2 : ⅟(2 : k) * 2 = 1 := invOf_mul_self _
      linear_combination ⅟(2 : k) * e3 - (j t ⬝ᵥ σ t₁) * h2
    show l (ext _) = l (ext f)
    rw [← e, ← key _ (schr_mem hc _ (ext_mem f hf)), hl _ (hσ t₁) _ (ext_mem f hf)]) h0
  intro φ hφ
  rw [key φ hφ]
  exact hT _ (res_mem φ hφ)
end PositivityTheory.ThKH.Evl
