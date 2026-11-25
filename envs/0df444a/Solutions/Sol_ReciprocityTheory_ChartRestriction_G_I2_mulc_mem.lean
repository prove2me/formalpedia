-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.mulc_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:44.490334+00:00
-- url     : https://prove2.me/submissions/dd9f128a-1d60-49ce-a84c-a11e5cd5c749

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_emb_sep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim))
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I) (σ : E →+* ℂ) :
    ∀ v ∈ Submodule.span ℂ (I : Set (Vsp dim)), prj σ v ∈ Submodule.span ℂ (I : Set (Vsp dim)) := by
  classical
  set S := Submodule.span ℂ (I : Set (Vsp dim)) with hS

  have hact : ∀ (α : 𝓞 E), ∀ v ∈ S, act α v ∈ S := by
    intro α
    let A : Vsp dim →ₗ[ℂ] Vsp dim :=
      { toFun := act α
        map_add' := fun x y => by ext j; simp [act]; ring
        map_smul' := fun c x => by ext j; simp [act]; ring }
    have hle : S.map A ≤ S := by
      rw [hS, Submodule.map_span]
      apply Submodule.span_le.2
      rintro _ ⟨x, hx, rfl⟩
      exact Submodule.subset_span (hst α x hx)
    intro v hv
    exact hle ⟨v, hv, rfl⟩

  have hα : ∀ τ : E →+* ℂ, ∃ α : 𝓞 E, τ ≠ σ → σ (α : E) ≠ τ (α : E) := by
    intro τ
    by_cases h : τ = σ
    · exact ⟨0, fun h' => (h' h).elim⟩
    · obtain ⟨α, hα⟩ := emb_sep (Ne.symm h)
      exact ⟨α, fun _ => hα⟩
  choose α hα using hα
  let c : (E →+* ℂ) → (E →+* ℂ) → ℂ := fun τ τ' =>
    (τ' (α τ : E) - τ (α τ : E)) * (σ (α τ : E) - τ (α τ : E))⁻¹
  have hstep : ∀ τ, ∀ v ∈ S, mulc (c τ) v ∈ S := by
    intro τ v hv
    have : mulc (c τ) v = (σ (α τ : E) - τ (α τ : E))⁻¹ • (act (α τ) v - (τ (α τ : E)) • v) := by
      ext j; simp [mulc, act, c]; ring
    rw [this]
    exact S.smul_mem _ (S.sub_mem (hact _ v hv) (S.smul_mem _ hv))
  have hprod : ∀ T : Finset (E →+* ℂ), ∀ v ∈ S, mulc (fun τ' => ∏ τ ∈ T, c τ τ') v ∈ S := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro v hv
      have : mulc (fun τ' => ∏ τ ∈ (∅ : Finset (E →+* ℂ)), c τ τ') v = v := by ext j; simp [mulc]
      rw [this]; exact hv
    | insert τ T hτ ih =>
      intro v hv
      have : mulc (fun τ' => ∏ t ∈ insert τ T, c t τ') v = mulc (c τ) (mulc (fun τ' => ∏ t ∈ T, c t τ') v) := by
        ext j; simp [mulc, Finset.prod_insert hτ]; ring
      rw [this]
      exact hstep τ _ (ih v hv)
  intro v hv
  have : prj σ v = mulc (fun τ' => ∏ τ ∈ Finset.univ.erase σ, c τ τ') v := by
    ext j
    simp only [prj, mulc, PiLp.toLp_apply]
    by_cases hj : j.1 = σ
    · rw [if_pos hj, hj, Finset.prod_eq_one, one_mul]
      intro τ hτ
      have hne := hα τ (Finset.ne_of_mem_erase hτ)
      simp only [c]
      exact mul_inv_cancel₀ (sub_ne_zero.2 hne)
    · rw [if_neg hj, Finset.prod_eq_zero (i := j.1) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ _⟩), zero_mul]
      simp [c]
  rw [this]
  exact hprod _ v hv
end ReciprocityTheory.ChartRestriction.G.I2
