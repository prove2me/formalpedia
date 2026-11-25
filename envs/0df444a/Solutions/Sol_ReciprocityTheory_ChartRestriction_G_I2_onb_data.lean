-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.onb_data
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:29:05.592591+00:00
-- url     : https://prove2.me/submissions/82f28513-f59e-4a66-870a-95d588077af1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_LemmaS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_HfEqInner
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_mulc_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_Hf_prj
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_Hf_eq_inner__57cc81a446bf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_prj_inpart

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
theorem _root_.solution (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (σ : E →+* ℂ) (ρ : ℕ)
    (hρ : Module.finrank ℂ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) = ρ)
    (hst : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I)
    (w : Fin ρ → Vsp X.dim) (hw : ∀ s, InPart σ (w s) ∧ w s ∈ Submodule.span ℂ (I : Set (Vsp X.dim)))
    (hon : ∀ s s', Hf (w s) (w s') = if s = s' then 1 else 0) :
    ∃ (N : ℕ) (b : Fin N → Vsp X.dim), N ≤ X.r ∧ ρ ≤ N ∧
      (∀ k (h : k.val < ρ), b k = w ⟨k, h⟩) ∧
      (∀ k, InPart σ (b k)) ∧
      (∀ k, ρ ≤ k.val → ‖b k‖ = 1 ∧ ∀ a ∈ I, Hf (b k) a = 0) ∧
      (∀ x y : Vsp X.dim, InPart σ x → InPart σ y → ∑ k, Hf x (b k) * Hf (b k) y = Hf x y) := by
  classical
  set N := Module.finrank ℂ (VP (dim := X.dim) σ) with hN
  have hw_inner : ∀ s s', inner ℂ (w s) (w s') = if s = s' then (1 : ℂ) else 0 := by
    intro s s'
    rw [← Hf_eq_inner', hon s' s]
    by_cases h : s = s' <;> simp [h, eq_comm]
  have hwo : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]; exact hw_inner
  have hρN : ρ ≤ N := hρ ▸ Submodule.finrank_mono inf_le_right
  have hNr : N ≤ X.r := by
    let f : VP (dim := X.dim) σ →ₗ[ℂ] (Fin (X.dim σ) → ℂ) :=
      { toFun := fun v a => (v : Vsp X.dim) ⟨σ, a⟩
        map_add' := fun x y => by funext a; simp
        map_smul' := fun c x => by funext a; simp }
    have hinj : Function.Injective f := by
      intro v v' h
      apply Subtype.ext
      ext j
      obtain ⟨τ, a⟩ := j
      by_cases hτ : τ = σ
      · subst hτ; exact congrFun h a
      · rw [(v.2 : InPart σ (v : Vsp X.dim)) ⟨τ, a⟩ hτ, (v'.2 : InPart σ (v' : Vsp X.dim)) ⟨τ, a⟩ hτ]
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun] at h1
    have h2 := X.dim_conj σ
    omega
  let vv : Fin N → VP (dim := X.dim) σ := fun k =>
    if h : k.val < ρ then ⟨w ⟨k, h⟩, (hw _).1⟩ else 0
  have hon' : Orthonormal ℂ (Set.domRestrict {k : Fin N | k.val < ρ} vv) := by
    rw [orthonormal_iff_ite]
    rintro ⟨k, hk⟩ ⟨k', hk'⟩
    have hk0 : k.val < ρ := hk
    have hk0' : k'.val < ρ := hk'
    show inner ℂ (vv k) (vv k') = if (⟨k, hk⟩ : {k : Fin N | k.val < ρ}) = ⟨k', hk'⟩ then 1 else 0
    simp only [vv, dif_pos hk0, dif_pos hk0', Submodule.coe_inner, hw_inner]
    simp [Fin.ext_iff, Subtype.ext_iff]
  obtain ⟨bb, hbb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℂ)
    (E := VP (dim := X.dim) σ) (ι := Fin N) (by simp [hN]) hon'
  have hbw : ∀ k (h : k.val < ρ), (bb k : Vsp X.dim) = w ⟨k, h⟩ := by
    intro k h
    rw [hbb k h]
    simp [vv, h]
  refine ⟨N, fun k => (bb k : Vsp X.dim), hNr, hρN, hbw, fun k => (bb k).2, ?_, ?_⟩
  · intro k hk
    constructor
    · exact bb.orthonormal.1 k
    · intro a ha
      rw [Hf_prj ((bb k).2 : InPart σ (bb k : Vsp X.dim)) a]
      have hpa : prj σ a ∈ (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) :=
        ⟨mulc_mem I hst σ a (Submodule.subset_span ha), prj_inpart σ a⟩
      have hspan : Submodule.span ℂ (Set.range w) =
          (Submodule.span ℂ (I : Set (Vsp X.dim)) ⊓ VP σ : Submodule ℂ _) := by
        apply Submodule.eq_of_le_of_finrank_eq
        · rw [Submodule.span_le]; rintro _ ⟨s, rfl⟩; exact ⟨(hw s).2, (hw s).1⟩
        · rw [finrank_span_eq_card hwo.linearIndependent, Fintype.card_fin, hρ]
      rw [← hspan] at hpa
      rw [Hf_eq_inner']
      refine Submodule.span_induction (p := fun z _ => inner ℂ z (bb k : Vsp X.dim) = 0) ?_ ?_ ?_ ?_ hpa
      · rintro _ ⟨s, rfl⟩
        have hs : (⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Fin N).val < ρ := s.2
        have e1 : w s = (bb ⟨s.val, lt_of_lt_of_le s.2 hρN⟩ : Vsp X.dim) := by
          rw [hbw _ hs]
        rw [e1, ← Submodule.coe_inner]
        refine bb.orthonormal.2 ?_
        intro h
        have := congrArg Fin.val h
        simp at this
        omega
      · simp
      · intro x y _ _ hx hy; rw [inner_add_left, hx, hy, add_zero]
      · intro c x _ hx; rw [inner_smul_left, hx, mul_zero]
  · intro x y hx hy
    have := bb.sum_inner_mul_inner (⟨y, hy⟩ : VP (dim := X.dim) σ) ⟨x, hx⟩
    simp only [Submodule.coe_inner] at this
    rw [Hf_eq_inner', ← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Hf_eq_inner', Hf_eq_inner', mul_comm]
end ReciprocityTheory.ChartRestriction.G.I2
