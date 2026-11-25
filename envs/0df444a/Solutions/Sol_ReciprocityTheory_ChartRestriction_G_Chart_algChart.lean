-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.algChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:46:43.338072+00:00
-- url     : https://prove2.me/submissions/d3999644-2e03-4d36-9fab-f242fa3bab08

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Lemmata_FirstBlockLemmaK_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_isUnit_of_aug
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_nil_of_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_trunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_comp_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetZero_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_etale_exists
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_etale_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_nil


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
variable {R : Type} [CommRing R]
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution [IsLocalRing R] (B : Type) [CommRing B] [Algebra R B] [Algebra.Smooth R B] (eps : B →ₐ[R] R) :
    ∃ (n : ℕ) (π : ∀ m : ℕ, B →ₐ[R] JetR R (Fin n) m),
      (∀ m, (jetTruncR R (Fin n) m).comp (π (m + 1)) = π m) ∧
      (∀ m, (jetZeroR R (Fin n) m).comp (π m) = (Algebra.ofId R _).comp eps) ∧
      ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) (m : ℕ), (RingHom.ker aug) ^ (m + 1) = ⊥ →
        ∀ φ : B →ₐ[R] A, aug.comp φ = eps →
          ∃! ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin n) m ∧ ψ.comp (π m) = φ := by
  let q : Ideal B := (IsLocalRing.maximalIdeal R).comap eps
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨f, hfq, n, _, hST, hSE⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := q)
  haveI := hST
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin n) R) (Localization.Away f) := inferInstance
  have hf : IsUnit (eps f) := by
    by_contra h
    exact hfq ((IsLocalRing.mem_maximalIdeal _).mpr h)
  let toS : B →ₐ[R] Localization.Away f := IsScalarTower.toAlgHom R B (Localization.Away f)
  let ε' : Localization.Away f →ₐ[R] R := IsLocalization.Away.liftAlgHom f hf
  have hε' : ε'.comp toS = eps := by
    ext b
    exact IsLocalization.Away.lift_eq f hf b
  have locExt : ∀ {A : Type} [CommRing A] [Algebra R A] (φ₁ φ₂ : Localization.Away f →ₐ[R] A),
      φ₁.comp toS = φ₂.comp toS → φ₁ = φ₂ := by
    intro A _ _ φ₁ φ₂ h
    ext s
    exact AlgHom.congr_fun h s
  have hπ : ∀ m : ℕ, ∃ π : Localization.Away f →ₐ[R] JetR R (Fin n) m, (jetAug R (Fin n) m).comp π = ε' ∧
      ∀ j, π (sX R j) = algebraMap R _ (ε' (sX R j)) + zR m j := fun m =>
    etale_exists (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ (fun j => by
      rw [map_add, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, jetAug_zR, add_zero])
  choose π hπaug hπX using hπ
  refine ⟨n, fun m => (π m).comp toS, ?_, ?_, ?_⟩
  · intro m
    rw [← AlgHom.comp_assoc]
    congr 1
    refine etale_ext (n := n) ε' (jetAug R (Fin n) m) (ker_jetAug_nil (Fin n) m) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_trunc]
      exact hπaug (m + 1)
    · exact hπaug m
    · intro j
      rw [AlgHom.comp_apply, hπX, hπX, map_add, AlgHom.commutes]
      rfl
  · intro m
    rw [← hε', ← AlgHom.comp_assoc, ← AlgHom.comp_assoc]
    congr 1
    refine etale_ext (n := n) ε' (jetAug R (Fin n) 0) (ker_jetAug_nil (Fin n) 0) _ _ ?_ ?_ ?_
    · rw [← AlgHom.comp_assoc, jetAug_comp_zero]
      exact hπaug m
    · ext s
      simp
    · intro j
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, AlgHom.comp_apply, jetZero_zR, add_zero]
      rfl
  · intro A _ _ aug m hJ φ hφ
    have hJn := nil_of_pow _ hJ
    have hu : IsUnit (φ f) := isUnit_of_aug aug hJn _ (by rw [← AlgHom.comp_apply, hφ]; exact hf)
    let φ' : Localization.Away f →ₐ[R] A := IsLocalization.Away.liftAlgHom f hu
    have hφ' : φ'.comp toS = φ := by
      ext b
      exact IsLocalization.Away.lift_eq f hu b
    have hφ'aug : aug.comp φ' = ε' := locExt _ _ (by rw [AlgHom.comp_assoc, hφ', hφ, hε'])
    have hmem : ∀ j : Fin n, φ' (sX (S := Localization.Away f) R j) -
        algebraMap R A (ε' (sX (S := Localization.Away f) R j)) ∈ RingHom.ker aug := by
      intro j
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        ← AlgHom.comp_apply, hφ'aug, sub_self]
    let ψ := jetLift R (RingHom.ker aug) hJ
      (fun j : Fin n => φ' (sX (S := Localization.Away f) R j) - algebraMap R A (ε' (sX (S := Localization.Away f) R j))) hmem
    have hψaug : aug.comp ψ = jetAug R (Fin n) m := jet_ext fun j => by
      rw [AlgHom.comp_apply, jetLift_zR, jetAug_zR]; exact hmem j
    have hψπ : ψ.comp (π m) = φ' := by
      refine etale_ext (n := n) ε' aug hJn _ _ ?_ ?_ ?_
      · rw [← AlgHom.comp_assoc, hψaug]
        exact hπaug m
      · exact hφ'aug
      · intro j
        rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes, jetLift_zR, add_sub_cancel]
    refine ⟨ψ, ⟨hψaug, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hψπ, hφ']
    · rintro ψ₂ ⟨_, h2⟩
      rw [← AlgHom.comp_assoc, ← hφ'] at h2
      have h4 : ψ₂.comp (π m) = φ' := locExt _ _ h2
      apply jet_ext
      intro j
      rw [jetLift_zR]
      have := AlgHom.congr_fun h4 (sX R j)
      rw [AlgHom.comp_apply, hπX, map_add, AlgHom.commutes] at this
      rw [← this, add_sub_cancel_left]
end ReciprocityTheory.ChartRestriction.G.Chart
