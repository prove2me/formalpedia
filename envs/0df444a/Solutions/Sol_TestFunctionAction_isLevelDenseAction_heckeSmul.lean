-- Prove2me | solution 1 for TestFunctionAction.isLevelDenseAction_heckeSmul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/de2a2671-ae1f-5838-aedd-66cb2ccb43db

import Definitions.Def_RepTheory_LevelDensity
import Definitions.Def_RepTheory_TestFunctionActionHom
import Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_TestFunctionAction_isLevelDenseAction_heckeSmul

set_option autoImplicit false

open MeasureTheory
p2m_open "FLT.SmoothAdmissibleSchurCommutant SchwartzBruhatSpace TestFunctionAction P2MW.S_TestFunctionAction_isLevelDenseAction_heckeSmul.TestFunctionAction"
open scoped Pointwise Topology

namespace TestFunctionAction
p2m_export "TestFunctionAction" "hasOpenStabilizer_of_isSmoothRep heckeSmulHom heckeSmulHom_apply measureCoeff finite_range_of_isLocallyConstant_of_hasCompactSupport heckeSmul_translate_left heckeIdempotent isLocallyConstant_heckeIdempotent hasCompactSupport_heckeIdempotent heckeSmul_indicator_of_forall_smul_eq heckeSmul_heckeIdempotent_of_forall_smul_eq augmentationSubmodule mem_fixedPointsSubmodule_iff heckeSmul_heckeIdempotent_mem_fixedPoints sub_heckeSmul_heckeIdempotent_mem_augmentation"
namespace LevelDense
p2m_open "TestFunctionAction"

section Stab

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def rstab (φ : G → ℂ) : Subgroup G where
  carrier := {t | ∀ g, φ (g * t) = φ g}
  one_mem' g := by rw [mul_one]
  mul_mem' {a b} ha hb g := by rw [← mul_assoc, hb, ha]
  inv_mem' {a} ha g := by
    have h := ha (g * a⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

def lstab (φ : G → ℂ) : Subgroup G where
  carrier := {t | ∀ g, φ (t * g) = φ g}
  one_mem' g := by rw [one_mul]
  mul_mem' {a b} ha hb g := by rw [mul_assoc, ha, hb]
  inv_mem' {a} ha g := by
    have h := ha (a⁻¹ * g)
    rw [mul_inv_cancel_left] at h
    exact h.symm

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem mem_rstab {φ : G → ℂ} {t : G} : t ∈ rstab φ ↔ ∀ g, φ (g * t) = φ g := Iff.rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem mem_lstab {φ : G → ℂ} {t : G} : t ∈ lstab φ ↔ ∀ g, φ (t * g) = φ g := Iff.rfl

theorem exists_nhds_mul_right_mem_iff {F : Set G} (hFc : IsCompact F) (hFo : IsOpen F) :
    ∃ U ∈ 𝓝 (1 : G), ∀ t ∈ U, ∀ g : G, g * t ∈ F ↔ g ∈ F := by
  obtain ⟨W, hW, hFW⟩ := compact_open_separated_mul_right hFc hFo subset_rfl
  refine ⟨W ∩ W⁻¹, Filter.inter_mem hW (inv_mem_nhds_one G hW), fun t ht g => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h' : g * t * t⁻¹ ∈ F * W := Set.mul_mem_mul h (Set.mem_inv.mp ht.2)
    rw [mul_inv_cancel_right] at h'
    exact hFW h'
  · exact hFW (Set.mul_mem_mul h ht.1)

theorem exists_nhds_mul_left_mem_iff {F : Set G} (hFc : IsCompact F) (hFo : IsOpen F) :
    ∃ U ∈ 𝓝 (1 : G), ∀ t ∈ U, ∀ g : G, t * g ∈ F ↔ g ∈ F := by
  obtain ⟨W, hW, hWF⟩ := compact_open_separated_mul_left hFc hFo subset_rfl
  refine ⟨W ∩ W⁻¹, Filter.inter_mem hW (inv_mem_nhds_one G hW), fun t ht g => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h' : t⁻¹ * (t * g) ∈ W * F := Set.mul_mem_mul (Set.mem_inv.mp ht.2) h
    rw [inv_mul_cancel_left] at h'
    exact hWF h'
  · exact hWF (Set.mul_mem_mul ht.1 h)

omit [Group G] [IsTopologicalGroup G] in
theorem isCompact_fiber {φ : G → ℂ} (hφ : φ ∈ testSpace G) {c : ℂ} (hc : c ≠ 0) :
    IsCompact {x | φ x = c} :=
  (isCompact_support_of_mem hφ).of_isClosed_subset (hφ.1.isClosed_fiber c) fun x hx => by
    rw [Set.mem_setOf_eq] at hx
    rw [Function.mem_support, hx]
    exact hc

theorem rstab_mem_nhds_one {φ : G → ℂ} (hφ : φ ∈ testSpace G) :
    (rstab φ : Set G) ∈ 𝓝 (1 : G) := by
  classical
  have hfin : (Set.range φ ∩ {c | c ≠ 0}).Finite :=
    (finite_range_of_isLocallyConstant_of_hasCompactSupport hφ.1 hφ.2).subset
      Set.inter_subset_left
  have key : ∀ c ∈ Set.range φ ∩ {c | c ≠ 0}, ∃ U ∈ 𝓝 (1 : G), ∀ t ∈ U, ∀ g : G,
      g * t ∈ {x | φ x = c} ↔ g ∈ {x | φ x = c} := fun c hc =>
    exists_nhds_mul_right_mem_iff (isCompact_fiber hφ hc.2) (hφ.1.isOpen_fiber c)
  choose! U hU hUF using key
  refine Filter.mem_of_superset ((Filter.biInter_mem hfin).mpr hU) fun t ht => ?_
  rw [SetLike.mem_coe, mem_rstab]
  intro g
  by_cases hg : φ g = 0
  · by_contra hne
    have hc : φ (g * t) ∈ Set.range φ ∩ {c | c ≠ 0} :=
      ⟨⟨g * t, rfl⟩, fun h => hne (h.trans hg.symm)⟩
    have h := (hUF _ hc t (Set.mem_iInter₂.mp ht _ hc) g).mp rfl
    exact hne h.symm
  · have hc : φ g ∈ Set.range φ ∩ {c | c ≠ 0} := ⟨⟨g, rfl⟩, hg⟩
    exact (hUF _ hc t (Set.mem_iInter₂.mp ht _ hc) g).mpr rfl

theorem lstab_mem_nhds_one {φ : G → ℂ} (hφ : φ ∈ testSpace G) :
    (lstab φ : Set G) ∈ 𝓝 (1 : G) := by
  classical
  have hfin : (Set.range φ ∩ {c | c ≠ 0}).Finite :=
    (finite_range_of_isLocallyConstant_of_hasCompactSupport hφ.1 hφ.2).subset
      Set.inter_subset_left
  have key : ∀ c ∈ Set.range φ ∩ {c | c ≠ 0}, ∃ U ∈ 𝓝 (1 : G), ∀ t ∈ U, ∀ g : G,
      t * g ∈ {x | φ x = c} ↔ g ∈ {x | φ x = c} := fun c hc =>
    exists_nhds_mul_left_mem_iff (isCompact_fiber hφ hc.2) (hφ.1.isOpen_fiber c)
  choose! U hU hUF using key
  refine Filter.mem_of_superset ((Filter.biInter_mem hfin).mpr hU) fun t ht => ?_
  rw [SetLike.mem_coe, mem_lstab]
  intro g
  by_cases hg : φ g = 0
  · by_contra hne
    have hc : φ (t * g) ∈ Set.range φ ∩ {c | c ≠ 0} :=
      ⟨⟨t * g, rfl⟩, fun h => hne (h.trans hg.symm)⟩
    have h := (hUF _ hc t (Set.mem_iInter₂.mp ht _ hc) g).mp rfl
    exact hne h.symm
  · have hc : φ g ∈ Set.range φ ∩ {c | c ≠ 0} := ⟨⟨g, rfl⟩, hg⟩
    exact (hUF _ hc t (Set.mem_iInter₂.mp ht _ hc) g).mpr rfl

theorem isOpen_rstab {φ : G → ℂ} (hφ : φ ∈ testSpace G) : IsOpen (rstab φ : Set G) :=
  Subgroup.isOpen_of_mem_nhds _ (rstab_mem_nhds_one hφ)

theorem isOpen_lstab {φ : G → ℂ} (hφ : φ ∈ testSpace G) : IsOpen (lstab φ : Set G) :=
  Subgroup.isOpen_of_mem_nhds _ (lstab_mem_nhds_one hφ)

end Stab

section Translate

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def τ (g : G) (ψ : testSpace G) : testSpace G :=
  ⟨fun x => (ψ : G → ℂ) (g⁻¹ * x),
    mem_testSpace_of (ψ.2.1.comp_continuous (continuous_const.mul continuous_id))
      (by have h__af := ψ.2.2.comp_homeomorph (Homeomorph.mulLeft g⁻¹); simp at h__af; exact h__af)⟩

@[scoped simp] theorem τ_apply (g : G) (ψ : testSpace G) (x : G) :
    (τ g ψ : G → ℂ) x = (ψ : G → ℂ) (g⁻¹ * x) :=
  rfl

theorem τ_coe (g : G) (ψ : testSpace G) : (τ g ψ : G → ℂ) = fun x => (ψ : G → ℂ) (g⁻¹ * x) :=
  rfl

noncomputable def ι (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) : testSpace G :=
  ⟨(K : Set G).indicator fun _ => (1 : ℂ),
    indicator_mem_testSpace ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩ hKc 1⟩

@[scoped simp] theorem ι_apply (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
    (x : G) : (ι K hKc hKo : G → ℂ) x = (K : Set G).indicator (fun _ => (1 : ℂ)) x :=
  rfl

theorem ι_coe (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G)) :
    (ι K hKc hKo : G → ℂ) = (K : Set G).indicator fun _ => (1 : ℂ) :=
  rfl

theorem eq_sum_translate_indicator (K : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (φ : testSpace G)
    (hφ : ∀ k ∈ K, ∀ g : G, (φ : G → ℂ) (g * k) = (φ : G → ℂ) g) :
    ∃ S : Finset (G ⧸ K),
      φ = ∑ q ∈ S, (φ : G → ℂ) q.out • τ q.out (ι K hKc hKo) := by
  classical
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have hfin : ((QuotientGroup.mk : G → G ⧸ K) '' tsupport (φ : G → ℂ)).Finite :=
    (φ.2.2.isCompact.image continuous_quotient_mk').finite_of_discrete
  refine ⟨hfin.toFinset, Subtype.ext (funext fun x => ?_)⟩
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, τ_apply,
    ι_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (QuotientGroup.mk x : G ⧸ K)]
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
    have hmem : ((x * k)⁻¹ * x) ∈ (K : Set G) := by
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
      exact K.inv_mem k.2
    rw [hk, Set.indicator_of_mem hmem, mul_one, hφ k k.2 x]
  · intro q _ hq
    have hnot : q.out⁻¹ * x ∉ (K : Set G) := fun hmem =>
      hq (by rw [← QuotientGroup.out_eq' q]; exact QuotientGroup.eq.mpr hmem)
    rw [Set.indicator_of_notMem hnot, mul_zero]
  · intro hx
    have hx' : x ∉ tsupport (φ : G → ℂ) := fun h => hx (hfin.mem_toFinset.mpr ⟨x, h, rfl⟩)
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
    rw [hk, hφ k k.2 x, image_eq_zero_of_notMem_tsupport hx', zero_mul]

end Translate

section Action

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π) (μ : Measure G) [μ.IsHaarMeasure]

theorem apply_translate (g : G) (ψ : testSpace G) (v : V) :
    heckeSmulHom π hsm μ (τ g ψ) v = π g (heckeSmulHom π hsm μ ψ v) := by
  letI := ModuleAction.ofHom π
  haveI := ModuleAction.smulCommClass_ofHom π
  rw [heckeSmulHom_apply, heckeSmulHom_apply, τ_coe]
  exact heckeSmul_translate_left μ ψ.2.1 ψ.2.2 (hasOpenStabilizer_of_isSmoothRep π hsm v) g

theorem apply_indicator_of_fixed (K : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {u : V} (hu : ∀ k ∈ K, π k u = u) :
    heckeSmulHom π hsm μ (ι K hKc hKo) u = measureCoeff ℂ μ (K : Set G) • u := by
  letI := ModuleAction.ofHom π
  haveI := ModuleAction.smulCommClass_ofHom π
  have h := heckeSmul_indicator_of_forall_smul_eq μ (K := (K : Set G)) (1 : ℂ) (v := u) hu
  rw [mul_one] at h
  rw [heckeSmulHom_apply, ι_coe]
  exact h

theorem fixed_of_left_invariant (K : Subgroup G) (ψ : testSpace G)
    (hψ : ∀ k ∈ K, ∀ x : G, (ψ : G → ℂ) (k * x) = (ψ : G → ℂ) x) (v : V) :
    ∀ k ∈ K, π k (heckeSmulHom π hsm μ ψ v) = heckeSmulHom π hsm μ ψ v := by
  intro k hk
  have hτ : τ k ψ = ψ := Subtype.ext (funext fun x => hψ k⁻¹ (K.inv_mem hk) x)
  rw [← apply_translate π hsm μ k ψ v, hτ]

theorem exists_mul_of_invariant (K : Subgroup G) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (φ ψ : testSpace G)
    (hφ : ∀ k ∈ K, ∀ g : G, (φ : G → ℂ) (g * k) = (φ : G → ℂ) g)
    (hψ : ∀ k ∈ K, ∀ x : G, (ψ : G → ℂ) (k * x) = (ψ : G → ℂ) x) :
    ∃ χ : testSpace G,
      heckeSmulHom π hsm μ φ * heckeSmulHom π hsm μ ψ = heckeSmulHom π hsm μ χ := by
  classical
  obtain ⟨S, hS⟩ := eq_sum_translate_indicator K hKc hKo φ hφ
  refine ⟨measureCoeff ℂ μ (K : Set G) • ∑ q ∈ S, (φ : G → ℂ) q.out • τ q.out ψ, ?_⟩
  ext v
  rw [Module.End.mul_apply]
  conv_lhs => rw [hS]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, apply_translate,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [apply_indicator_of_fixed π hsm μ K hKc hKo (fixed_of_left_invariant π hsm μ K ψ hψ v),
    map_smul, smul_comm]

theorem exists_mul (hK₀ : ∃ K₀ : Subgroup G, IsCompact (K₀ : Set G) ∧ IsOpen (K₀ : Set G))
    (φ ψ : testSpace G) :
    ∃ χ : testSpace G,
      heckeSmulHom π hsm μ φ * heckeSmulHom π hsm μ ψ = heckeSmulHom π hsm μ χ := by
  obtain ⟨K₀, hc, ho⟩ := hK₀
  have hro : IsOpen (rstab (φ : G → ℂ) : Set G) := isOpen_rstab φ.2
  have hlo : IsOpen (lstab (ψ : G → ℂ) : Set G) := isOpen_lstab ψ.2
  refine exists_mul_of_invariant π hsm μ (K₀ ⊓ rstab (φ : G → ℂ) ⊓ lstab (ψ : G → ℂ)) ?_ ?_ φ ψ
    (fun k hk g => mem_rstab.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hk).1).2 g)
    (fun k hk x => mem_lstab.mp (Subgroup.mem_inf.mp hk).2 x)
  · rw [Subgroup.coe_inf, Subgroup.coe_inf]
    exact (hc.inter_right (Subgroup.isClosed_of_isOpen _ hro)).inter_right
      (Subgroup.isClosed_of_isOpen _ hlo)
  · rw [Subgroup.coe_inf, Subgroup.coe_inf]
    exact (ho.inter hro).inter hlo

end Action

section Level

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π) (μ : Measure G) [μ.IsHaarMeasure]
variable (K : Subgroup G) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

noncomputable def eK : testSpace G :=
  ⟨heckeIdempotent ℂ μ (K : Set G),
    mem_testSpace_of
      (isLocallyConstant_heckeIdempotent ℂ μ ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩)
      (hasCompactSupport_heckeIdempotent ℂ μ hKc (Subgroup.isClosed_of_isOpen _ hKo))⟩

omit [BorelSpace G] [μ.IsHaarMeasure] in
theorem eK_coe : (eK μ K hKc hKo : G → ℂ) = heckeIdempotent ℂ μ (K : Set G) := rfl

theorem proj_mem (v : V) : heckeSmulHom π hsm μ (eK μ K hKc hKo) v ∈ fixedVectors π K := by
  letI := ModuleAction.ofHom π
  haveI := ModuleAction.smulCommClass_ofHom π
  have h := heckeSmul_heckeIdempotent_mem_fixedPoints (𝕜 := ℂ) μ hKo hKc
    (hasOpenStabilizer_of_isSmoothRep π hsm v)
  rw [mem_fixedVectors]
  intro k hk
  have h' := (mem_fixedPointsSubmodule_iff.mp h) k hk
  rw [heckeSmulHom_apply, eK_coe]
  exact h'

theorem proj_eq_self {w : V} (hw : w ∈ fixedVectors π K) :
    heckeSmulHom π hsm μ (eK μ K hKc hKo) w = w := by
  letI := ModuleAction.ofHom π
  haveI := ModuleAction.smulCommClass_ofHom π
  rw [heckeSmulHom_apply, eK_coe]
  exact heckeSmul_heckeIdempotent_of_forall_smul_eq μ (LevelMeasure.measure_ne_zero μ K hKo)
    (LevelMeasure.measure_ne_top μ K hKc) ((mem_fixedVectors π).mp hw)

theorem functional_proj (ℓ : V →ₗ[ℂ] ℂ) (hℓ : ∀ k ∈ K, ∀ x : V, ℓ (π k x) = ℓ x) (v : V) :
    ℓ (heckeSmulHom π hsm μ (eK μ K hKc hKo) v) = ℓ v := by
  letI := ModuleAction.ofHom π
  haveI := ModuleAction.smulCommClass_ofHom π
  have hmem := sub_heckeSmul_heckeIdempotent_mem_augmentation (𝕜 := ℂ) μ hKo hKc
    (LevelMeasure.measure_ne_zero μ K hKo) (hasOpenStabilizer_of_isSmoothRep π hsm v)
  have hker : (augmentationSubmodule ℂ K : Submodule ℂ V) ≤ LinearMap.ker ℓ := by
    show Submodule.span ℂ _ ≤ _
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, hk, u, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
    exact hℓ k hk u
  have h := hker hmem
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h
  rw [heckeSmulHom_apply, eK_coe]
  exact h.symm

noncomputable def corner : testSpace G →ₗ[ℂ] Module.End ℂ (fixedVectors π K) where
  toFun φ := LinearMap.codRestrict (fixedVectors π K)
      ((heckeSmulHom π hsm μ (eK μ K hKc hKo) * heckeSmulHom π hsm μ φ) ∘ₗ
        (fixedVectors π K).subtype)
      (fun w => proj_mem π hsm μ K hKc hKo _)
  map_add' φ ψ := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp only [map_add, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Module.End.mul_apply, LinearMap.add_apply, Submodule.coe_add]
  map_smul' c φ := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp only [map_smul, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      Module.End.mul_apply, LinearMap.smul_apply, Submodule.coe_smul, RingHom.id_apply]

theorem corner_apply_coe (φ : testSpace G) (w : fixedVectors π K) :
    ((corner π hsm μ K hKc hKo φ w : fixedVectors π K) : V) =
      heckeSmulHom π hsm μ (eK μ K hKc hKo) (heckeSmulHom π hsm μ φ w) :=
  rfl

noncomputable def cornerMonoid : Submonoid (Module.End ℂ (fixedVectors π K)) where
  carrier := Set.range (corner π hsm μ K hKc hKo)
  one_mem' := by
    refine ⟨eK μ K hKc hKo, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [corner_apply_coe, proj_eq_self π hsm μ K hKc hKo w.2, proj_eq_self π hsm μ K hKc hKo w.2]
    rfl
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    obtain ⟨χ₁, h₁⟩ := exists_mul π hsm μ ⟨K, hKc, hKo⟩ (eK μ K hKc hKo) ψ
    obtain ⟨χ, h⟩ := exists_mul π hsm μ ⟨K, hKc, hKo⟩ φ χ₁
    refine ⟨χ, LinearMap.ext fun w => Subtype.ext ?_⟩
    rw [corner_apply_coe, ← h, Module.End.mul_apply, ← h₁, Module.End.mul_apply]
    rfl

noncomputable def cornerRep :
    Representation ℂ (cornerMonoid π hsm μ K hKc hKo) (fixedVectors π K) :=
  (cornerMonoid π hsm μ K hKc hKo).subtype

theorem exists_corner_apply_eq (hirr : IsIrreducibleRep π) {w : fixedVectors π K} (hw : w ≠ 0)
    (w' : fixedVectors π K) : ∃ φ : testSpace G, corner π hsm μ K hKc hKo φ w = w' := by
  let ev : testSpace G →ₗ[ℂ] V := LinearMap.applyₗ (w : V) ∘ₗ heckeSmulHom π hsm μ
  have hev : ∀ φ : testSpace G, ev φ = heckeSmulHom π hsm μ φ w := fun φ => rfl
  have hstab : ∀ (g : G) (v : V), v ∈ LinearMap.range ev → π g v ∈ LinearMap.range ev := by
    rintro g _ ⟨φ, rfl⟩
    exact ⟨τ g φ, by rw [hev, hev, apply_translate]⟩
  have hne : LinearMap.range ev ≠ ⊥ := by
    intro h
    have h0 : ev (eK μ K hKc hKo) = 0 :=
      (Submodule.eq_bot_iff _).mp h _ ⟨eK μ K hKc hKo, rfl⟩
    rw [hev, proj_eq_self π hsm μ K hKc hKo w.2] at h0
    exact hw (Subtype.ext h0)
  have htop : LinearMap.range ev = ⊤ := (hirr.2 _ hstab).resolve_left hne
  have hmem : (w' : V) ∈ LinearMap.range ev := htop ▸ Submodule.mem_top
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨φ, Subtype.ext ?_⟩
  rw [corner_apply_coe, ← hev, hφ, proj_eq_self π hsm μ K hKc hKo w'.2]

theorem isIrreducible_cornerRep (hirr : IsIrreducibleRep π) (hnt : ∃ w : fixedVectors π K, w ≠ 0) :
    (cornerRep π hsm μ K hKc hKo).IsIrreducible := by
  obtain ⟨w₀, hw₀⟩ := hnt
  haveI : Nontrivial (fixedVectors π K) := ⟨⟨w₀, 0, hw₀⟩⟩
  haveI : Nontrivial (Subrepresentation (cornerRep π hsm μ K hKc hKo)) :=
    ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine ⟨fun σ => ?_⟩
  by_cases hσ : σ.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hσ)
  · refine Or.inr (Subrepresentation.toSubmodule_injective ?_)
    obtain ⟨w, hwσ, hw0⟩ := (Submodule.ne_bot_iff _).mp hσ
    refine eq_top_iff.mpr fun w' _ => ?_
    obtain ⟨φ, hφ⟩ := exists_corner_apply_eq π hsm μ K hKc hKo hirr hw0 w'
    rw [← hφ]
    exact σ.apply_mem_toSubmodule ⟨corner π hsm μ K hKc hKo φ, φ, rfl⟩ hwσ

theorem range_corner_eq_top (hirr : IsIrreducibleRep π) (hadm : IsAdmissibleRep π)
    (hnt : ∃ w : fixedVectors π K, w ≠ 0) :
    LinearMap.range (corner π hsm μ K hKc hKo) = ⊤ := by
  haveI : FiniteDimensional ℂ (fixedVectors π K) := hadm K hKc hKo
  haveI := isIrreducible_cornerRep π hsm μ K hKc hKo hirr hnt
  have h := Representation.span_range_eq_top_of_isIrreducible (cornerRep π hsm μ K hKc hKo)
  have hr : Set.range (cornerRep π hsm μ K hKc hKo) =
      (LinearMap.range (corner π hsm μ K hKc hKo) : Set (Module.End ℂ (fixedVectors π K))) := by
    ext f
    constructor
    · rintro ⟨⟨_, φ, rfl⟩, rfl⟩
      exact ⟨φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨⟨corner π hsm μ K hKc hKo φ, φ, rfl⟩, rfl⟩
  rw [hr, Submodule.span_eq] at h
  exact h

theorem isLevelDenseAction (hirr : IsIrreducibleRep π) (hadm : IsAdmissibleRep π) :
    TwistedPairing.IsLevelDenseAction π (heckeSmulHom π hsm μ) := by
  intro K hKc hKo ℓ hℓ x₀ hx₀
  by_cases hnt : ∃ w : fixedVectors π K, w ≠ 0
  · have htop := range_corner_eq_top π hsm μ K hKc hKo hirr hadm hnt
    have hx₀' : x₀ ∈ fixedVectors π K := (mem_fixedVectors π).mpr hx₀
    let R : Module.End ℂ (fixedVectors π K) :=
      (ℓ ∘ₗ (fixedVectors π K).subtype).smulRight ⟨x₀, hx₀'⟩
    have hRw : ∀ w : fixedVectors π K, ((R w : fixedVectors π K) : V) = ℓ (w : V) • x₀ :=
      fun w => rfl
    have hR : R ∈ LinearMap.range (corner π hsm μ K hKc hKo) := htop ▸ Submodule.mem_top
    obtain ⟨φ, hφ⟩ := hR
    obtain ⟨χ₁, h₁⟩ := exists_mul π hsm μ ⟨K, hKc, hKo⟩ φ (eK μ K hKc hKo)
    obtain ⟨χ, h⟩ := exists_mul π hsm μ ⟨K, hKc, hKo⟩ (eK μ K hKc hKo) χ₁
    refine ⟨χ, fun x => ?_⟩
    have hu : heckeSmulHom π hsm μ (eK μ K hKc hKo) x ∈ fixedVectors π K :=
      proj_mem π hsm μ K hKc hKo x
    have key := congrArg
      (fun f : Module.End ℂ (fixedVectors π K) => ((f ⟨_, hu⟩ : fixedVectors π K) : V)) hφ
    rw [corner_apply_coe, hRw] at key
    rw [← h, Module.End.mul_apply, ← h₁, Module.End.mul_apply, key,
      functional_proj π hsm μ K hKc hKo ℓ hℓ x]
  · have hx : x₀ = 0 := by
      by_contra h
      exact hnt ⟨⟨x₀, (mem_fixedVectors π).mpr hx₀⟩, fun h' => h (congrArg Subtype.val h')⟩
    refine ⟨0, fun x => ?_⟩
    rw [map_zero, LinearMap.zero_apply, hx, smul_zero]

end Level

end TestFunctionAction.LevelDense
p2m_reactivate "P2MW.S_TestFunctionAction_isLevelDenseAction_heckeSmul.TestFunctionAction P2MW.S_TestFunctionAction_isLevelDenseAction_heckeSmul.TestFunctionAction.LevelDense"
p2m_reactivate "P2MW.S_TestFunctionAction_isLevelDenseAction_heckeSmul.TestFunctionAction"

theorem solution
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π)
    (μ : Measure G) [μ.IsHaarMeasure]
    (hirr : IsIrreducibleRep π) (hadm : IsAdmissibleRep π) :
    TwistedPairing.IsLevelDenseAction π (heckeSmulHom π hsm μ) :=
  TestFunctionAction.LevelDense.isLevelDenseAction π hsm μ hirr hadm

end S_TestFunctionAction_isLevelDenseAction_heckeSmul
end P2MW
export P2MW.S_TestFunctionAction_isLevelDenseAction_heckeSmul (solution)
