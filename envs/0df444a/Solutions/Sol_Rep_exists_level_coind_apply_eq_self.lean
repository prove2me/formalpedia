-- Prove2me | solution 1 for Rep.exists_level_coind_apply_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/e3243b0c-4103-5894-bf38-a3ab71c44da2

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Rep_exists_level_coind_apply_eq_self

set_option autoImplicit false

universe u

open CategoryTheory

namespace P2mS26U5

open IntermediateField groupCohomology

section levels

variable {G : Type u} [Group G] {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}

theorem exists_isGalois_ge (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F' ∧ IsGalois ℚ F' ∧ F ≤ F' := by
  haveI : Normal ℚ (AlgebraicClosure ℚ) := by
    convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
    rfl
  let L : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ L := normalClosure.is_finiteDimensional ℚ F (AlgebraicClosure ℚ)
  haveI : Normal ℚ L := normalClosure.normal ℚ F (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ L := ⟨⟩
  exact ⟨L, inferInstance, inferInstance, IntermediateField.le_normalClosure F⟩

theorem lc₁ {X : Type*} {f : G → X} (hf : IsLevelConstant₁ r f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ g s : G, r s ∈ F.fixingSubgroup → f (g * s) = f g ∧ f (s * g) = f g := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  haveI := hF₀
  obtain ⟨F, hF, hG, hle⟩ := exists_isGalois_ge F₀
  haveI := hG
  have hN : (F.fixingSubgroup.comap r).Normal := inferInstance
  refine ⟨F, hF, hG, fun g s hs => ⟨h g s (fixingSubgroup_antitone hle hs), ?_⟩⟩
  have hs' : g⁻¹ * s * g ∈ F.fixingSubgroup.comap r := by
    simpa using hN.conj_mem s hs g⁻¹
  have := h g (g⁻¹ * s * g) (fixingSubgroup_antitone hle hs')
  rwa [show g * (g⁻¹ * s * g) = s * g by group] at this

theorem lc₂ {X : Type*} {f : G × G → X} (hf : IsLevelConstant₂ r f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      ∀ g g' s : G, r s ∈ F.fixingSubgroup →
        f (g * s, g') = f (g, g') ∧ f (s * g, g') = f (g, g') ∧
        f (g, g' * s) = f (g, g') ∧ f (g, s * g') = f (g, g') := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  haveI := hF₀
  obtain ⟨F, hF, hG, hle⟩ := exists_isGalois_ge F₀
  haveI := hG
  have hN : (F.fixingSubgroup.comap r).Normal := inferInstance
  refine ⟨F, hF, hG, fun g g' s hs => ?_⟩
  have h1 : r 1 ∈ F₀.fixingSubgroup := by rw [map_one]; exact one_mem _
  have hs₀ : r s ∈ F₀.fixingSubgroup := fixingSubgroup_antitone hle hs
  have hcg : r (g⁻¹ * s * g) ∈ F₀.fixingSubgroup :=
    fixingSubgroup_antitone hle (by simpa using hN.conj_mem s hs g⁻¹)
  have hcg' : r (g'⁻¹ * s * g') ∈ F₀.fixingSubgroup :=
    fixingSubgroup_antitone hle (by simpa using hN.conj_mem s hs g'⁻¹)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using h g g' s 1 hs₀ h1
  · simpa [show g * (g⁻¹ * s * g) = s * g by group] using h g g' (g⁻¹ * s * g) 1 hcg h1
  · simpa using h g g' 1 s h1 hs₀
  · simpa [show g' * (g'⁻¹ * s * g') = s * g' by group] using h g g' 1 (g'⁻¹ * s * g') h1 hcg'

theorem out_coe_eq (U : Subgroup G) (g : G) : ∃ u ∈ U, ((g : G ⧸ U).out : G) = g * u := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  exact ⟨u, u.2, hu⟩

end levels

section smooth

variable {k G : Type u} [CommRing k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} {M : Rep k G}
  (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s, r s ∈ F.fixingSubgroup → M.ρ s m = m)
include hsm

theorem exists_level_forall_of_finite {ι : Type*} [Finite ι] (v : ι → M) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ i s, r s ∈ F.fixingSubgroup → M.ρ s (v i) = v i := by
  choose Fi hFi hfix using fun i => hsm (v i)
  haveI := hFi
  exact ⟨⨆ i, Fi i, finiteDimensional_iSup_of_finite, fun i s hs =>
    hfix i s (fixingSubgroup_antitone (le_iSup Fi i) hs)⟩

theorem exists_level₁ {y : G → M} (hy : IsLevelConstant₁ r y) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      (∀ g s : G, r s ∈ F.fixingSubgroup → y (g * s) = y g ∧ y (s * g) = y g) ∧
      (∀ g s : G, r s ∈ F.fixingSubgroup → M.ρ s (y g) = y g) := by
  obtain ⟨F₁, hF₁, hG₁, h₁⟩ := lc₁ hy
  haveI := hF₁; haveI := hG₁
  let U₁ := F₁.fixingSubgroup.comap r
  haveI : Finite (G ⧸ U₁) := Subgroup.finite_quotient_of_finiteIndex

  obtain ⟨F₂, hF₂, h₂⟩ := exists_level_forall_of_finite hsm (fun a : G ⧸ U₁ => y a.out)
  haveI := hF₂
  obtain ⟨F, hF, hG, hle⟩ := exists_isGalois_ge (F₁ ⊔ F₂)
  refine ⟨F, hF, hG, fun g s hs => h₁ g s (fixingSubgroup_antitone (le_sup_left.trans hle) hs),
    fun g s hs => ?_⟩
  obtain ⟨u, hu, hgu⟩ := out_coe_eq U₁ g
  have hyg : y ((g : G ⧸ U₁).out) = y g := by rw [hgu]; exact (h₁ g u hu).1
  rw [← hyg]
  exact h₂ (g : G ⧸ U₁) s (fixingSubgroup_antitone (le_sup_right.trans hle) hs)

theorem exists_level₂ {x : G × G → M} (hx : IsLevelConstant₂ r x) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ IsGalois ℚ F ∧
      (∀ g g' s : G, r s ∈ F.fixingSubgroup →
        x (g * s, g') = x (g, g') ∧ x (s * g, g') = x (g, g') ∧
        x (g, g' * s) = x (g, g') ∧ x (g, s * g') = x (g, g')) ∧
      (∀ g g' s : G, r s ∈ F.fixingSubgroup → M.ρ s (x (g, g')) = x (g, g')) := by
  obtain ⟨F₁, hF₁, hG₁, h₁⟩ := lc₂ hx
  haveI := hF₁; haveI := hG₁
  let U₁ := F₁.fixingSubgroup.comap r
  haveI : Finite (G ⧸ U₁) := Subgroup.finite_quotient_of_finiteIndex
  obtain ⟨F₂, hF₂, h₂⟩ :=
    exists_level_forall_of_finite hsm (fun p : (G ⧸ U₁) × (G ⧸ U₁) => x (p.1.out, p.2.out))
  haveI := hF₂
  obtain ⟨F, hF, hG, hle⟩ := exists_isGalois_ge (F₁ ⊔ F₂)
  refine ⟨F, hF, hG, fun g g' s hs => h₁ g g' s (fixingSubgroup_antitone (le_sup_left.trans hle) hs),
    fun g g' s hs => ?_⟩
  obtain ⟨u, hu, hgu⟩ := out_coe_eq U₁ g
  obtain ⟨u', hu', hgu'⟩ := out_coe_eq U₁ g'
  have hxg : x ((g : G ⧸ U₁).out, (g' : G ⧸ U₁).out) = x (g, g') := by
    rw [hgu, hgu', (h₁ g _ u hu).1, (h₁ g g' u' hu').2.2.1]
  rw [← hxg]
  exact h₂ ((g : G ⧸ U₁), (g' : G ⧸ U₁)) s (fixingSubgroup_antitone (le_sup_right.trans hle) hs)

end smooth

section qti

variable {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (U : Subgroup G) [U.Normal]

theorem qti_ρ_coe (g : G) (v : M.quotientToInvariants U) :
    (((M.quotientToInvariants U).ρ (g : G ⧸ U) v : M.quotientToInvariants U) : M) = M.ρ g (v : M) :=
  rfl

omit [U.Normal] in
theorem coe_eq_of_mem {g s : G} (hs : s ∈ U) : ((g * s : G) : G ⧸ U) = (g : G ⧸ U) := by
  rw [QuotientGroup.eq]; simpa using U.inv_mem hs

theorem qti_ρ_coe' (g : G) (v : M.quotientToInvariants U) :
    (((M.ρ.quotientToInvariants U) (g : G ⧸ U) v : M.quotientToInvariants U) : M) = M.ρ g (v : M) :=
  rfl

end qti

end P2mS26U5

theorem solution {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G) [S.FiniteIndex]
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, r s ∈ F.fixingSubgroup → N.ρ s n = n)
    (f : Rep.coind S.subtype N) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ u : G, r u ∈ F.fixingSubgroup → (Rep.coind S.subtype N).ρ u f = f := by
  classical
  obtain ⟨F₀, hF₀, hle₀⟩ := hS
  haveI := hF₀
  obtain ⟨F₁, hF₁, hG₁, h01⟩ := P2mS26U5.exists_isGalois_ge F₀
  haveI := hF₁; haveI := hG₁
  have hU₁S : F₁.fixingSubgroup.comap r ≤ S :=
    (Subgroup.comap_mono (IntermediateField.fixingSubgroup_antitone h01)).trans hle₀

  let Q := Quotient (QuotientGroup.rightRel S)
  haveI : Finite Q := Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm
  choose Fv hFv hfix using fun q : Q => hsm ((f : G → N) q.out)
  haveI := hFv
  haveI : FiniteDimensional ℚ (⨆ q, Fv q : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  obtain ⟨F, hF, hG, hle⟩ := P2mS26U5.exists_isGalois_ge (F₁ ⊔ ⨆ q, Fv q)
  haveI := hF; haveI := hG
  refine ⟨F, hF, fun u hu => ?_⟩
  have hN : (F.fixingSubgroup.comap r).Normal := inferInstance
  apply Subtype.ext
  funext x
  show (f : G → N) (x * u) = (f : G → N) x

  set q : Q := Quotient.mk _ x with hq
  have hxt : x * (q.out)⁻¹ ∈ S := by
    have : @Setoid.r _ (QuotientGroup.rightRel S) q.out x := Quotient.mk_out x
    exact QuotientGroup.rightRel_apply.1 this
  have hx : x = (x * (q.out)⁻¹) * q.out := by group

  have hcu : x * u * x⁻¹ ∈ F.fixingSubgroup.comap r := hN.conj_mem u hu x
  have hcuS : x * u * x⁻¹ ∈ S :=
    hU₁S (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle) hcu)
  have htu : q.out * u * (q.out)⁻¹ ∈ F.fixingSubgroup.comap r := hN.conj_mem u hu q.out
  have htuS : q.out * u * (q.out)⁻¹ ∈ S :=
    hU₁S (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle) htu)

  have e1 : (f : G → N) (x * u) = N.ρ ⟨x * u * x⁻¹, hcuS⟩ ((f : G → N) x) := by
    have := f.2 ⟨x * u * x⁻¹, hcuS⟩ x
    rw [Subgroup.coe_subtype] at this
    rw [← this]
    show (f : G → N) (x * u) = (f : G → N) (x * u * x⁻¹ * x)
    rw [inv_mul_cancel_right]

  have e2 : (f : G → N) x = N.ρ ⟨x * (q.out)⁻¹, hxt⟩ ((f : G → N) q.out) := by
    have := f.2 ⟨x * (q.out)⁻¹, hxt⟩ q.out
    rw [← this]
    show (f : G → N) x = (f : G → N) (x * (q.out)⁻¹ * q.out)
    rw [← hx]

  have e3 : N.ρ ⟨q.out * u * (q.out)⁻¹, htuS⟩ ((f : G → N) q.out) = (f : G → N) q.out :=
    hfix q ⟨_, htuS⟩ (IntermediateField.fixingSubgroup_antitone ((le_iSup Fv q).trans (le_sup_right.trans hle)) htu)

  have e4 : (⟨x * u * x⁻¹, hcuS⟩ : S) * ⟨x * (q.out)⁻¹, hxt⟩
      = ⟨x * (q.out)⁻¹, hxt⟩ * ⟨q.out * u * (q.out)⁻¹, htuS⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group
  rw [e1, e2, ← Module.End.mul_apply, ← map_mul, e4, map_mul, Module.End.mul_apply, e3]

end S_Rep_exists_level_coind_apply_eq_self
end P2MW
export P2MW.S_Rep_exists_level_coind_apply_eq_self (solution)
