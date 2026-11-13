-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P20.crossedModulesAndInternalCategories
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-13T02:47:03.172941+00:00
-- url     : https://prove2.me/submissions/40a2b3f9-5fd2-41bf-9753-b172462fe49e

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P20
import Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_internalGroup_sourceTargetKer_commute
import Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_splitCoordinates_mulEquiv
import Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P20_internalGroup_composition_formula
import Mathlib.Tactic.Group
set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intake100.P20


open CategoryTheory

open scoped TensorProduct

universe u v w z

/-- PDF pp. 9–12: BOTH explicit constructions and reconstruction compatibility.
The forward category has s(c,g)=g, t(c,g)=boundary(c)g, identity(g)=(1,g),
and (d,boundary(c)g) after (c,g) = (dc,g). The reverse crossed module is
the source kernel with restricted target and identity-conjugation action.
The original category is recovered by its computed semidirect coordinates,
including composition as a CONCLUSION of the category/interchange laws.
The original crossed module is recovered by c ↦ (c,1) in the source kernel.
No claim about a category of crossed-module morphisms is silently added. -/
theorem solution :
    (∀ {C : Type u} {G : Type v} [Group C] [Group G]
      (d : C →* G) (r : G →* MulAut C), CrossedModule d r →
      InternalCategoryInGrp (crossedCategoryMaps d r) ∧
      ∃ q : C ≃* (SemidirectProduct.rightHom : SemidirectProduct C G r →* G).ker,
        (∀ c, q c = crossedKernelMap r c) ∧
        (∀ c, (crossedCategoryMaps d r).target (q c).val = d c) ∧
        (∀ g c, (q (r g c)).val =
          (crossedCategoryMaps d r).identity g * (q c).val *
            ((crossedCategoryMaps d r).identity g)⁻¹)) ∧
    (∀ {A : Type u} {O : Type v} [Group A] [Group O]
      (D : CategoryMaps A O) (h : InternalCategoryInGrp D),
      CrossedModule (kernelBoundary D h) (kernelAction D h) ∧
      InternalCategoryInGrp (crossedCategoryMaps (kernelBoundary D h) (kernelAction D h)) ∧
      ∃ q : A ≃* SemidirectProduct (sourceHom D h).ker O (kernelAction D h),
        (∀ a, q a = categoryCoordinates D h a) ∧
        (∀ a, (q a).right = D.source a ∧
          kernelBoundary D h (q a).left * (q a).right = D.target a) ∧
        (∀ x, q (D.identity x) = ⟨1, x⟩) ∧
        (∀ f g, D.target f = D.source g →
          q (D.compose g f) = ⟨(q g).left * (q f).left, (q f).right⟩)) := by
  have forward {C : Type u} {G : Type v} [Group C] [Group G]
      (d : C →* G) (r : G →* MulAut C) (hr : CrossedModule d r) :
      InternalCategoryInGrp (crossedCategoryMaps d r) := by
    have hc : CategoryDiagrams (crossedCategoryMaps d r) := by
      constructor
      · intro x; rfl
      · intro x; simp [crossedCategoryMaps]
      · intro f g hfg; rfl
      · intro f g hfg
        change d f.left * f.right = g.right at hfg
        change d (g.left * f.left) * f.right = d g.left * g.right
        rw [map_mul,← hfg,mul_assoc]
      · intro f; apply SemidirectProduct.ext <;> simp [crossedCategoryMaps]
      · intro f; apply SemidirectProduct.ext <;> simp [crossedCategoryMaps]
      · intro f g k hfg hgk
        apply SemidirectProduct.ext
        · exact (mul_assoc k.left g.left f.left).symm
        · rfl
    refine ⟨hc,rfl,fun _ _ => rfl,?_,?_,rfl,?_,?_,?_⟩
    · simp [crossedCategoryMaps]
    · intro a b
      change d (a.left * r a.right b.left) * (a.right*b.right) =
        (d a.left*a.right)*(d b.left*b.right)
      rw [map_mul,hr.1]
      group
    · intro x y
      apply SemidirectProduct.ext <;> simp [crossedCategoryMaps]
    · apply SemidirectProduct.ext <;> simp [crossedCategoryMaps]
    · intro f g a b hfg hab
      change d f.left * f.right = g.right at hfg
      have he : r g.right b.left = f.left * r f.right b.left * f.left⁻¹ := by
        rw [← hfg,r.map_mul]
        exact hr.2 f.left (r f.right b.left)
      apply SemidirectProduct.ext
      · change (g.left * r g.right b.left) * (f.left * r f.right a.left) =
          (g.left*f.left) * r f.right (b.left*a.left)
        rw [he,map_mul]
        group
      · rfl
  constructor
  · intro C G instC instG d r hr
    refine ⟨forward d r hr,?_⟩
    let q : C ≃* (SemidirectProduct.rightHom : SemidirectProduct C G r →* G).ker :=
      { toFun := crossedKernelMap r
        invFun := fun z => z.val.left
        left_inv := fun _ => rfl
        right_inv := by
          intro z
          apply Subtype.ext
          apply SemidirectProduct.ext
          · rfl
          · exact z.property.symm
        map_mul' := by
          intro c c'
          apply Subtype.ext
          exact (SemidirectProduct.inl : C →* SemidirectProduct C G r).map_mul c c' }
    refine ⟨q,fun _ => rfl,?_,?_⟩
    · intro c
      change d c * 1 = d c
      exact mul_one _
    · intro g c
      change (SemidirectProduct.inl (r g c) : SemidirectProduct C G r) =
        SemidirectProduct.inr g * SemidirectProduct.inl c * (SemidirectProduct.inr g)⁻¹
      simpa only [map_inv] using SemidirectProduct.inl_aut (φ := r) g c
  · intro A O instA instO D h
    have hx : CrossedModule (kernelBoundary D h) (kernelAction D h) := by
      constructor
      · intro x c
        change D.target (D.identity x * c.val * (D.identity x)⁻¹) =
          x * D.target c.val * x⁻¹
        rw [h.target_mul,h.target_mul,h.category.target_identity]
        have hh := (targetHom D h).map_inv (D.identity x)
        change D.target (D.identity x)⁻¹ = (D.target (D.identity x))⁻¹ at hh
        rw [hh,h.category.target_identity]
      · intro c k
        apply Subtype.ext
        change D.identity (D.target c.val) * k.val * (D.identity (D.target c.val))⁻¹ =
          c.val * k.val * c.val⁻¹
        have ht : D.target (c.val⁻¹ * D.identity (D.target c.val)) = 1 := by
          rw [h.target_mul,h.category.target_identity]
          have hh := (targetHom D h).map_inv c.val
          change D.target c.val⁻¹ = (D.target c.val)⁻¹ at hh
          rw [hh,inv_mul_cancel]
        have hk : D.source k.val = 1 := k.property
        have hh := internalGroup_sourceTargetKer_commute D h k.val
          (c.val⁻¹ * D.identity (D.target c.val)) hk ht
        calc
          _ = c.val * ((c.val⁻¹ * D.identity (D.target c.val)) * k.val) *
              (D.identity (D.target c.val))⁻¹ := by group
          _ = c.val * (k.val * (c.val⁻¹ * D.identity (D.target c.val))) *
              (D.identity (D.target c.val))⁻¹ := by rw [← hh]
          _ = _ := by group
    refine ⟨hx,forward _ _ hx,?_⟩
    obtain ⟨q,hq,hqi⟩ := splitCoordinates_mulEquiv (sourceHom D h) (identityHom D h)
      h.category.source_identity
    refine ⟨q,hq,?_,?_,?_⟩
    · intro a
      erw [hq]
      refine ⟨rfl,?_⟩
      change D.target (a * (D.identity (D.source a))⁻¹) * D.source a = D.target a
      rw [h.target_mul]
      have hh := (targetHom D h).map_inv (D.identity (D.source a))
      change D.target (D.identity (D.source a))⁻¹ = (D.target (D.identity (D.source a)))⁻¹ at hh
      rw [hh,h.category.target_identity]
      group
    · intro x
      erw [hq]
      apply SemidirectProduct.ext
      · apply Subtype.ext
        change D.identity x * (D.identity (D.source (D.identity x)))⁻¹ = 1
        rw [h.category.source_identity,mul_inv_cancel]
      · exact h.category.source_identity x
    · intro f g hfg
      erw [hq,hq,hq]
      apply SemidirectProduct.ext
      · apply Subtype.ext
        change D.compose g f * (D.identity (D.source (D.compose g f)))⁻¹ =
          (g * (D.identity (D.source g))⁻¹) * (f * (D.identity (D.source f))⁻¹)
        rw [h.category.source_compose f g hfg,internalGroup_composition_formula D h f g hfg]
        group
      · exact h.category.source_compose f g hfg
