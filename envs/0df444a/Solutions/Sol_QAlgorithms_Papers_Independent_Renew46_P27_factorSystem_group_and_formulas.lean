-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P27.factorSystem_group_and_formulas
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:27:32.536705+00:00
-- url     : https://prove2.me/submissions/e0dc3feb-a4d6-4e0a-afd2-b5feb4b5987e

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P27
open QAlgorithms.Papers.Independent.Renew46.P27

universe u v

variable {G : Type u} {N : Type v} [Group G] [Group N]

theorem g64j_grp_facts {X : Type*} (grp : Group X) :
    (∀ a b c, grp.mul (grp.mul a b) c = grp.mul a (grp.mul b c)) ∧
    (∀ a, grp.mul grp.one a = a) ∧ (∀ a, grp.mul a grp.one = a) ∧
    (∀ a, grp.mul (grp.inv a) a = grp.one) ∧ (∀ a, grp.mul a (grp.inv a) = grp.one) := by
  letI := grp
  exact ⟨mul_assoc, one_mul, mul_one, inv_mul_cancel, mul_inv_cancel⟩

theorem g64j_hc (S : G → MulAut N) (omega : G → G → N) (h : IsFactorCocycle S omega)
    (g k l : G) : S g (omega k l) * omega g (k * l) = omega g k * omega (g * k) l := by
  have := h g k l
  unfold nonabelianDifferential at this
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
  exact this

theorem g64j_assoc (S : G → MulAut N) (omega : G → G → N)
    (hCompatible : CompatibleFactorData S omega) (h : IsFactorCocycle S omega) (a b c : N × G) :
    extensionProduct S omega (extensionProduct S omega a b) c =
      extensionProduct S omega a (extensionProduct S omega b c) := by
  have hC : ∀ g h n, S g (S h n) = omega g h * S (g * h) n * (omega g h)⁻¹ := hCompatible
  unfold extensionProduct
  ext
  · simp only [map_mul, hC]
    simp only [mul_assoc]
    rw [g64j_hc S omega h]
    group
  · simp [mul_assoc]

theorem g64j_cocycle_of_assoc (S : G → MulAut N) (omega : G → G → N)
    (hS : S 1 = MulEquiv.refl N)
    (hassoc : ∀ a b c, extensionProduct S omega (extensionProduct S omega a b) c =
      extensionProduct S omega a (extensionProduct S omega b c)) :
    IsFactorCocycle S omega := by
  intro g k l
  have := congrArg Prod.fst (hassoc (1, g) (1, k) (1, l))
  simp only [extensionProduct, map_one, mul_one, one_mul] at this
  unfold nonabelianDifferential
  rw [← this]
  group

theorem solution
    (S : G → MulAut N) (omega : G → G → N)
    (hS : S 1 = MulEquiv.refl N)
    (hNormalized : NormalizedTwoCochain omega)
    (hCompatible : CompatibleFactorData S omega) :
    (AdmitsExtensionGroup S omega ↔ IsFactorCocycle S omega) ∧
    (∀ grp : Group (N × G), grp.mul = extensionProduct S omega →
      grp.one = (1, 1) ∧
      (∀ n g,
        grp.inv (n, g) = ((S g).symm (n⁻¹ * (omega g g⁻¹)⁻¹), g⁻¹) ∧
        grp.inv (n, g) = ((omega g⁻¹ g)⁻¹ * S g⁻¹ n⁻¹, g⁻¹)) ∧
      (∀ g,
        grp.inv (1, g) = ((S g).symm ((omega g g⁻¹)⁻¹), g⁻¹) ∧
        grp.inv (1, g) = ((omega g⁻¹ g)⁻¹, g⁻¹)) ∧
      (∀ n g n2 g2,
        grp.mul (grp.mul (n, g) (n2, g2)) (grp.inv (n, g)) =
          (n * S g n2 * conjugationCochain omega g g2 *
            S (g * g2 * g⁻¹) n⁻¹, g * g2 * g⁻¹)) ∧
      (∀ n n2 g2,
        grp.mul (grp.mul (n, 1) (n2, g2)) (grp.inv (n, 1)) =
          (n * n2 * S g2 n⁻¹, g2)) ∧
      (∀ g n2 g2,
        grp.mul (grp.mul (1, g) (n2, g2)) (grp.inv (1, g)) =
          (S g n2 * conjugationCochain omega g g2, g * g2 * g⁻¹))) := by
  obtain ⟨hN1, hN2⟩ := hNormalized
  have hS1 : ∀ n, S 1 n = n := by intro n; rw [hS]; rfl
  have e_one_mul : ∀ a : N × G, extensionProduct S omega (1, 1) a = a := by
    intro a; ext <;> simp [extensionProduct, hS1, hN1]
  have e_mul_one : ∀ a : N × G, extensionProduct S omega a (1, 1) = a := by
    intro a; ext <;> simp [extensionProduct, hN2]
  -- facts about any group structure with this multiplication
  have grpfacts : ∀ grp : Group (N × G), grp.mul = extensionProduct S omega →
      IsFactorCocycle S omega ∧ grp.one = (1, 1) ∧
      ∀ n g, grp.inv (n, g) = ((S g).symm (n⁻¹ * (omega g g⁻¹)⁻¹), g⁻¹) ∧
        grp.inv (n, g) = ((omega g⁻¹ g)⁻¹ * S g⁻¹ n⁻¹, g⁻¹) := by
    intro grp hmul
    obtain ⟨fa, f1, f2, f3, f4⟩ := g64j_grp_facts grp
    rw [hmul] at fa f1 f2 f3 f4
    have hcoc := g64j_cocycle_of_assoc S omega hS fa
    have hone : grp.one = (1, 1) := by
      have := f1 (1, 1); rw [e_mul_one] at this; exact this
    refine ⟨hcoc, hone, fun n g => ?_⟩
    have hl := f3 (n, g)
    have hr := f4 (n, g)
    rw [hone] at hl hr
    set x := grp.inv (n, g)
    simp only [extensionProduct, Prod.mk.injEq] at hl hr
    have hx2 : x.2 = g⁻¹ := eq_inv_of_mul_eq_one_left hl.2
    have hx1a : x.1 = (omega g⁻¹ g)⁻¹ * S g⁻¹ n⁻¹ := by
      have h1 := hl.1
      rw [hx2] at h1
      rw [map_inv]
      rw [mul_assoc, mul_eq_one_iff_eq_inv] at h1
      rw [h1, mul_inv_rev]
    have hx1b : x.1 = (S g).symm (n⁻¹ * (omega g g⁻¹)⁻¹) := by
      rw [MulEquiv.eq_symm_apply]
      have h1 := hr.1
      rw [hx2] at h1
      rw [mul_assoc, mul_eq_one_iff_eq_inv] at h1
      rw [h1]
      group
    exact ⟨Prod.ext hx1b hx2, Prod.ext hx1a hx2⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨grp, hmul⟩
    exact (grpfacts grp hmul).1
  · intro hcoc
    refine ⟨@Group.ofLeftAxioms (N × G) ⟨extensionProduct S omega⟩
      ⟨fun a => ((omega a.2⁻¹ a.2)⁻¹ * S a.2⁻¹ a.1⁻¹, a.2⁻¹)⟩ ⟨(1, 1)⟩
      (g64j_assoc S omega hCompatible hcoc) e_one_mul ?_, rfl⟩
    intro a
    change extensionProduct S omega _ a = (1, 1)
    ext <;> simp [extensionProduct]
  · intro grp hmul
    obtain ⟨hcoc, hone, hinv⟩ := grpfacts grp hmul
    have conj : ∀ n g n2 g2,
        grp.mul (grp.mul (n, g) (n2, g2)) (grp.inv (n, g)) =
          (n * S g n2 * conjugationCochain omega g g2 *
            S (g * g2 * g⁻¹) n⁻¹, g * g2 * g⁻¹) := by
      intro n g n2 g2
      have hC : ∀ g h n, S g (S h n) = omega g h * S (g * h) n * (omega g h)⁻¹ := hCompatible
      rw [(hinv n g).2, hmul]
      have hk := g64j_hc S omega hcoc (g * g2) g⁻¹ g
      rw [inv_mul_cancel, hN2, mul_one] at hk
      ext
      · simp only [extensionProduct, conjugationCochain, map_mul, map_inv, hC, hk]
        group
      · simp [extensionProduct]
    refine ⟨hone, hinv, fun g => ?_, conj, fun n n2 g2 => ?_, fun g n2 g2 => ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [(hinv 1 g).1]; simp
      · rw [(hinv 1 g).2]; simp
    · rw [conj]
      simp [conjugationCochain, hS1, hN1, hN2]
    · rw [conj]
      simp
