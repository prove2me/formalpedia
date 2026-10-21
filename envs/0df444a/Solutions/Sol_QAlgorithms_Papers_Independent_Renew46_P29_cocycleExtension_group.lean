-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Renew46.P29.cocycleExtension_group
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T00:26:34.943388+00:00
-- url     : https://prove2.me/submissions/35d3d8ea-9884-421e-b572-18665d2be3a4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P29
open QAlgorithms.Papers.Independent.Renew46.P29

open Set Filter Topology

universe u v

section AlgebraicExtension

variable {G : Type u} [Group G] {A : Type v} [AddCommGroup A]

variable [DistribMulAction G A]

theorem solution
    (f : G → G → A) (hf : NormalizedTwoCocycle f) :
    ∃ groupStructure : Group (A × G),
      letI := groupStructure
      (∀ x y : A × G, x * y = extensionMul f x y) ∧
      (1 : A × G) = (0, 1) ∧
      (∀ x : A × G, x⁻¹ = extensionInv f x) ∧
      (∀ (a b : A) (g h : G),
        (a, g) * (b, h) * (a, g)⁻¹ =
          (a + g • b - (g * h * g⁻¹) • a + f g h - f (g * h * g⁻¹) g,
            g * h * g⁻¹)) ∧
      (∃ q : (A × G) →* G,
        (∀ x, q x = x.2) ∧ Function.Surjective q ∧
        (∀ x, x ∈ q.ker ↔ x.2 = 1) ∧
        ∃ i : Multiplicative A ≃* q.ker,
          (∀ a, (i a).val = (Multiplicative.toAdd a, 1)) ∧
          ∀ (x : A × G) (a : A),
            x * (a, 1) * x⁻¹ = (q x • a, 1)) := by
  obtain ⟨h1, h2, hc⟩ := hf
  have hassoc : ∀ x y z : A × G, extensionMul f (extensionMul f x y) z =
      extensionMul f x (extensionMul f y z) := by
    intro x y z
    unfold extensionMul
    ext
    · simp only [smul_add, mul_smul]
      have := hc x.2 y.2 z.2
      rw [← sub_eq_zero] at this
      rw [← sub_eq_zero, ← this]
      abel
    · simp [mul_assoc]
  have hinvc : ∀ g : G, f g⁻¹ g = g⁻¹ • f g g⁻¹ := by
    intro g
    have := hc g⁻¹ g g⁻¹
    rw [inv_mul_cancel, h2, mul_inv_cancel, h1] at this
    simpa only [add_zero] using this
  let grp : Group (A × G) := @Group.ofLeftAxioms (A × G) ⟨extensionMul f⟩ ⟨extensionInv f⟩
    ⟨(0, 1)⟩ hassoc
    (by intro a; change extensionMul f (0, 1) a = a; ext <;> simp [extensionMul, h2])
    (by
      intro a
      change extensionMul f (extensionInv f a) a = (0, 1)
      ext
      · simp only [extensionMul, extensionInv, smul_add, hinvc]; abel
      · simp [extensionMul, extensionInv])
  letI := grp
  have conj : ∀ (a b : A) (g h : G),
        (a, g) * (b, h) * (a, g)⁻¹ =
          (a + g • b - (g * h * g⁻¹) • a + f g h - f (g * h * g⁻¹) g,
            g * h * g⁻¹) := by
    intro a b g h
    change extensionMul f (extensionMul f (a, g) (b, h)) (extensionInv f (a, g)) = _
    have hk := hc (g * h * g⁻¹) g g⁻¹
    rw [mul_inv_cancel, h1, add_zero, show g * h * g⁻¹ * g = g * h by group] at hk
    ext
    · simp only [extensionMul, extensionInv, smul_add, smul_neg, ← mul_smul]
      rw [show g * h * g⁻¹ = g * h * g⁻¹ from rfl, ← hk,
        show g * h * g⁻¹ = (g * h) * g⁻¹ from rfl]
      abel
    · simp [extensionMul, extensionInv]
  let q : (A × G) →* G :=
    { toFun := Prod.snd, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hker : ∀ x, x ∈ q.ker ↔ x.2 = 1 := fun x => MonoidHom.mem_ker
  refine ⟨grp, fun _ _ => rfl, rfl, fun _ => rfl, conj, q, fun _ => rfl,
    fun g => ⟨(0, g), rfl⟩, hker, ?_⟩
  refine ⟨{ toFun := fun a => ⟨(Multiplicative.toAdd a, 1), (hker _).2 rfl⟩,
            invFun := fun x => Multiplicative.ofAdd x.1.1,
            left_inv := fun a => rfl,
            right_inv := fun x => ?_,
            map_mul' := fun a b => ?_ }, fun a => rfl, ?_⟩
  · apply Subtype.ext
    have := (hker x.1).1 x.2
    exact Prod.ext rfl this.symm
  · apply Subtype.ext
    change _ = extensionMul f _ _
    ext <;> simp [extensionMul, h1]
  · rintro ⟨x1, g⟩ a
    rw [conj]
    ext <;> simp [h1, h2] <;> rfl
