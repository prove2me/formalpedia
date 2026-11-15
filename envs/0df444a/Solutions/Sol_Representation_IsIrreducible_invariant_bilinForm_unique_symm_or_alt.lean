-- Prove2me | solution 1 for Representation.IsIrreducible.invariant_bilinForm_unique_symm_or_alt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T07:19:52.994433+00:00
-- url     : https://prove2.me/submissions/d56370e5-554f-4e78-84ba-31c498032851

import Mathlib

set_option autoImplicit false

namespace SelfDualSol

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- `B` is `G`-invariant. -/
def IsInvForm (ρ : Representation k G V) (B : LinearMap.BilinForm k V) : Prop :=
  ∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w

/-- Elementwise irreducibility: every `G`-stable subspace is `⊥` or `⊤`. -/
def Irr (ρ : Representation k G V) : Prop :=
  ∀ U : Submodule k V, (∀ (g : G), ∀ v ∈ U, ρ g v ∈ U) → U = ⊥ ∨ U = ⊤

theorem irr_of_isIrreducible [ρ.IsIrreducible] : Irr ρ := by
  intro U hU
  let S : Subrepresentation ρ := ⟨U, fun g v hv => hU g v hv⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · left; exact congrArg Subrepresentation.toSubmodule h
  · right; exact congrArg Subrepresentation.toSubmodule h

theorem nontrivial_of_isIrreducible [ρ.IsIrreducible] : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  show (⊥ : Submodule k V) = ⊤
  rw [eq_comm, Submodule.eq_bot_iff]
  intro x _
  exact Subsingleton.elim x 0

/-- **Schur**: an endomorphism commuting with an irreducible `ρ` is a scalar. -/
theorem schur [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] (hρ : Irr ρ) (T : V →ₗ[k] V)
    (hT : ∀ (g : G) (v : V), T (ρ g v) = ρ g (T v)) : ∃ c : k, ∀ v, T v = c • v := by
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  refine ⟨c, fun v => ?_⟩
  have hinv : ∀ (g : G), ∀ v ∈ Module.End.eigenspace T c, ρ g v ∈ Module.End.eigenspace T c :=
    fun g v hv => by
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hT, hv, map_smul]
  rcases hρ _ hinv with h | h
  · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
  · have hv : v ∈ Module.End.eigenspace T c := by rw [h]; exact Submodule.mem_top
    exact Module.End.mem_eigenspace_iff.1 hv

/-- A nondegenerate invariant form is unique up to scalar. -/
theorem eq_smul_of_isInvForm [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] (hρ : Irr ρ)
    {B B' : LinearMap.BilinForm k V} (hB : B.Nondegenerate) (hBi : IsInvForm ρ B) (hB'i : IsInvForm ρ B') :
    ∃ c : k, B' = c • B := by
  let T : V →ₗ[k] V := (B.toDual hB).symm.toLinearMap ∘ₗ B'
  have hT : ∀ v w, B (T v) w = B' v w := fun v w => by
    show B ((B.toDual hB).symm (B' v)) w = B' v w
    rw [← LinearMap.BilinForm.toDual_def hB, LinearEquiv.apply_symm_apply]
  have hcomm : ∀ (g : G) (v : V), T (ρ g v) = ρ g (T v) := by
    intro g v
    have e1 : ∀ w, B' (ρ g v) w = B (ρ g (T v)) w := fun w => by
      conv_lhs => rw [← ρ.self_inv_apply g w]
      rw [hB'i, ← hT, ← hBi g, ρ.self_inv_apply]
    have hx : ∀ w, B (T (ρ g v) - ρ g (T v)) w = 0 := fun w => by
      rw [LinearMap.map_sub₂, hT, e1 w, sub_self]
    exact sub_eq_zero.1 (hB.1 _ hx)
  obtain ⟨c, hc⟩ := schur hρ T hcomm
  refine ⟨c, LinearMap.ext₂ fun v w => ?_⟩
  rw [← hT, hc, LinearMap.map_smul₂]
  rfl

/-- A nondegenerate invariant form satisfies `Bᵗ = ± B`. -/
theorem flip_eq_or [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] (hρ : Irr ρ)
    {B : LinearMap.BilinForm k V} (hB : B.Nondegenerate) (hBi : IsInvForm ρ B) :
    B.flip = B ∨ B.flip = -B := by
  obtain ⟨c, hc⟩ := eq_smul_of_isInvForm hρ hB hBi (B' := B.flip) (fun g v w => hBi g w v)
  have h1 : ∀ v w, B w v = c * B v w := fun v w =>
    congrArg (fun F : LinearMap.BilinForm k V => F v w) hc
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ : ∃ w, B x w ≠ 0 := by
    by_contra h
    exact hx (hB.1 x fun w => not_not.1 fun h' => h ⟨w, h'⟩)
  have hcc : c * c = 1 := by
    have e := h1 w x
    rw [h1 x w] at e
    have h2 : (c * c - 1) * B x w = 0 := by rw [sub_mul, one_mul, mul_assoc, ← e, sub_self]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right hw)
  rcases mul_self_eq_one_iff.1 hcc with h | h
  · left; rw [hc, h, one_smul]
  · right; rw [hc, h]; ext v w; simp

/-- A normalising `Φ` is a similitude of `B`. -/
theorem exists_similitude [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] (hρ : Irr ρ)
    {B : LinearMap.BilinForm k V} (hB : B.Nondegenerate) (hBi : IsInvForm ρ B) {Φ : V ≃ₗ[k] V}
    (hΦ : ∀ g : G, ∃ h : G, ∀ v : V, Φ (ρ g v) = ρ h (Φ v)) :
    ∃ c : k, c ≠ 0 ∧ ∀ v w, B (Φ v) (Φ w) = c * B v w := by
  let B' : LinearMap.BilinForm k V := B.compl₁₂ (Φ : V →ₗ[k] V) (Φ : V →ₗ[k] V)
  have hB'i : IsInvForm ρ B' := fun g v w => by
    obtain ⟨h, hh⟩ := hΦ g
    show B (Φ (ρ g v)) (Φ (ρ g w)) = B (Φ v) (Φ w)
    rw [hh, hh, hBi]
  obtain ⟨c, hc⟩ := eq_smul_of_isInvForm hρ hB hBi hB'i
  have h1 : ∀ v w, B (Φ v) (Φ w) = c * B v w := fun v w =>
    congrArg (fun F : LinearMap.BilinForm k V => F v w) hc
  refine ⟨c, fun h0 => ?_, h1⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  apply hx
  apply hB.1
  intro w
  have h2 := h1 (Φ.symm x) (Φ.symm w)
  rwa [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, h0, zero_mul] at h2

/-- The scalar twist `a • Φ` with `a² c = 1` preserves `B`. -/
theorem exists_twist [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] (hρ : Irr ρ)
    {B : LinearMap.BilinForm k V} (hB : B.Nondegenerate) (hBi : IsInvForm ρ B) {Φ : V ≃ₗ[k] V}
    (hΦ : ∀ g : G, ∃ h : G, ∀ v : V, Φ (ρ g v) = ρ h (Φ v)) :
    ∃ a : k, a ≠ 0 ∧ ∀ v w : V, B (a • Φ v) (a • Φ w) = B v w := by
  obtain ⟨c, hc0, hc⟩ := exists_similitude hρ hB hBi hΦ
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) two_pos
  have hb0 : b ≠ 0 := by rintro rfl; exact hc0 (by rw [← hb]; ring)
  refine ⟨b⁻¹, inv_ne_zero hb0, fun v w => ?_⟩
  rw [LinearMap.map_smul₂, map_smul, hc, smul_eq_mul, smul_eq_mul, ← hb,
    show b⁻¹ * (b⁻¹ * (b ^ 2 * B v w)) = (b⁻¹ * b) ^ 2 * B v w by ring, inv_mul_cancel₀ hb0, one_pow, one_mul]

end SelfDualSol

theorem solution
    {k G V : Type*} [Field k] [IsAlgClosed k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible]
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (hBinv : ∀ (g : G) (v w : V), B (ρ g v) (ρ g w) = B v w) :
    (∀ B' : LinearMap.BilinForm k V, (∀ (g : G) (v w : V), B' (ρ g v) (ρ g w) = B' v w) →
      ∃ c : k, B' = c • B) ∧
    ((∀ v w : V, B v w = B w v) ∨ ∀ v : V, B v v = 0) ∧
    ∀ Φ : V ≃ₗ[k] V, (∀ g : G, ∃ h : G, ∀ v : V, Φ (ρ g v) = ρ h (Φ v)) →
      (∃ c : k, c ≠ 0 ∧ ∀ v w : V, B (Φ v) (Φ w) = c * B v w) ∧
      ∃ a : k, a ≠ 0 ∧ ∀ v w : V, B (a • Φ v) (a • Φ w) = B v w := by

  haveI : Nontrivial V := SelfDualSol.nontrivial_of_isIrreducible (ρ := ρ)
  have hρ : SelfDualSol.Irr ρ := SelfDualSol.irr_of_isIrreducible
  refine ⟨fun B' hB' => SelfDualSol.eq_smul_of_isInvForm hρ hB hBinv hB', ?_,
    fun Φ hΦ => ⟨SelfDualSol.exists_similitude hρ hB hBinv hΦ, SelfDualSol.exists_twist hρ hB hBinv hΦ⟩⟩
  have hfl : ∀ v w : V, B.flip w v = B v w := fun v w => rfl
  rcases SelfDualSol.flip_eq_or hρ hB hBinv with h | h
  · left
    intro v w
    rw [← hfl, h]
  · have e : ∀ v w : V, B v w = -B w v := fun v w => by
      rw [← hfl, h, LinearMap.neg_apply, LinearMap.neg_apply]
    by_cases h2 : (2 : k) = 0
    · left
      intro v w
      have hneg : ∀ x : k, -x = x := fun x => by
        rw [neg_eq_iff_add_eq_zero, ← two_mul, h2, zero_mul]
      rw [e v w, hneg]
    · right
      intro v
      have h3 : (2 : k) * B v v = 0 := by linear_combination e v v
      exact (mul_eq_zero.1 h3).resolve_left h2
