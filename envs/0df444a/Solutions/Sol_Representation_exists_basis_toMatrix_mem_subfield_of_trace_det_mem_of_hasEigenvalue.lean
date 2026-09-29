-- Prove2me | solution 1 for Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/55fa4020-9dc7-5445-86bc-5642e5bbe94e

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue

set_option autoImplicit false
set_option maxHeartbeats 6400000

open Module

namespace P2mWs11Desc

variable {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {G : Type*} [Group G]

theorem mem_of_eq {F : Subfield Ω} {x y : Ω} (h : y ∈ F) (e : x = y) : x ∈ F := e ▸ h

theorem exists_basis (hV : finrank Ω V = 2) (x y : V) (h : LinearIndependent Ω ![x, y]) :
    ∃ b : Basis (Fin 2) Ω V, b 0 = x ∧ b 1 = y :=
  ⟨basisOfLinearIndependentOfCardEqFinrank h (by simp [hV]), by simp, by simp⟩

theorem pair_of_basis (b : Basis (Fin 2) Ω V) : LinearIndependent Ω ![b 0, b 1] := by
  convert b.linearIndependent using 1
  ext i; fin_cases i <;> rfl

theorem smul_add_smul_eq_zero (b : Basis (Fin 2) Ω V) {s t : Ω} (h : s • b 0 + t • b 1 = 0) :
    s = 0 ∧ t = 0 :=
  LinearIndependent.pair_iff.mp (pair_of_basis b) s t h

theorem eq_of_smul_add_smul_eq (b : Basis (Fin 2) Ω V) {s t s' t' : Ω}
    (h : s • b 0 + t • b 1 = s' • b 0 + t' • b 1) : s = s' ∧ t = t' := by
  have h0 : (s - s') • b 0 + (t - t') • b 1 = 0 := by
    calc (s - s') • b 0 + (t - t') • b 1 = (s • b 0 + t • b 1) - (s' • b 0 + t' • b 1) := by
            simp only [sub_smul]; abel
      _ = 0 := by rw [h, sub_self]
  obtain ⟨h1, h2⟩ := smul_add_smul_eq_zero b h0
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

theorem linIndep_of_det_ne_zero (b : Basis (Fin 2) Ω V) {p q r s : Ω} (h : p * s - q * r ≠ 0) :
    LinearIndependent Ω ![p • b 0 + r • b 1, q • b 0 + s • b 1] := by
  refine LinearIndependent.pair_iff.mpr fun α β hαβ => ?_
  have h1 : (α * p + β * q) • b 0 + (α * r + β * s) • b 1 = 0 := by
    calc (α * p + β * q) • b 0 + (α * r + β * s) • b 1
        = α • (p • b 0 + r • b 1) + β • (q • b 0 + s • b 1) := by
          simp only [add_smul, mul_smul, smul_add]; abel
      _ = 0 := hαβ
  obtain ⟨e1, e2⟩ := smul_add_smul_eq_zero b h1
  have hα : α * (p * s - q * r) = 0 := by linear_combination s * e1 - q * e2
  have hβ : β * (p * s - q * r) = 0 := by linear_combination p * e2 - r * e1
  exact ⟨(mul_eq_zero.mp hα).resolve_right h, (mul_eq_zero.mp hβ).resolve_right h⟩

noncomputable def A (ρ : G →* (V ≃ₗ[Ω] V)) (b : Basis (Fin 2) Ω V) (g : G) :
    Matrix (Fin 2) (Fin 2) Ω :=
  LinearMap.toMatrix b b (ρ g).toLinearMap

variable (ρ : G →* (V ≃ₗ[Ω] V))

theorem A_mul (b : Basis (Fin 2) Ω V) (g h : G) : A ρ b (g * h) = A ρ b g * A ρ b h := by
  simp only [A, map_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

theorem A_mul_apply (b : Basis (Fin 2) Ω V) (g h : G) (i j : Fin 2) :
    A ρ b (g * h) i j = A ρ b g i 0 * A ρ b h 0 j + A ρ b g i 1 * A ρ b h 1 j := by
  rw [A_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem apply_basis (b : Basis (Fin 2) Ω V) (g : G) (j : Fin 2) :
    ρ g (b j) = A ρ b g 0 j • b 0 + A ρ b g 1 j • b 1 := by
  simp only [A, LinearMap.toMatrix_apply, LinearEquiv.coe_coe]
  have := b.sum_repr (ρ g (b j))
  rw [Fin.sum_univ_two] at this
  exact this.symm

theorem trace_A (b : Basis (Fin 2) Ω V) (g : G) :
    A ρ b g 0 0 + A ρ b g 1 1 = LinearMap.trace Ω V (ρ g).toLinearMap := by
  rw [LinearMap.trace_eq_matrix_trace Ω b, Matrix.trace_fin_two]; rfl

theorem det_A (b : Basis (Fin 2) Ω V) (g : G) :
    A ρ b g 0 0 * A ρ b g 1 1 - A ρ b g 0 1 * A ρ b g 1 0 = LinearMap.det (ρ g).toLinearMap := by
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]; rfl

theorem A_eq_of_apply (b : Basis (Fin 2) Ω V) (g : G) (j : Fin 2) {p r : Ω}
    (h : ρ g (b j) = p • b 0 + r • b 1) : A ρ b g 0 j = p ∧ A ρ b g 1 j = r :=
  eq_of_smul_add_smul_eq b (by rw [← apply_basis ρ b g j]; exact h)

variable {ρ}

theorem exists_A_one_zero_ne_zero
    (hirr : ∀ W : Submodule Ω V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (b : Basis (Fin 2) Ω V) : ∃ g, A ρ b g 1 0 ≠ 0 := by
  by_contra h'
  have h : ∀ g, A ρ b g 1 0 = 0 := fun g => not_not.mp (not_exists.mp h' g)
  have hW : ∀ g, ∀ v ∈ (Ω ∙ b 0), ρ g v ∈ (Ω ∙ b 0) := by
    intro g v hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, apply_basis ρ b g 0, h g, zero_smul, add_zero, smul_smul]
    exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
  rcases hirr _ hW with h0 | h0
  · exact b.ne_zero 0 (Submodule.span_singleton_eq_bot.mp h0)
  · have h1 : b 1 ∈ (Ω ∙ b 0) := h0 ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h1
    have := smul_add_smul_eq_zero b (s := t) (t := -1) (by rw [ht, neg_one_smul, add_neg_cancel])
    exact one_ne_zero (neg_eq_zero.mp this.2)

theorem exists_A_zero_one_ne_zero
    (hirr : ∀ W : Submodule Ω V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (b : Basis (Fin 2) Ω V) : ∃ g, A ρ b g 0 1 ≠ 0 := by
  by_contra h'
  have h : ∀ g, A ρ b g 0 1 = 0 := fun g => not_not.mp (not_exists.mp h' g)
  have hW : ∀ g, ∀ v ∈ (Ω ∙ b 1), ρ g v ∈ (Ω ∙ b 1) := by
    intro g v hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, apply_basis ρ b g 1, h g, zero_smul, zero_add, smul_smul]
    exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩
  rcases hirr _ hW with h0 | h0
  · exact b.ne_zero 1 (Submodule.span_singleton_eq_bot.mp h0)
  · have h1 : b 0 ∈ (Ω ∙ b 1) := h0 ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp h1
    have := smul_add_smul_eq_zero b (s := -1) (t := t) (by rw [ht, neg_one_smul, neg_add_cancel])
    exact one_ne_zero (neg_eq_zero.mp this.1)

theorem main (F : Subfield Ω) (ρ : G →* (V ≃ₗ[Ω] V)) (hV : finrank Ω V = 2)
    (hirr : ∀ W : Submodule Ω V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ g, LinearMap.trace Ω V (ρ g).toLinearMap ∈ F)
    (hdet : ∀ g, LinearMap.det (ρ g).toLinearMap ∈ F)
    (g₀ : G) (a : Ω) (haF : a ∈ F) (hev : Module.End.HasEigenvalue (ρ g₀).toLinearMap a)
    (hns : (ρ g₀).toLinearMap ≠ a • LinearMap.id) :
    ∃ b : Basis (Fin 2) Ω V, ∀ g (i j : Fin 2), A ρ b g i j ∈ F := by
  haveI : FiniteDimensional Ω V := .of_finrank_eq_succ hV
  have htr' : ∀ (b : Basis (Fin 2) Ω V) (g : G), A ρ b g 0 0 + A ρ b g 1 1 ∈ F :=
    fun b g => by rw [trace_A]; exact htr g
  have hdet' : ∀ (b : Basis (Fin 2) Ω V) (g : G),
      A ρ b g 0 0 * A ρ b g 1 1 - A ρ b g 0 1 * A ρ b g 1 0 ∈ F :=
    fun b g => by rw [det_A]; exact hdet g

  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hgv : ρ g₀ v = a • v := hv.apply_eq_smul
  have hlt : (Ω ∙ v) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    have h1 := finrank_span_singleton (K := Ω) hv0
    rw [htop, finrank_top, hV] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨u₀, -, hu₀⟩ := SetLike.exists_of_lt hlt
  have hli : LinearIndependent Ω ![v, u₀] := by
    refine linearIndependent_fin2.mpr ⟨?_, ?_⟩
    · intro h
      have h' : u₀ = 0 := by simpa using h
      exact hu₀ (by rw [h']; exact zero_mem _)
    · intro c hc'
      have hc : c • u₀ = v := by simpa using hc'
      have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact hv0 hc.symm
      exact hu₀ (Submodule.mem_span_singleton.mpr
        ⟨c⁻¹, by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩)
  obtain ⟨b₀, hb₀0, hb₀1⟩ := exists_basis hV v u₀ hli

  have e₀ : A ρ b₀ g₀ 0 0 = a ∧ A ρ b₀ g₀ 1 0 = 0 :=
    A_eq_of_apply ρ b₀ g₀ 0 (by rw [hb₀0, hgv, zero_smul, add_zero])
  set β := A ρ b₀ g₀ 0 1 with hβ
  set μ := A ρ b₀ g₀ 1 1 with hμ
  have hμF : μ ∈ F := mem_of_eq (F.sub_mem (htr' b₀ g₀) haF) (by rw [e₀.1]; ring)
  have hg₀u : ρ g₀ u₀ = β • v + μ • u₀ := by
    have := apply_basis ρ b₀ g₀ 1; rwa [hb₀0, hb₀1] at this
  by_cases hμa : μ = a
  ·
    have hβ0 : β ≠ 0 := by
      intro hβ0
      apply hns
      refine b₀.ext fun i => ?_
      fin_cases i
      · simp [hb₀0, hgv]
      · simp [hb₀1, hg₀u, hβ0, hμa]

    have hli₁ : LinearIndependent Ω ![β • v, u₀] := by
      have := linIndep_of_det_ne_zero b₀ (p := β) (q := 0) (r := 0) (s := 1) (by simpa using hβ0)
      simpa [hb₀0, hb₀1] using this
    obtain ⟨b₁, hb₁0, hb₁1⟩ := exists_basis hV (β • v) u₀ hli₁
    have hJ₁0 : ρ g₀ (b₁ 0) = a • b₁ 0 := by rw [hb₁0, map_smul, hgv, smul_comm]
    have hJ₁1 : ρ g₀ (b₁ 1) = b₁ 0 + a • b₁ 1 := by rw [hb₁1, hb₁0, hg₀u, hμa]

    have jordan : ∀ c : Basis (Fin 2) Ω V, ρ g₀ (c 0) = a • c 0 → ρ g₀ (c 1) = c 0 + a • c 1 →
        ∀ h, A ρ c h 1 0 ∈ F := by
      intro c hc0 hc1 h
      have f0 := A_eq_of_apply ρ c g₀ 0 (p := a) (r := 0) (by rw [hc0, zero_smul, add_zero])
      have f1 := A_eq_of_apply ρ c g₀ 1 (p := 1) (r := a) (by rw [hc1, one_smul])
      have t1 : a * (A ρ c h 0 0 + A ρ c h 1 1) + A ρ c h 1 0 ∈ F := by
        convert htr' c (g₀ * h) using 1
        rw [A_mul_apply, A_mul_apply, f0.1, f0.2, f1.1, f1.2]; ring
      exact mem_of_eq (F.sub_mem t1 (F.mul_mem haF (htr' c h))) (by ring)

    obtain ⟨h₁, hr₁⟩ := exists_A_one_zero_ne_zero hirr b₁
    have hli₂ : LinearIndependent Ω ![b₁ 0, b₁ 1 + (A ρ b₁ h₁ 0 0 / A ρ b₁ h₁ 1 0) • b₁ 0] := by
      have := linIndep_of_det_ne_zero b₁ (p := 1) (q := A ρ b₁ h₁ 0 0 / A ρ b₁ h₁ 1 0)
        (r := 0) (s := 1) (by simp)
      simpa [add_comm] using this
    obtain ⟨b, hb0, hb1⟩ := exists_basis hV _ _ hli₂
    have hJ0 : ρ g₀ (b 0) = a • b 0 := by rw [hb0]; exact hJ₁0
    have hJ1 : ρ g₀ (b 1) = b 0 + a • b 1 := by
      rw [hb1, hb0, map_add, map_smul, hJ₁1, hJ₁0]; module
    have hA₁ : A ρ b h₁ 0 0 = 0 ∧ A ρ b h₁ 1 0 = A ρ b₁ h₁ 1 0 := A_eq_of_apply ρ b h₁ 0 (by
      rw [hb0, hb1, apply_basis ρ b₁ h₁ 0, zero_smul, zero_add, smul_add, smul_smul,
        mul_div_cancel₀ _ hr₁, add_comm])
    have hr : ∀ h, A ρ b h 1 0 ∈ F := jordan b hJ0 hJ1
    have hr₁F : A ρ b₁ h₁ 1 0 ∈ F := hA₁.2 ▸ hr h₁
    have hs₁F : A ρ b h₁ 1 1 ∈ F := mem_of_eq (htr' b h₁) (by rw [hA₁.1, zero_add])
    have hq₁F : A ρ b h₁ 0 1 ∈ F := by
      have t : -(A ρ b h₁ 0 1 * A ρ b₁ h₁ 1 0) ∈ F := by
        convert hdet' b h₁ using 1; rw [hA₁.1, hA₁.2]; ring
      exact mem_of_eq (F.div_mem (F.neg_mem t) hr₁F) (by field_simp)
    refine ⟨b, fun h => ?_⟩
    have hp : A ρ b h 0 0 ∈ F := by
      have t : A ρ b₁ h₁ 1 0 * A ρ b h 0 0 + A ρ b h₁ 1 1 * A ρ b h 1 0 ∈ F := by
        convert hr (h₁ * h) using 1; rw [A_mul_apply, hA₁.2]
      exact mem_of_eq (F.div_mem (F.sub_mem t (F.mul_mem hs₁F (hr h))) hr₁F) (by field_simp; ring)
    have hs : A ρ b h 1 1 ∈ F := mem_of_eq (F.sub_mem (htr' b h) hp) (by ring)
    have hq : A ρ b h 0 1 ∈ F := by
      have t : A ρ b h₁ 0 1 * A ρ b h 1 0 +
          (A ρ b₁ h₁ 1 0 * A ρ b h 0 1 + A ρ b h₁ 1 1 * A ρ b h 1 1) ∈ F := by
        convert htr' b (h₁ * h) using 1
        rw [A_mul_apply, A_mul_apply, hA₁.1, hA₁.2]; ring
      exact mem_of_eq (F.div_mem (F.sub_mem (F.sub_mem t (F.mul_mem hq₁F (hr h)))
        (F.mul_mem hs₁F hs)) hr₁F) (by field_simp; ring)
    intro i j
    fin_cases i <;> fin_cases j
    exacts [hp, hq, hr h, hs]
  ·
    have hμa' : μ - a ≠ 0 := sub_ne_zero.mpr hμa
    have hg₀u₁ : ρ g₀ (u₀ + (β / (μ - a)) • v) = μ • (u₀ + (β / (μ - a)) • v) := by
      rw [map_add, map_smul, hg₀u, hgv, smul_add, smul_smul, smul_smul]
      have key : β + β / (μ - a) * a = μ * (β / (μ - a)) := by field_simp; ring
      calc β • v + μ • u₀ + (β / (μ - a) * a) • v = (β + β / (μ - a) * a) • v + μ • u₀ := by
              rw [add_smul]; abel
        _ = (μ * (β / (μ - a))) • v + μ • u₀ := by rw [key]
        _ = μ • u₀ + (μ * (β / (μ - a))) • v := add_comm _ _
    have hli₁ : LinearIndependent Ω ![v, u₀ + (β / (μ - a)) • v] := by
      have := linIndep_of_det_ne_zero b₀ (p := 1) (r := 0) (q := β / (μ - a)) (s := 1) (by simp)
      simpa [hb₀0, hb₀1, add_comm] using this
    obtain ⟨b₁, hb₁0, hb₁1⟩ := exists_basis hV _ _ hli₁
    have hD₁0 : ρ g₀ (b₁ 0) = a • b₁ 0 := by rw [hb₁0]; exact hgv
    have hD₁1 : ρ g₀ (b₁ 1) = μ • b₁ 1 := by rw [hb₁1]; exact hg₀u₁

    obtain ⟨g₁, hγ⟩ := exists_A_one_zero_ne_zero hirr b₁
    have hli₂ : LinearIndependent Ω ![b₁ 0, A ρ b₁ g₁ 1 0 • b₁ 1] := by
      have := linIndep_of_det_ne_zero b₁ (p := 1) (r := 0) (q := 0) (s := A ρ b₁ g₁ 1 0)
        (by simpa using hγ)
      simpa using this
    obtain ⟨b, hb0, hb1⟩ := exists_basis hV _ _ hli₂
    have hD0 : ρ g₀ (b 0) = a • b 0 := by rw [hb0]; exact hD₁0
    have hD1 : ρ g₀ (b 1) = μ • b 1 := by rw [hb1, map_smul, hD₁1, smul_comm]
    have e0 := A_eq_of_apply ρ b g₀ 0 (p := a) (r := 0) (by rw [hD0, zero_smul, add_zero])
    have e1 := A_eq_of_apply ρ b g₀ 1 (p := 0) (r := μ) (by rw [hD1, zero_smul, zero_add])
    have hγ1 : A ρ b g₁ 1 0 = 1 := (A_eq_of_apply ρ b g₁ 0 (p := A ρ b₁ g₁ 0 0) (r := 1) (by
      rw [hb0, hb1, apply_basis ρ b₁ g₁ 0, one_smul])).2

    have hdiag : ∀ h, A ρ b h 0 0 ∈ F ∧ A ρ b h 1 1 ∈ F := by
      intro h
      have t0 := htr' b h
      have t1 : a * A ρ b h 0 0 + μ * A ρ b h 1 1 ∈ F := by
        convert htr' b (g₀ * h) using 1
        rw [A_mul_apply, A_mul_apply, e0.1, e0.2, e1.1, e1.2]; ring
      have hs : A ρ b h 1 1 ∈ F :=
        mem_of_eq (F.div_mem (F.sub_mem t1 (F.mul_mem haF t0)) (F.sub_mem hμF haF))
          (by field_simp; ring)
      exact ⟨mem_of_eq (F.sub_mem t0 hs) (by ring), hs⟩

    have hq : ∀ h, A ρ b h 0 1 ∈ F := by
      intro h
      have t : A ρ b h 0 1 + A ρ b g₁ 1 1 * A ρ b h 1 1 ∈ F := by
        convert (hdiag (g₁ * h)).2 using 1; rw [A_mul_apply, hγ1, one_mul]
      exact mem_of_eq (F.sub_mem t (F.mul_mem (hdiag g₁).2 (hdiag h).2)) (by ring)

    obtain ⟨h₂, hq₂⟩ := exists_A_zero_one_ne_zero hirr b
    have hr : ∀ h, A ρ b h 1 0 ∈ F := by
      intro h
      have t : A ρ b h₂ 0 0 * A ρ b h 0 0 + A ρ b h₂ 0 1 * A ρ b h 1 0 ∈ F := by
        convert (hdiag (h₂ * h)).1 using 1; rw [A_mul_apply]
      exact mem_of_eq (F.div_mem (F.sub_mem t (F.mul_mem (hdiag h₂).1 (hdiag h).1)) (hq h₂))
        (by field_simp; ring)
    exact ⟨b, fun h i j => by
      fin_cases i <;> fin_cases j
      exacts [(hdiag h).1, hq h, hr h, (hdiag h).2]⟩

end P2mWs11Desc

theorem solution
    {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {G : Type*} [Group G]
    (F : Subfield Ω) (ρ : G →* (V ≃ₗ[Ω] V)) (hV : Module.finrank Ω V = 2)
    (hirr : ∀ W : Submodule Ω V, (∀ g, ∀ v ∈ W, ρ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (htr : ∀ g, LinearMap.trace Ω V (ρ g).toLinearMap ∈ F)
    (hdet : ∀ g, LinearMap.det (ρ g).toLinearMap ∈ F)
    (g₀ : G) (a : Ω) (haF : a ∈ F) (hev : Module.End.HasEigenvalue (ρ g₀).toLinearMap a)
    (hns : (ρ g₀).toLinearMap ≠ a • LinearMap.id) :
    ∃ b : Module.Basis (Fin 2) Ω V,
      ∀ g (i j : Fin 2), LinearMap.toMatrix b b (ρ g).toLinearMap i j ∈ F :=
  P2mWs11Desc.main F ρ hV hirr htr hdet g₀ a haF hev hns

end S_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue
end P2MW
export P2MW.S_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue (solution)
