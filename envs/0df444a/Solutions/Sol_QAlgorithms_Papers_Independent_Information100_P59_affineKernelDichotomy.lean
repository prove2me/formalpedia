-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P59.affineKernelDichotomy
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T04:03:40.648517+00:00
-- url     : https://prove2.me/submissions/1ddf1bc6-9ea2-44ef-b179-108581c026ff

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P59

noncomputable section

open scoped Matrix ComplexOrder


open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P59

attribute [local instance 100] LieRing.ofAssociativeRing

/-- arXiv:2610.00046v1 PDF p.16, Lemma 3.17. h is an arbitrary affine Lie
subalgebra, supplied as a linear subspace closed under the actual affine bracket.
The translation kernel and matrix projection are computed from h, never supplied independently. -/
theorem solution {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (h : Submodule ℝ (Module.End ℝ V × V))
    (hbracket : ∀ X ∈ h, ∀ Y ∈ h, affineBracket X Y ∈ h) :
    (∀ (A : Module.End ℝ V), (∃ b, (A,b) ∈ h) →
      ∀ t : V, (0,t) ∈ h → (0,A t) ∈ h) ∧
    ((∃ b : V, (1,b) ∈ h) → IrreducibleProjection h →
      (Xor (∀ t : V, (0,t) ∈ h)
        ((∀ t : V, (0,t) ∈ h ↔ t = 0) ∧
          ∃ v : V,
            (∀ (A : Module.End ℝ V) (b : V),
              (A,b) ∈ h ↔ (∃ c : V, (A,c) ∈ h) ∧ b = A v) ∧
            (∀ X ∈ h, X.1 (-v) + X.2 = 0))) ∧
      ((¬ ∃ w : V, ∀ X ∈ h, X.1 w + X.2 = 0) → ∀ t : V, (0,t) ∈ h)) := by
  have part1 : ∀ (A : Module.End ℝ V), (∃ b, (A,b) ∈ h) → ∀ t : V, (0,t) ∈ h → (0,A t) ∈ h := by
    intro A ⟨b, hb⟩ t ht
    have := hbracket _ hb _ ht
    simpa [affineBracket] using this
  refine ⟨part1, ?_⟩
  rintro ⟨b0, hb0⟩ ⟨hnt, hirr⟩
  let T : Submodule ℝ V :=
    { carrier := {t | ((0 : Module.End ℝ V), t) ∈ h}
      add_mem' := by
        intro x y hx hy
        have := h.add_mem hx hy
        simpa using this
      zero_mem' := by
        show ((0 : Module.End ℝ V), (0 : V)) ∈ h
        exact h.zero_mem
      smul_mem' := by
        intro c x hx
        have := h.smul_mem c hx
        simpa using this }
  have hT : T = ⊥ ∨ T = ⊤ := by
    apply hirr
    intro X hX v hv
    exact part1 X.1 ⟨X.2, by simpa using hX⟩ v hv
  have hmemT : ∀ t, t ∈ T ↔ ((0 : Module.End ℝ V), t) ∈ h := fun t => Iff.rfl
  -- key: if T = ⊥, then every element is (A, A b0)
  have key : T = ⊥ → ∀ X ∈ h, X.2 = X.1 b0 := by
    intro hbot X hX
    have hbr := hbracket _ hb0 _ hX
    have h0 : (0 : Module.End ℝ V) = 1 * X.1 - X.1 * 1 := by simp
    have : X.2 - X.1 b0 ∈ T := by
      rw [hmemT]
      convert hbr using 1
      simp [affineBracket]
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  have hnotboth : ¬ (T = ⊥ ∧ T = ⊤) := by
    rintro ⟨h1, h2⟩
    obtain ⟨x, y, hxy⟩ := hnt
    have : (⊥ : Submodule ℝ V) = ⊤ := h1 ▸ h2
    have hx : x ∈ (⊥ : Submodule ℝ V) := this ▸ Submodule.mem_top
    have hy : y ∈ (⊥ : Submodule ℝ V) := this ▸ Submodule.mem_top
    rw [Submodule.mem_bot] at hx hy
    exact hxy (hx.trans hy.symm)
  have htopiff : (∀ t : V, ((0 : Module.End ℝ V), t) ∈ h) ↔ T = ⊤ := by
    constructor
    · intro H; rw [eq_top_iff]; intro t _; exact H t
    · intro H t; rw [← hmemT, H]; exact Submodule.mem_top
  have hbotiff : (∀ t : V, ((0 : Module.End ℝ V), t) ∈ h ↔ t = 0) ↔ T = ⊥ := by
    constructor
    · intro H; rw [eq_bot_iff]; intro t ht; rw [Submodule.mem_bot]; exact (H t).1 ht
    · intro H t; rw [← hmemT, H, Submodule.mem_bot]
  have second : T = ⊥ → ((∀ t : V, ((0 : Module.End ℝ V), t) ∈ h ↔ t = 0) ∧
          ∃ v : V,
            (∀ (A : Module.End ℝ V) (b : V),
              (A,b) ∈ h ↔ (∃ c : V, (A,c) ∈ h) ∧ b = A v) ∧
            (∀ X ∈ h, X.1 (-v) + X.2 = 0)) := by
    intro hbot
    refine ⟨hbotiff.2 hbot, b0, ?_, ?_⟩
    · intro A b
      constructor
      · intro hAb; exact ⟨⟨b, hAb⟩, key hbot (A, b) hAb⟩
      · rintro ⟨⟨c, hc⟩, rfl⟩
        have := key hbot (A, c) hc
        simp only at this
        rw [← this]; exact hc
    · intro X hX
      rw [key hbot X hX, map_neg, neg_add_cancel]
  refine ⟨?_, ?_⟩
  · rcases hT with hbot | htop
    · exact Or.inr ⟨second hbot, fun H => hnotboth ⟨hbot, htopiff.1 H⟩⟩
    · exact Or.inl ⟨htopiff.2 htop, fun H => hnotboth ⟨hbotiff.1 H.1, htop⟩⟩
  · intro hno
    rcases hT with hbot | htop
    · exact absurd ⟨-b0, fun X hX => by rw [key hbot X hX, map_neg, neg_add_cancel]⟩ hno
    · exact htopiff.2 htop



end

