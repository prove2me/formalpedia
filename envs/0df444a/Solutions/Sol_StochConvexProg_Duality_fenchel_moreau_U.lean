-- Prove2me | solution 1 for StochConvexProg.Duality.fenchel_moreau_U
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T14:37:04.415522+00:00
-- url     : https://prove2.me/submissions/4c993be8-48a0-4e80-87e1-a10d8f56480b

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open Topology

namespace SCPFM

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Separation step: a point strictly below the epigraph is separated by `(u,t) ↦ B u y + c t`. -/
theorem sep (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (φ : WeakBilin B → EReal)
    (hconv : Convex ℝ {p : WeakBilin B × ℝ | φ p.1 ≤ (p.2 : EReal)})
    (hlsc : LowerSemicontinuous φ) (u₀ : WeakBilin B) (α : ℝ) (hα : ¬ φ u₀ ≤ (α : EReal)) :
    ∃ (y : F) (c s : ℝ), (∀ (u : WeakBilin B) (t : ℝ), φ u ≤ (t : EReal) → B u y + t * c < s) ∧
      s < B u₀ y + α * c := by
  have hcl : IsClosed {p : WeakBilin B × ℝ | φ p.1 ≤ (p.2 : EReal)} := by
    have h := lowerSemicontinuous_iff_isClosed_epigraph.mp hlsc
    have hc : Continuous (fun p : WeakBilin B × ℝ => (p.1, (p.2 : EReal))) :=
      Continuous.prodMk continuous_fst (continuous_coe_real_ereal.comp continuous_snd)
    exact h.preimage hc
  obtain ⟨f, s, hf, hs⟩ := geometric_hahn_banach_closed_point (x := (u₀, α)) hconv hcl hα
  obtain ⟨y, hy⟩ := LinearMap.dualEmbedding_surjective B
    (f.comp (ContinuousLinearMap.inl ℝ (WeakBilin B) ℝ))
  have hyu : ∀ u : WeakBilin B, B u y = f (u, 0) := by
    intro u
    have := congrArg (fun g : StrongDual ℝ (WeakBilin B) => g u) hy
    simp only [WeakBilin.eval] at this
    exact this
  have hdec : ∀ (u : WeakBilin B) (t : ℝ), f (u, t) = B u y + t * f (0, 1) := by
    intro u t
    have : ((u, t) : WeakBilin B × ℝ) = (u, 0) + t • ((0 : WeakBilin B), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, hyu, smul_eq_mul]
  refine ⟨y, f (0, 1), s, fun u t ht => ?_, ?_⟩
  · rw [← hdec]; exact hf (u, t) ht
  · rw [← hdec]; exact hs

/-- Real form of an affine minorant gives the EReal conjugate bound. -/
theorem conj_le (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (φ : E → EReal) (hbot : ∀ u, φ u ≠ ⊥) (y : F) (β : ℝ)
    (h : ∀ (u : E) (r : ℝ), φ u ≤ (r : EReal) → B u y - r ≤ β) :
    (⨆ u, ((B u y : ℝ) : EReal) - φ u) ≤ (β : EReal) := by
  refine iSup_le fun u => ?_
  induction h' : φ u using EReal.rec with
  | bot => exact absurd h' (hbot u)
  | top => simp
  | coe r =>
    rw [← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (h u r (le_of_eq h'))


theorem c_nonpos (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (φ : WeakBilin B → EReal) (hbot : ∀ u, φ u ≠ ⊥)
    (hdom : ∃ u, φ u ≠ ⊤) (y : F) (c s : ℝ)
    (H : ∀ (u : WeakBilin B) (t : ℝ), φ u ≤ (t : EReal) → B u y + t * c < s) : c ≤ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨u₁, hu₁⟩ := hdom
  set t := max (φ u₁).toReal ((s - B u₁ y) / c)
  have ht : φ u₁ ≤ (t : EReal) := by
    rw [← EReal.coe_toReal hu₁ (hbot u₁)]
    exact EReal.coe_le_coe_iff.mpr (le_max_left _ _)
  have h1 := H u₁ t ht
  have h2 : (s - B u₁ y) / c ≤ t := le_max_right _ _
  have h3 : s - B u₁ y ≤ t * c := by rwa [div_le_iff₀ hc] at h2
  linarith

theorem minor_of_neg (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (φ : WeakBilin B → EReal) (y : F) (c s : ℝ)
    (hc : c < 0)
    (H : ∀ (u : WeakBilin B) (t : ℝ), φ u ≤ (t : EReal) → B u y + t * c < s) :
    ∀ (u : WeakBilin B) (r : ℝ), φ u ≤ (r : EReal) → B u ((-c)⁻¹ • y) - r ≤ s / (-c) := by
  intro u r hr
  have h := H u r hr
  have hd : 0 < -c := by linarith
  rw [map_smul, smul_eq_mul, le_div_iff₀ hd]
  have hne : -c ≠ 0 := hd.ne'
  have : ((-c)⁻¹ * B u y - r) * -c = B u y + r * c := by
    rw [sub_mul, mul_comm ((-c)⁻¹), mul_assoc, inv_mul_cancel₀ hne]; ring
  rw [this]; exact h.le

theorem key (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (φ : WeakBilin B → EReal) (hbot : ∀ u, φ u ≠ ⊥)
    (hdom : ∃ u, φ u ≠ ⊤)
    (hconv : Convex ℝ {p : WeakBilin B × ℝ | φ p.1 ≤ (p.2 : EReal)})
    (hlsc : LowerSemicontinuous φ) (u₀ : WeakBilin B) (α : ℝ) (hα : (α : EReal) < φ u₀) :
    ∃ (y : F) (β : ℝ), (∀ (u : WeakBilin B) (r : ℝ), φ u ≤ (r : EReal) → B u y - r ≤ β) ∧
      α ≤ B u₀ y - β := by
  obtain ⟨y, c, s, H1, H2⟩ := sep B φ hconv hlsc u₀ α (not_le.mpr hα)
  have hc := c_nonpos B φ hbot hdom y c s H1
  rcases hc.lt_or_eq with hc | hc
  · refine ⟨(-c)⁻¹ • y, s / (-c), minor_of_neg B φ y c s hc H1, ?_⟩
    have hd : 0 < -c := by linarith
    rw [map_smul, smul_eq_mul]
    have : (-c)⁻¹ * B u₀ y - s / -c = (B u₀ y - s) / (-c) := by ring
    rw [this, le_div_iff₀ hd]
    linarith
  · subst hc
    -- an affine minorant from a point of the effective domain
    obtain ⟨u₁, hu₁⟩ := hdom
    set r₁ := (φ u₁).toReal
    have hr₁ : φ u₁ = (r₁ : EReal) := (EReal.coe_toReal hu₁ (hbot u₁)).symm
    have hα₁ : ¬ φ u₁ ≤ ((r₁ - 1 : ℝ) : EReal) := by
      rw [hr₁, EReal.coe_le_coe_iff]; linarith
    obtain ⟨y₁, c₁, s₁, H1', H2'⟩ := sep B φ hconv hlsc u₁ (r₁ - 1) hα₁
    have hc₁ := c_nonpos B φ hbot ⟨u₁, hu₁⟩ y₁ c₁ s₁ H1'
    have hc₁' : c₁ < 0 := by
      rcases hc₁.lt_or_eq with h | h
      · exact h
      · subst h
        have := H1' u₁ r₁ hr₁.le
        linarith
    have M := minor_of_neg B φ y₁ c₁ s₁ hc₁' H1'
    set y₁' := (-c₁)⁻¹ • y₁
    set β₁ := s₁ / (-c₁)
    have hg : 0 < B u₀ y - s := by linarith
    set k := max 0 ((α - B u₀ y₁' + β₁) / (B u₀ y - s))
    have hk0 : 0 ≤ k := le_max_left _ _
    have hk : α - B u₀ y₁' + β₁ ≤ k * (B u₀ y - s) := by
      have := le_max_right 0 ((α - B u₀ y₁' + β₁) / (B u₀ y - s))
      rwa [div_le_iff₀ hg] at this
    refine ⟨y₁' + k • y, β₁ + k * s, fun u r hr => ?_, ?_⟩
    · have h1 := M u r hr
      have h2 := H1 u r hr
      have e : B u (y₁' + k • y) = B u y₁' + k * B u y := by
        simp only [y₁', map_add, map_smul, smul_eq_mul]
      rw [e]
      have : k * B u y ≤ k * s := mul_le_mul_of_nonneg_left (by linarith) hk0
      linarith
    · have e : B u₀ (y₁' + k • y) = B u₀ y₁' + k * B u₀ y := by
        simp only [y₁', map_add, map_smul, smul_eq_mul]
      rw [e]
      linarith

/-- Fenchel–Moreau for a weak dual pair. -/
theorem fenchel_moreau (B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ) (φ : WeakBilin B → EReal) (hbot : ∀ u, φ u ≠ ⊥)
    (hdom : ∃ u, φ u ≠ ⊤)
    (hconv : Convex ℝ {p : WeakBilin B × ℝ | φ p.1 ≤ (p.2 : EReal)})
    (hlsc : LowerSemicontinuous φ) (u₀ : WeakBilin B) :
    (⨆ y, ((B u₀ y : ℝ) : EReal) - ⨆ u, ((B u y : ℝ) : EReal) - φ u) = φ u₀ := by
  apply le_antisymm
  · refine iSup_le fun y => ?_
    induction h' : φ u₀ using EReal.rec with
    | bot => exact absurd h' (hbot u₀)
    | top => exact le_top
    | coe r =>
      have h1 : ((B u₀ y - r : ℝ) : EReal) ≤ ⨆ u, ((B u y : ℝ) : EReal) - φ u := by
        refine le_trans ?_ (le_iSup _ u₀)
        rw [h', EReal.coe_sub]
      calc ((B u₀ y : ℝ) : EReal) - ⨆ u, ((B u y : ℝ) : EReal) - φ u
          ≤ ((B u₀ y : ℝ) : EReal) - ((B u₀ y - r : ℝ) : EReal) := EReal.sub_le_sub le_rfl h1
        _ = (r : EReal) := by rw [← EReal.coe_sub]; congr 1; ring
  · by_contra hlt
    push_neg at hlt
    obtain ⟨α, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    obtain ⟨y, β, hM, hb⟩ := key B φ hbot hdom hconv hlsc u₀ α h2
    have hconj := conj_le B φ hbot y β hM
    have : (α : EReal) ≤ ⨆ y, ((B u₀ y : ℝ) : EReal) - ⨆ u, ((B u y : ℝ) : EReal) - φ u := by
      refine le_trans ?_ (le_iSup _ y)
      calc (α : EReal) ≤ ((B u₀ y - β : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hb
        _ = ((B u₀ y : ℝ) : EReal) - (β : EReal) := EReal.coe_sub _ _
        _ ≤ _ := EReal.sub_le_sub le_rfl hconj
    exact absurd h1 (not_lt.mpr this)

end SCPFM

namespace SCPFMU

open MeasureTheory StochConvexProg.Duality

theorem integrable_dot {S : Type*} [MeasurableSpace S] {σ : Measure S} {m : ℕ}
    (f : Lp (Fin m → ℝ) ⊤ σ) (g : Lp (Fin m → ℝ) 1 σ) :
    Integrable (fun s => f s ⬝ᵥ g s) σ := by
  simp only [dotProduct]
  refine integrable_finset_sum _ fun i _ => ?_
  have hg : Integrable (fun s => g s i) σ :=
    memLp_one_iff_integrable.1 ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).comp_memLp g)
  have hf : MemLp (fun s => f s i) ⊤ σ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) i).comp_memLp f
  exact hg.mul_of_top_right hf

/-- The pairing (1.6) as a bilinear map. -/
noncomputable def Bp {S : Type*} [MeasurableSpace S] (σ : Measure S) (m₁ m₂ : ℕ) :
    USpace σ m₁ m₂ →ₗ[ℝ] YSpace σ m₁ m₂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u y => pairUY u y)
    (fun u u' y => by
      simp only [pairUY, Prod.fst_add, Prod.snd_add, add_dotProduct]
      have : ∫ s, (u.2 + u'.2 : Lp (Fin m₂ → ℝ) ⊤ σ) s ⬝ᵥ y.2 s ∂σ =
          ∫ s, (u.2 s ⬝ᵥ y.2 s + u'.2 s ⬝ᵥ y.2 s) ∂σ := by
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add u.2 u'.2] with s hs
        rw [hs, Pi.add_apply, add_dotProduct]
      rw [this, integral_add (integrable_dot _ _) (integrable_dot _ _)]
      ring)
    (fun c u y => by
      simp only [pairUY, Prod.smul_fst, Prod.smul_snd, smul_dotProduct, smul_eq_mul]
      have : ∫ s, (c • u.2 : Lp (Fin m₂ → ℝ) ⊤ σ) s ⬝ᵥ y.2 s ∂σ =
          ∫ s, c * (u.2 s ⬝ᵥ y.2 s) ∂σ := by
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c u.2] with s hs
        rw [hs, Pi.smul_apply, smul_dotProduct, smul_eq_mul]
      rw [this, integral_const_mul]
      ring)
    (fun u y y' => by
      simp only [pairUY, Prod.fst_add, Prod.snd_add, dotProduct_add]
      have : ∫ s, u.2 s ⬝ᵥ (y.2 + y'.2 : Lp (Fin m₂ → ℝ) 1 σ) s ∂σ =
          ∫ s, (u.2 s ⬝ᵥ y.2 s + u.2 s ⬝ᵥ y'.2 s) ∂σ := by
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add y.2 y'.2] with s hs
        rw [hs, Pi.add_apply, dotProduct_add]
      rw [this, integral_add (integrable_dot _ _) (integrable_dot _ _)]
      ring)
    (fun c u y => by
      simp only [pairUY, Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_eq_mul]
      have : ∫ s, u.2 s ⬝ᵥ (c • y.2 : Lp (Fin m₂ → ℝ) 1 σ) s ∂σ =
          ∫ s, c * (u.2 s ⬝ᵥ y.2 s) ∂σ := by
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c y.2] with s hs
        rw [hs, Pi.smul_apply, dotProduct_smul, smul_eq_mul]
      rw [this, integral_const_mul]
      ring)

theorem top_eq {S : Type*} [MeasurableSpace S] (σ : Measure S) (m₁ m₂ : ℕ) :
    (WeakBilin.instTopologicalSpace (Bp σ m₁ m₂) : TopologicalSpace (USpace σ m₁ m₂)) =
      weakU σ m₁ m₂ := by
  simp only [WeakBilin.instTopologicalSpace, Pi.topologicalSpace, induced_iInf, induced_compose,
    weakU]
  rfl

end SCPFMU

open MeasureTheory StochConvexProg.Duality in
theorem solution {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {m₁ m₂ : ℕ} (φ : USpace σ m₁ m₂ → EReal)
    (hproper : EProper φ) (hconv : EConvex φ)
    (hlsc : @LowerSemicontinuous (USpace σ m₁ m₂) EReal (weakU σ m₁ m₂) _ φ) :
    biconjU φ = φ := by
  funext u₀
  have hlsc' : @LowerSemicontinuous (USpace σ m₁ m₂) EReal
      (WeakBilin.instTopologicalSpace (SCPFMU.Bp σ m₁ m₂)) _ φ :=
    (SCPFMU.top_eq σ m₁ m₂) ▸ hlsc
  exact SCPFM.fenchel_moreau (SCPFMU.Bp σ m₁ m₂) φ hproper.1 hproper.2 hconv hlsc' u₀
