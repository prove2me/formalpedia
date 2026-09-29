-- Prove2me | solution 1 for Representation.exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/6ebeb626-9cff-5d01-a596-d2d8fce4d7ee

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing

set_option autoImplicit false

p2m_open "LinearMap P2MW.S_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing.LinearMap"

namespace CTEDev

variable {A : Type} [CommRing A] {G : Type} [Monoid G]
variable {V₁ V₂ : Type}
  [AddCommGroup V₁] [Module A V₁] [Module.Free A V₁] [Module.Finite A V₁]
  [AddCommGroup V₂] [Module A V₂] [Module.Free A V₂] [Module.Finite A V₂]

theorem end_eq_zero_of_forall_trace_mul_eq_zero
    (X : Module.End A V₁) (h : ∀ Y : Module.End A V₁, LinearMap.trace A V₁ (X * Y) = 0) :
    X = 0 := by
  classical
  let b := Module.Free.chooseBasis A V₁
  apply (LinearMap.toMatrix b b).injective
  rw [map_zero, Matrix.ext_iff_trace_mul_right]
  intro x
  have hY := h (Matrix.toLin b b x)
  rw [LinearMap.trace_eq_matrix_trace A b] at hY
  have hcomp : X * Matrix.toLin b b x = X ∘ₗ Matrix.toLin b b x := rfl
  rw [hcomp, LinearMap.toMatrix_comp b b b, LinearMap.toMatrix_toLin] at hY
  simp [hY]

theorem end_eq_of_forall_trace_mul_eq
    (ρ : G →* Module.End A V₁) (hspan : Submodule.span A (Set.range ⇑ρ) = ⊤)
    (ψ ψ' : Module.End A V₁)
    (h : ∀ g : G, LinearMap.trace A V₁ (ψ * ρ g) = LinearMap.trace A V₁ (ψ' * ρ g)) :
    ψ = ψ' := by
  rw [← sub_eq_zero]
  apply end_eq_zero_of_forall_trace_mul_eq_zero
  intro Y
  set T : Module.End A V₁ →ₗ[A] A :=
    (LinearMap.trace A V₁).comp (LinearMap.mulLeft A (ψ - ψ')) with hT
  have hgen : ∀ g : G, T (ρ g) = 0 := by
    intro g
    simp only [hT, LinearMap.comp_apply, LinearMap.mulLeft_apply, sub_mul, map_sub]
    rw [sub_eq_zero]
    exact h g
  have hle : Submodule.span A (Set.range ⇑ρ) ≤ LinearMap.ker T :=
    Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; simpa [LinearMap.mem_ker] using hgen g)
  have hker : LinearMap.ker T = ⊤ := top_unique (hspan ▸ hle)
  have hT0 : T = 0 := LinearMap.ker_eq_top.mp hker
  have := congrArg (fun (f : Module.End A V₁ →ₗ[A] A) => f Y) hT0
  simpa [hT] using this

omit [Module.Free A V₁] [Module.Finite A V₁] in

theorem exists_pairing_linearMap
    (ρ₁ : G →* Module.End A V₁) (ρ₂ : G →* Module.End A V₂)
    (hspan₁ : Submodule.span A (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span A (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g : G, LinearMap.trace A V₁ (ρ₁ g) = LinearMap.trace A V₂ (ρ₂ g)) :
    ∃ α : Module.End A V₁ →ₗ[A] Module.End A V₂,
      (∀ g : G, α (ρ₁ g) = ρ₂ g) ∧
      ∀ (φ : Module.End A V₁) (h : G),
        LinearMap.trace A V₂ (α φ * ρ₂ h) = LinearMap.trace A V₁ (φ * ρ₁ h) := by
  classical
  set R : Submodule A (Module.End A V₁ × Module.End A V₂) :=
    Submodule.span A (Set.range fun g => (ρ₁ g, ρ₂ g)) with hR
  have hpairR : ∀ x ∈ R, ∀ h : G,
      LinearMap.trace A V₁ (x.1 * ρ₁ h) = LinearMap.trace A V₂ (x.2 * ρ₂ h) := by
    intro x hx h
    set L : (Module.End A V₁ × Module.End A V₂) →ₗ[A] A :=
      ((LinearMap.trace A V₁).comp ((LinearMap.mulRight A (ρ₁ h)).comp
          (LinearMap.fst A (Module.End A V₁) (Module.End A V₂))))
        - ((LinearMap.trace A V₂).comp ((LinearMap.mulRight A (ρ₂ h)).comp
          (LinearMap.snd A (Module.End A V₁) (Module.End A V₂)))) with hL
    have hgen : ∀ g : G, L (ρ₁ g, ρ₂ g) = 0 := by
      intro g
      simp only [hL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, LinearMap.mulRight_apply]
      rw [sub_eq_zero, ← map_mul, ← map_mul, htr]
    have hle : R ≤ LinearMap.ker L := by
      rw [hR]
      exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; simpa [LinearMap.mem_ker] using hgen g)
    have h0 := hle hx
    simp only [LinearMap.mem_ker, hL, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.mulRight_apply, sub_eq_zero] at h0
    exact h0
  have hsurj : ∀ φ : Module.End A V₁, ∃ ψ, (φ, ψ) ∈ R := by
    intro φ
    have hmap : R.map (LinearMap.fst A (Module.End A V₁) (Module.End A V₂)) = ⊤ := by
      rw [hR, Submodule.map_span, ← Set.range_comp]
      have hfun : (⇑(LinearMap.fst A (Module.End A V₁) (Module.End A V₂)) ∘
          fun g => (ρ₁ g, ρ₂ g)) = ⇑ρ₁ := rfl
      rw [hfun]
      exact hspan₁
    have hφ : φ ∈ R.map (LinearMap.fst A (Module.End A V₁) (Module.End A V₂)) :=
      hmap ▸ Submodule.mem_top
    obtain ⟨x, hxR, hx1⟩ := hφ
    subst hx1
    exact ⟨x.2, hxR⟩
  choose f hf using hsurj
  have hfpair : ∀ (φ : Module.End A V₁) (h : G),
      LinearMap.trace A V₂ (f φ * ρ₂ h) = LinearMap.trace A V₁ (φ * ρ₁ h) :=
    fun φ h => (hpairR _ (hf φ) h).symm
  have funiq : ∀ (φ : Module.End A V₁) (ψ : Module.End A V₂), (φ, ψ) ∈ R → f φ = ψ := by
    intro φ ψ hψ
    apply end_eq_of_forall_trace_mul_eq ρ₂ hspan₂
    intro g
    rw [hfpair φ g]
    exact hpairR _ hψ g
  have hadd : ∀ φ φ', f (φ + φ') = f φ + f φ' := by
    intro φ φ'
    exact funiq _ _ (R.add_mem (hf φ) (hf φ'))
  have hsmul : ∀ (a : A) (φ), f (a • φ) = a • f φ := by
    intro a φ
    exact funiq _ _ (R.smul_mem a (hf φ))
  refine ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, ?_, ?_⟩
  · intro g
    exact funiq _ _ (Submodule.subset_span ⟨g, rfl⟩)
  · intro φ h
    exact hfpair φ h

theorem exists_algEquiv_of_span_range_eq_top_of_trace_eq
    (ρ₁ : G →* Module.End A V₁) (ρ₂ : G →* Module.End A V₂)
    (hspan₁ : Submodule.span A (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span A (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g : G, LinearMap.trace A V₁ (ρ₁ g) = LinearMap.trace A V₂ (ρ₂ g)) :
    ∃ α : Module.End A V₁ ≃ₐ[A] Module.End A V₂,
      (∀ g : G, α (ρ₁ g) = ρ₂ g) ∧
      ∀ φ : Module.End A V₁, LinearMap.trace A V₂ (α φ) = LinearMap.trace A V₁ φ := by
  obtain ⟨α₀, hαgen, hαpair⟩ := exists_pairing_linearMap ρ₁ ρ₂ hspan₁ hspan₂ htr
  obtain ⟨β₀, hβgen, hβpair⟩ :=
    exists_pairing_linearMap ρ₂ ρ₁ hspan₂ hspan₁ (fun g => (htr g).symm)
  have huniq₁ := end_eq_of_forall_trace_mul_eq ρ₁ hspan₁
  have huniq₂ := end_eq_of_forall_trace_mul_eq ρ₂ hspan₂
  have hβα : ∀ φ, β₀ (α₀ φ) = φ := by
    intro φ
    apply huniq₁
    intro g
    rw [hβpair, hαpair]
  have hαβ : ∀ ψ, α₀ (β₀ ψ) = ψ := by
    intro ψ
    apply huniq₂
    intro g
    rw [hαpair, hβpair]
  have hM1 : ∀ (χ : Module.End A V₁) (h : G), α₀ χ * ρ₂ h = α₀ (χ * ρ₁ h) := by
    intro χ h
    apply huniq₂
    intro k
    calc LinearMap.trace A V₂ ((α₀ χ * ρ₂ h) * ρ₂ k)
        = LinearMap.trace A V₂ (α₀ χ * ρ₂ (h * k)) := by
          rw [mul_assoc, ← map_mul ρ₂ h k]
      _ = LinearMap.trace A V₁ (χ * ρ₁ (h * k)) := hαpair χ (h * k)
      _ = LinearMap.trace A V₁ ((χ * ρ₁ h) * ρ₁ k) := by
          rw [map_mul ρ₁ h k, mul_assoc]
      _ = LinearMap.trace A V₂ (α₀ (χ * ρ₁ h) * ρ₂ k) := (hαpair _ k).symm
  have hT2 : ∀ (φ χ : Module.End A V₁),
      LinearMap.trace A V₂ (α₀ φ * α₀ χ) = LinearMap.trace A V₁ (φ * χ) := by
    intro φ χ
    set L : Module.End A V₁ →ₗ[A] A :=
      ((LinearMap.trace A V₂).comp ((LinearMap.mulLeft A (α₀ φ)).comp α₀))
        - ((LinearMap.trace A V₁).comp (LinearMap.mulLeft A φ)) with hL
    have hgen : ∀ g : G, L (ρ₁ g) = 0 := by
      intro g
      simp only [hL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
      rw [hαgen, hαpair, sub_self]
    have hle : Submodule.span A (Set.range ⇑ρ₁) ≤ LinearMap.ker L :=
      Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; simpa [LinearMap.mem_ker] using hgen g)
    have hker : LinearMap.ker L = ⊤ := top_unique (hspan₁ ▸ hle)
    have hL0 : L χ = 0 := by
      have hχ : χ ∈ LinearMap.ker L := hker ▸ Submodule.mem_top
      simpa [LinearMap.mem_ker] using hχ
    simp only [hL, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      sub_eq_zero] at hL0
    exact hL0
  have hmul : ∀ φ χ : Module.End A V₁, α₀ (φ * χ) = α₀ φ * α₀ χ := by
    intro φ χ
    apply huniq₂
    intro k
    calc LinearMap.trace A V₂ (α₀ (φ * χ) * ρ₂ k)
        = LinearMap.trace A V₁ ((φ * χ) * ρ₁ k) := hαpair _ k
      _ = LinearMap.trace A V₁ (φ * (χ * ρ₁ k)) := by rw [mul_assoc]
      _ = LinearMap.trace A V₂ (α₀ φ * α₀ (χ * ρ₁ k)) := (hT2 _ _).symm
      _ = LinearMap.trace A V₂ (α₀ φ * (α₀ χ * ρ₂ k)) := by rw [hM1]
      _ = LinearMap.trace A V₂ ((α₀ φ * α₀ χ) * ρ₂ k) := by rw [mul_assoc]
  have hcompαβ : α₀ ∘ₗ β₀ = LinearMap.id :=
    LinearMap.ext fun ψ => hαβ ψ
  have hcompβα : β₀ ∘ₗ α₀ = LinearMap.id :=
    LinearMap.ext fun φ => hβα φ
  set eLin : Module.End A V₁ ≃ₗ[A] Module.End A V₂ :=
    LinearEquiv.ofLinear α₀ β₀ hcompαβ hcompβα with heLin
  have heq : ∀ x : Module.End A V₁, eLin x = α₀ x := by
    intro x
    rw [heLin, LinearEquiv.ofLinear_apply]
  have hone : eLin (1 : Module.End A V₁) = 1 := by
    rw [heq, ← map_one ρ₁, hαgen, map_one ρ₂]
  have hmul' : ∀ φ χ : Module.End A V₁, eLin (φ * χ) = eLin φ * eLin χ := by
    intro φ χ
    rw [heq, heq, heq]
    exact hmul φ χ
  refine ⟨AlgEquiv.ofLinearEquiv eLin hone hmul', fun g => ?_, fun φ => ?_⟩
  · rw [AlgEquiv.ofLinearEquiv_apply, heq]
    exact hαgen g
  · rw [AlgEquiv.ofLinearEquiv_apply, heq]
    have htr1 := hαpair φ 1
    rw [map_one ρ₁, map_one ρ₂, mul_one, mul_one] at htr1
    exact htr1

end CTEDev

open Module

namespace CarayolSN

variable {A : Type} [CommRing A]
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module A V₁] [AddCommGroup V₂] [Module A V₂]
  {ι : Type}

noncomputable def E (b : Basis ι A V₁) (i j : ι) : Module.End A V₁ :=
  (b.coord j).smulRight (b i)

theorem E_apply (b : Basis ι A V₁) (i j : ι) (v : V₁) : E b i j v = b.repr v j • b i := rfl

theorem E_apply_basis [DecidableEq ι] (b : Basis ι A V₁) (i j k : ι) :
    E b i j (b k) = if k = j then b i else 0 := by
  rw [E_apply, b.repr_self, Finsupp.single_apply]
  split_ifs <;> simp

theorem mul_E [Fintype ι] (b : Basis ι A V₁) (φ : Module.End A V₁) (i i₀ : ι) :
    φ * E b i i₀ = ∑ j, b.repr (φ (b i)) j • E b j i₀ := by
  refine b.ext fun k => ?_
  simp only [Module.End.mul_apply, E_apply, map_smul, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.smul_apply]
  simp_rw [smul_comm (b.repr (φ (b i)) _) (b.repr (b k) i₀) (b _), ← Finset.smul_sum]
  rw [b.sum_repr]

theorem sum_E [Fintype ι] (b : Basis ι A V₁) : ∑ i, E b i i = 1 := by
  refine b.ext fun k => ?_
  simp only [LinearMap.coe_sum, Finset.sum_apply, E_apply, Module.End.one_apply]
  rw [b.sum_repr]

theorem E_mul_E_mul_E [DecidableEq ι] (b : Basis ι A V₁) (i i₀ : ι) :
    E b i i₀ * E b i₀ i₀ * E b i₀ i = E b i i := by
  refine b.ext fun k => ?_
  simp only [Module.End.mul_apply, E_apply_basis]
  split_ifs <;> simp [E_apply_basis]

variable (b : Basis ι A V₁) (α : Module.End A V₁ →ₐ[A] Module.End A V₂) (i₀ : ι)

noncomputable def eOf (w : V₂) : V₁ →ₗ[A] V₂ := b.constr A fun i => α (E b i i₀) w

theorem eOf_basis (w : V₂) (i : ι) : eOf b α i₀ w (b i) = α (E b i i₀) w := by
  simp [eOf, b.constr_basis]

theorem eOf_intertwines [Fintype ι] (w : V₂) (φ : Module.End A V₁) (v : V₁) :
    eOf b α i₀ w (φ v) = α φ (eOf b α i₀ w v) := by
  suffices h : eOf b α i₀ w ∘ₗ φ = α φ ∘ₗ eOf b α i₀ w from LinearMap.congr_fun h v
  refine b.ext fun i => ?_
  simp only [LinearMap.comp_apply, eOf_basis]
  rw [← Module.End.mul_apply, ← map_mul, mul_E, map_sum, LinearMap.coe_sum, Finset.sum_apply]
  conv_lhs => rw [← b.sum_repr (φ (b i))]
  simp only [map_sum, map_smul, eOf_basis, LinearMap.smul_apply]

theorem eOf_surjective [Fintype ι] (hα : Function.Surjective α) (w : V₂) (l : V₂ →ₗ[A] A)
    (hl : l (α (E b i₀ i₀) w) = 1) : Function.Surjective (eOf b α i₀ w) := by
  intro v
  obtain ⟨φ, hφ⟩ := hα (l.smulRight v)
  refine ⟨φ (b i₀), ?_⟩
  rw [eOf_intertwines, eOf_basis, hφ, LinearMap.smulRight_apply, hl, one_smul]

theorem exists_unit [Fintype ι] [DecidableEq ι] [IsLocalRing A] {κ : Type} (b₂ : Basis κ A V₂) (j₀ : κ) :
    ∃ (w : V₂) (l : V₂ →ₗ[A] A), IsUnit (l (α (E b i₀ i₀) w)) := by
  by_contra! H
  have key : ∀ (w : V₂) (l : V₂ →ₗ[A] A), l (α (E b i₀ i₀) w) ∈ IsLocalRing.maximalIdeal A :=
    fun w l => (IsLocalRing.mem_maximalIdeal _).mpr (H w l)
  apply (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : A) = b₂.coord j₀ ((α 1) (b₂ j₀)) := by
    rw [map_one, Module.End.one_apply, Basis.coord_apply, b₂.repr_self, Finsupp.single_eq_same]
  rw [h1, ← sum_E b, map_sum, LinearMap.coe_sum, Finset.sum_apply, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← E_mul_E_mul_E b i i₀, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  exact key _ (b₂.coord j₀ ∘ₗ α (E b i i₀))

end CarayolSN

namespace LinearMap p2m_export "LinearMap" "mulLeft_apply single_apply toMatrix range sub_apply rank trace_eq_matrix_trace id sum_apply snd toMatrix_toLin coe_sum module smulRight_apply range_comp map_span fst_apply smulRight smul_apply mulLeft fst ker_eq_top ext toMatrix_comp comp trace mulRight_apply ker snd_apply mem_ker comp_apply mulRight" end LinearMap
p2m_open_scoped "LinearMap" in
open CarayolSN in

theorem LinearMap.exists_linearEquiv_of_algHom_surjective_of_isLocalRing
    {A : Type} [CommRing A] [IsLocalRing A] {V₁ V₂ : Type}
    [AddCommGroup V₁] [Module A V₁] [Module.Free A V₁] [Module.Finite A V₁]
    [AddCommGroup V₂] [Module A V₂] [Module.Free A V₂] [Module.Finite A V₂]
    (hrank : Module.finrank A V₁ = Module.finrank A V₂)
    (α : Module.End A V₁ →ₐ[A] Module.End A V₂) (hα : Function.Surjective α) :
    ∃ e : V₁ ≃ₗ[A] V₂, ∀ (φ : Module.End A V₁) (v : V₁), e (φ v) = α φ (e v) := by
  classical
  rcases Nat.eq_zero_or_eq_succ_pred (Module.finrank A V₁) with h0 | hpos
  ·
    have b := Module.finBasisOfFinrankEq A V₁ h0
    have : Subsingleton V₁ := b.repr.toEquiv.subsingleton
    refine ⟨LinearEquiv.ofFinrankEq V₁ V₂ hrank, fun φ v => ?_⟩
    rw [Subsingleton.elim v 0, map_zero, map_zero, map_zero]
  · set n := (Module.finrank A V₁).pred
    let b := Module.finBasisOfFinrankEq A V₁ hpos
    let b₂ := Module.finBasisOfFinrankEq A V₂ (hrank ▸ hpos)
    obtain ⟨w, l, hu⟩ := exists_unit b α 0 b₂ 0
    obtain ⟨u, hu⟩ := hu

    have hl : ((↑u⁻¹ : A) • l) (α (E b 0 0) w) = 1 := by
      rw [LinearMap.smul_apply, ← hu, smul_eq_mul, Units.inv_mul]
    have hsurj := eOf_surjective b α 0 hα w _ hl
    have hinj : Function.Injective (eOf b α 0 w) := by
      have := OrzechProperty.injective_of_surjective_endomorphism
        ((LinearEquiv.ofFinrankEq V₂ V₁ hrank.symm).toLinearMap ∘ₗ eOf b α 0 w)
        ((LinearEquiv.ofFinrankEq V₂ V₁ hrank.symm).surjective.comp hsurj)
      exact Function.Injective.of_comp this
    exact ⟨LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩, fun φ v => eOf_intertwines b α 0 w φ v⟩

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] {G : Type} [Monoid G]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module A V₁] [Module.Free A V₁] [Module.Finite A V₁]
    [AddCommGroup V₂] [Module A V₂] [Module.Free A V₂] [Module.Finite A V₂]
    (ρ₁ : G →* Module.End A V₁) (ρ₂ : G →* Module.End A V₂)
    (hrank : Module.finrank A V₁ = Module.finrank A V₂)
    (hspan₁ : Submodule.span A (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span A (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g : G, LinearMap.trace A V₁ (ρ₁ g) = LinearMap.trace A V₂ (ρ₂ g)) :
    ∃ e : V₁ ≃ₗ[A] V₂, ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v) := by
  obtain ⟨α, hαρ, _⟩ :=
    CTEDev.exists_algEquiv_of_span_range_eq_top_of_trace_eq ρ₁ ρ₂ hspan₁ hspan₂ htr
  obtain ⟨e, he⟩ := LinearMap.exists_linearEquiv_of_algHom_surjective_of_isLocalRing
    hrank α.toAlgHom α.surjective
  exact ⟨e, fun g v ↦ by rw [he (ρ₁ g) v]; simp [hαρ g]⟩

end S_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
end P2MW
export P2MW.S_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing (solution)
