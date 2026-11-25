-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_of_isDiscreteValuationRing_315fc3a6886b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:30.096497+00:00
-- url     : https://prove2.me/submissions/11b1a1b4-54ae-4da8-9575-af7b7b4a4295

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_GradientAtPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModelPlace
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_SmoothOfRegular
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_JacobianAtCurvePoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianAtCurvePoint_exists_mul_mem_of_algebraMap_mem_ad35f2d7d286
import Theorems.Thm_GroundTheory_Arith_Jacobian_ker_le_span_of_spanFinrank_le
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_X_sub_C_9853297c8fca
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_apply_6330d6b8766e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_eq_zero_of_mem_sq_d16d44a9d73b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_grad_mul_of_eval_eq_zero_a46392587438
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_ker_eval_eq_span_c590d7c396ab
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GradientAtPoint_mem_sq_of_grad_eq_zero_7cd8970785ba


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial IsLocalRing GradientAtPoint
noncomputable section
open GroundTheory.Heights₂.Heights.JacobianAtCurvePoint
variable {σ : Type}
variable [Fintype σ]
namespace GroundTheory.Heights₂.Heights.JacobianAtCurvePoint
theorem _root_.solution (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) (S : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra (ptLoc w) S] [Algebra (MvPolynomial σ ℂ) S] [IsScalarTower (MvPolynomial σ ℂ) (ptLoc w) S]
    (hsurj : Function.Surjective (algebraMap (ptLoc w) S))
    (hker : RingHom.ker (algebraMap (ptLoc w) S) = ptIdeal I w) :
    ∃ (k : ℕ) (f : Fin k → MvPolynomial σ ℂ) (D : MvPolynomial σ ℂ),
      k + 1 = Fintype.card σ ∧ (∀ j, f j ∈ I) ∧
        LinearIndependent ℂ (fun j (i : σ) => eval w (pderiv i (f j))) ∧
        eval w D ≠ 0 ∧ ∀ p ∈ I, D * p ∈ Ideal.span (Set.range f) := by
  classical
  have hRS : ∀ y, algebraMap (MvPolynomial σ ℂ) S y =
      algebraMap (ptLoc w) S (algebraMap _ (ptLoc w) y) := fun y => IsScalarTower.algebraMap_apply _ _ _ y
  have hIm : I ≤ ptMax w := fun q hq => RingHom.mem_ker.2 (hw q hq)
  have hmax : (ptMax w).IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C _⟩)

  have hcomapPS : (maximalIdeal S).comap (algebraMap (ptLoc w) S) = maximalIdeal (ptLoc w) :=
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hsurj)
  have hmap : (ptMax w).map (algebraMap _ S) = maximalIdeal S := by
    rw [IsScalarTower.algebraMap_eq (MvPolynomial σ ℂ) (ptLoc w) S, ← Ideal.map_map,
      Localization.AtPrime.map_eq_maximalIdeal, ← hcomapPS, Ideal.map_comap_of_surjective _ hsurj]
  have hcomap : (maximalIdeal S).comap (algebraMap _ S) = ptMax w :=
    (hmax.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal S).ne_top)
      (hmap ▸ Ideal.le_comap_map)).symm
  have hunit : ∀ s : MvPolynomial σ ℂ, eval w s ≠ 0 → IsUnit (algebraMap _ S s) := by
    intro s hs
    rw [hRS]
    exact (IsLocalization.map_units (ptLoc w) (⟨s, fun h => hs (RingHom.mem_ker.1 h)⟩ :
      (ptMax w).primeCompl)).map _
  have hspec : ∀ (a : MvPolynomial σ ℂ) (s : (ptMax w).primeCompl),
      algebraMap (ptLoc w) S (IsLocalization.mk' (ptLoc w) a s) *
        algebraMap _ S (s : MvPolynomial σ ℂ) = algebraMap _ S a := by
    intro a s
    rw [hRS, hRS, ← map_mul, IsLocalization.mk'_spec]

  set V : Submodule ℂ (σ → ℂ) := (I.restrictScalars ℂ).map (grad w) with hV

  have hQ : ∀ x : MvPolynomial σ ℂ, algebraMap _ S x ∈ maximalIdeal S ^ 2 →
      grad w x ∈ V := by
    intro x hx
    have hx' : algebraMap (ptLoc w) S (algebraMap _ (ptLoc w) x) ∈
        ((ptMax w ^ 2).map (algebraMap _ (ptLoc w))).map (algebraMap (ptLoc w) S) := by
      rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq, Ideal.map_pow, hmap, ← hRS]
      exact hx
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, hker, ptIdeal,
      ← Ideal.map_sup] at hx'
    obtain ⟨s, hs, hsx⟩ := exists_mul_mem_of_algebraMap_mem w _ x hx'
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hsx
    have hxm : eval w x = 0 := by
      have h1 : s * x ∈ ptMax w := sup_le (Ideal.pow_le_self two_ne_zero) hIm hsx
      rw [RingHom.mem_ker, map_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left hs
    have h2 : eval w s • grad w x = grad w z := by
      rw [← grad_mul_of_eval_eq_zero w s x hxm, ← hyz, map_add, grad_eq_zero_of_mem_sq w hy, zero_add]
    have h3 : grad w z ∈ V := ⟨z, hz, rfl⟩
    have h4 : grad w x = (eval w s)⁻¹ • grad w z := by
      rw [← h2, smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [h4]
    exact V.smul_mem _ h3

  have hVne : V ≠ ⊤ := by
    intro hVtop
    have hXi : ∀ i, algebraMap _ S (X i - C (w i)) ∈ maximalIdeal S ^ 2 := by
      intro i
      obtain ⟨p, hp, hpg⟩ : Pi.single i (1 : ℂ) ∈ V := hVtop ▸ Submodule.mem_top
      have hm : X i - C (w i) - p ∈ ptMax w :=
        Ideal.sub_mem _ (by simp [RingHom.mem_ker]) (hIm hp)
      have hg : grad w (X i - C (w i) - p) = 0 := by rw [map_sub, grad_X_sub_C, hpg, sub_self]
      have h2 := mem_sq_of_grad_eq_zero w hm hg
      have hp0 : algebraMap _ S p = 0 := by
        rw [hRS, ← RingHom.mem_ker, hker]
        exact Ideal.mem_map_of_mem _ hp
      rw [show X i - C (w i) = (X i - C (w i) - p) + p by ring, map_add, hp0, add_zero, ← hmap,
        ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ h2
    have hgen : maximalIdeal S =
        Ideal.span (Set.range fun i => algebraMap _ S (X i - C (w i))) := by
      rw [← hmap, show ptMax w = _ from ker_eval_eq_span w, Ideal.map_span, ← Set.range_comp]
      rfl
    have hle : maximalIdeal S ≤ maximalIdeal S • maximalIdeal S := by
      conv_lhs => rw [hgen]
      rw [Ideal.span_le, Ideal.smul_eq_mul, ← pow_two]
      rintro _ ⟨i, rfl⟩
      exact hXi i
    have hbot : maximalIdeal S = ⊥ :=
      Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal S) (maximalIdeal S) (IsNoetherian.noetherian _) hle
        (maximalIdeal_le_jacobson ⊥)
    exact IsDiscreteValuationRing.not_isField S (isField_iff_maximalIdeal_eq.2 hbot)

  have hres : ∀ b : S, ∃ c : ℂ, b - algebraMap (MvPolynomial σ ℂ) S (C c) ∈ maximalIdeal S := by
    intro b
    obtain ⟨p', rfl⟩ := hsurj b
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (ptMax w).primeCompl p'
    have hs : eval w (s : MvPolynomial σ ℂ) ≠ 0 := fun h => s.2 (RingHom.mem_ker.2 h)
    refine ⟨eval w a / eval w (s : MvPolynomial σ ℂ), ?_⟩
    have hmem : algebraMap _ S (a - C (eval w a / eval w (s : MvPolynomial σ ℂ)) * (s : MvPolynomial σ ℂ)) ∈
        maximalIdeal S := by
      rw [← Ideal.mem_comap, hcomap, RingHom.mem_ker, map_sub, map_mul, eval_C, div_mul_cancel₀ _ hs, sub_self]
    rw [← Ideal.mul_unit_mem_iff_mem _ (hunit _ hs), sub_mul, hspec, ← map_mul, ← map_sub]
    exact hmem

  obtain ⟨t, ht⟩ := (IsPrincipalIdealRing.principal (maximalIdeal S)).principal
  obtain ⟨p', rfl⟩ := hsurj t
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (ptMax w).primeCompl p'
  have hgena : maximalIdeal S = Ideal.span {algebraMap _ S a} := by
    rw [← hspec, Ideal.span_singleton_mul_right_unit (hunit _ fun h => s.2 (RingHom.mem_ker.2 h))]
    exact ht
  have hsup : ∀ i, Pi.single i (1 : ℂ) ∈ V ⊔ ℂ ∙ grad w a := by
    intro i
    have hi : algebraMap _ S (X i - C (w i)) ∈ maximalIdeal S := by
      rw [← Ideal.mem_comap, hcomap, RingHom.mem_ker]
      simp
    rw [hgena, Ideal.mem_span_singleton'] at hi
    obtain ⟨b, hb⟩ := hi
    obtain ⟨c, hc⟩ := hres b
    have h2 : algebraMap _ S (X i - C (w i) - C c * a) ∈ maximalIdeal S ^ 2 := by
      rw [map_sub, ← hb, map_mul, ← sub_mul, pow_two]
      exact Ideal.mul_mem_mul hc (by rw [hgena]; exact Ideal.mem_span_singleton_self _)
    have h3 := hQ _ h2
    rw [map_sub, grad_X_sub_C, C_mul', map_smul] at h3
    rw [show Pi.single i (1 : ℂ) = (Pi.single i 1 - c • grad w a) + c • grad w a by abel]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h3)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  have htop : V ⊔ ℂ ∙ grad w a = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℂ σ).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact hsup i

  obtain ⟨N, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (Ideal.fg_of_isNoetherianRing I)
  have hgI : ∀ j, g j ∈ I := fun j => hg ▸ Submodule.subset_span ⟨j, rfl⟩
  have hVg : V = Submodule.span ℂ (Set.range (grad w ∘ g)) := by
    apply le_antisymm
    · rintro _ ⟨p, hp, rfl⟩
      have hp' : p ∈ Ideal.span (Set.range g) := by rw [Ideal.span, hg]; exact hp
      obtain ⟨r, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hp'
      rw [map_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [grad_mul_of_eval_eq_zero w _ _ (RingHom.mem_ker.1 (hIm (hgI j)))]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨g j, hgI j, rfl⟩
  obtain ⟨κ, ι, hι, hspanι, hli⟩ := exists_linearIndependent' ℂ (grad w ∘ g)
  have : Finite κ := Finite.of_injective ι hι
  let := Fintype.ofFinite κ
  let e := Fintype.equivFin κ
  let f : Fin (Fintype.card κ) → MvPolynomial σ ℂ := g ∘ ι ∘ e.symm
  have hfI : ∀ j, f j ∈ I := fun j => hgI _
  have hlif' : LinearIndependent ℂ (grad w ∘ f) := hli.comp e.symm e.symm.injective
  have hlif : LinearIndependent ℂ (fun j (i : σ) => eval w (pderiv i (f j))) := by
    convert hlif' using 1
    funext j i
    simp [grad_apply]
  have hrange : Set.range (grad w ∘ f) = Set.range (grad w ∘ g ∘ ι) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨e.symm j, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨e j, by simp [f]⟩
  have hVf : V = Submodule.span ℂ (Set.range (grad w ∘ f)) := by
    rw [hVg, hrange, ← hspanι]
    rfl
  have hfinV : Module.finrank ℂ V = Fintype.card κ := by
    rw [hVf, finrank_span_eq_card hlif', Fintype.card_fin]

  have hcovR : I ≤ Ideal.span (Set.range f) ⊔ ptMax w ^ 2 := by
    intro p hp
    have hpV : grad w p ∈ V := ⟨p, hp, rfl⟩
    rw [hVf] at hpV
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hpV
    have hzm : p - ∑ j, C (c j) * f j ∈ ptMax w :=
      Ideal.sub_mem _ (hIm hp) (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hIm (hfI j)))
    have hzg : grad w (p - ∑ j, C (c j) * f j) = 0 := by
      rw [map_sub, map_sum]
      simp_rw [C_mul', map_smul]
      rw [← hc, sub_eq_zero]
      rfl
    have h2 := mem_sq_of_grad_eq_zero w hzm hzg
    rw [show p = (p - ∑ j, C (c j) * f j) + ∑ j, C (c j) * f j by ring]
    exact Ideal.add_mem _ (Ideal.mem_sup_right h2)
      (Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))

  have hcov : RingHom.ker (algebraMap (ptLoc w) S) ≤
      Ideal.span (Set.range (algebraMap _ (ptLoc w) ∘ f)) ⊔ maximalIdeal (ptLoc w) ^ 2 := by
    rw [hker, Set.range_comp, ← Ideal.map_span, ← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
      ← Ideal.map_sup]
    exact Ideal.map_mono hcovR
  have hfker : ∀ j, (algebraMap _ (ptLoc w) ∘ f) j ∈ RingHom.ker (algebraMap (ptLoc w) S) :=
    fun j => by rw [hker]; exact Ideal.mem_map_of_mem _ (hfI j)
  have hμ : (maximalIdeal S).spanFinrank ≤ 1 := by
    rw [hgena]
    calc (Ideal.span {algebraMap _ S a}).spanFinrank
        ≤ ({algebraMap _ S a} : Set S).ncard :=
          Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton _)
      _ = 1 := Set.ncard_singleton _
  have hdim : ((1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim S := by
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one]
    simp
  have hIP := GroundTheory.Arith.Jacobian.ker_le_span_of_spanFinrank_le (P := ptLoc w) (S := S)
    hsurj (algebraMap _ (ptLoc w) ∘ f) hfker hcov 1 hμ hdim

  have hden : ∀ j, ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * g j ∈ Ideal.span (Set.range f) := by
    intro j
    apply exists_mul_mem_of_algebraMap_mem w
    rw [Ideal.map_span, ← Set.range_comp]
    exact hIP (by rw [hker]; exact Ideal.mem_map_of_mem _ (hgI j))
  choose s hs0 hsg using hden
  refine ⟨Fintype.card κ, f, ∏ j, s j, ?_, hfI, hlif, ?_, ?_⟩
  · have h1 : Fintype.card κ < Fintype.card σ := by
      have := Submodule.finrank_lt hVne
      rwa [hfinV, Module.finrank_fintype_fun_eq_card] at this
    have h2 : Fintype.card σ ≤ Fintype.card κ + 1 := by
      have h3 := Submodule.finrank_add_le_finrank_add_finrank V (ℂ ∙ grad w a)
      rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card, hfinV] at h3
      have h4 := finrank_span_le_card (R := ℂ) ({grad w a} : Set (σ → ℂ))
      simp only [Set.toFinset_singleton, Finset.card_singleton] at h4
      omega
    omega
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun j _ => hs0 j
  · intro p hp
    have hp' : p ∈ Submodule.span (MvPolynomial σ ℂ) (Set.range g) := by rw [hg]; exact hp
    clear hp
    induction hp' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), mul_comm (s j), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hsg j)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
    | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ _ hx
end GroundTheory.Heights₂.Heights.JacobianAtCurvePoint
