-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartResidueDegree_proof_ed6ab4371d6d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:00:22.516095+00:00
-- url     : https://prove2.me/submissions/20554f11-4de1-4c3f-be8a-4fd2dea84647

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsBis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartResidueDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartResidueDegree_exists_chartHom_d3a5e6030201
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartResidueDegree_ratio_23e579f45365
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartResidueDegree_length_quotient_eq_one_0714608bd97e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_iff_656fe0f0fba5


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
open MvPolynomial
noncomputable section
open ChartResidueDegree
namespace GroundTheory.Heights₂.Heights
namespace ChartResidueDegree
theorem _root_.solution (h₁ : ChowFormBirational.Statement) (h₂ : ChartFinite.Statement)
    (h₃ : ChartKernel.Statement) (h₄ : ConeDimOfChowForm.Statement) (h₅ : ConeDimComponent.Statement)
    (h₆ : ChowFormExists.Statement) (h₇ : IncidenceGeneric.Statement) (h₈ : ChartLocalOrder.Statement) :
    ChartResidueDegree.Statement := by
  intro F _ _ n e I W f t u q p _ hI hf hu hq hp hqt hW hqW htW
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := by
    cases e with
    | zero =>
      exfalso
      have h0 : coeff 0 q ≠ 0 := fun h => hq.ne_zero (by rw [eq_C_of_isEmpty q, h, C_0])
      exact hq.not_isUnit (by rw [eq_C_of_isEmpty q]; exact (Ne.isUnit h0).map C)
    | succ k => exact ⟨k, rfl⟩

  have hIW : I ≤ W := le_trans le_sup_left hW.1.1.2
  have hdim := h₄ F n (k + 1 + 1) I f hI hf
  obtain ⟨hWp, hWdim⟩ := h₅ F n (k + 1) I W u hI hdim hu hW
  obtain ⟨g, hg⟩ := h₆ F n (k + 1) W hWp hWdim
  have := hWp.isPrime

  set K := FractionRing (MvPolynomial (Fin n) F ⧸ W)
  set ξ := genPt W with hξdef
  have hξ : ∀ h : MvPolynomial (Fin n) F, aeval ξ h = algebraMap _ K (Ideal.Quotient.mk W h) := by
    intro h
    have : (aeval ξ : MvPolynomial (Fin n) F →ₐ[F] K) =
        (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) K).comp (Ideal.Quotient.mkₐ F W) := by
      ext m; simp [ξ, genPt]
      all_goals rfl
    rw [this]; rfl
  set ℓ := aeval ξ (linForm t) with hℓdef
  have hℓ : ℓ ≠ 0 := by
    rw [hℓdef, hξ]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr
      fun h => htW (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hℓsum : ℓ = ∑ l, algebraMap F K (t l) * ξ l := by
    simp [hℓdef, linForm, map_sum]
    all_goals rfl
  set c : Fin n → K := fun m => algebraMap F K (t m) / ℓ with hcdef
  have hc : ∑ j, c j * ξ j = 1 := by
    simp only [hcdef, div_mul_eq_mul_div, ← Finset.sum_div, ← hℓsum, div_self hℓ]
  have hIG := fun h => h₇ F n (k + 1) W c hc h
  have hc' : ∑ j, c j * genPt W j = 1 := hc
  rw [← hξdef] at hIG
  clear_value c ℓ ξ
  obtain ⟨ΦI, hΦIS, hΦIX, hdeh⟩ :=
    exists_chartHom (e := k + 1) (I := I) hWp.isHomog hIW ξ hξ ℓ hℓdef hℓ c hc

  have hgen := isChowForm_iff.mp hg
  have hpinc : p = incIdeal W (k + 1) := by
    rw [hp, hgen.2]
    have hgq : g ∣ q := by rw [← Ideal.mem_span_singleton, ← hgen.2]; exact hqW
    obtain ⟨a, ha⟩ := hgq
    rcases hq.irreducible.isUnit_or_isUnit ha with hu' | hu'
    · exfalso
      have h1 : (1 : MvPolynomial (Fin (k + 1) × Fin n) F) ∈ incIdeal W (k + 1) := by
        rw [hgen.2, Ideal.span_singleton_eq_top.mpr hu']; trivial
      rw [hIG] at h1
      simp at h1
    · exact Ideal.span_singleton_eq_span_singleton.mpr (Associated.symm ⟨hu'.unit, ha.symm⟩)

  set L := FractionRing (MvPolynomial (Fin (k + 1) × Fin n) K)
  have hunit : ∀ y : Algebra.algebraMapSubmonoid (ChartInc I t (k + 1)) p.primeCompl,
      IsUnit ((algebraMap _ L).comp ΦI y) := by
    rintro ⟨_, s, hs, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [RingHom.comp_apply, hΦIS]
    refine (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr fun h0 => hs ?_
    rw [hpinc]
    exact (hIG s).mpr h0
  let ψ : ChartLoc I t (k + 1) p →+* L := IsLocalization.lift hunit
  have hψ : ∀ a, ψ (algebraMap _ (ChartLoc I t (k + 1) p) a) = algebraMap _ L (ΦI a) :=
    fun a => IsLocalization.lift_eq hunit a
  have hω : ∀ h : MvPolynomial (Fin (k + 1) × Fin n) F, ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
      (algebraMap _ (Localization.AtPrime p) h)) = algebraMap _ L (aeval (genSubst ξ c) h) := by
    intro h
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply _ (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p), hψ, hΦIS]

  set 𝔓 := chartIdeal I t (k + 1) p W with h𝔓def
  obtain ⟨h𝔓prime, -⟩ := h₈ F n (k + 1) I W f t u q p hI hf hu hq hp hqt hW hqW htW
  have hJW : chartIncIdeal W t (k + 1) ≤
      (W.map (chartX I t (k + 1))).comap (Ideal.Quotient.mk (chartIncIdeal I t (k + 1))) := by
    have hz : ∀ a ∈ chartIncIdeal I t (k + 1),
        Ideal.Quotient.mk (chartIncIdeal I t (k + 1)) a ∈ W.map (chartX I t (k + 1)) := fun a ha => by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact Ideal.zero_mem _
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      refine sup_le (fun h hh => ?_) ?_
      · exact Ideal.mem_map_of_mem (chartX I t (k + 1)) hh
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        exact hz _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _
          (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hz _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  have hqS : algebraMap _ (ChartInc I t (k + 1)) q ∈ W.map (chartX I t (k + 1)) := by
    have h0 : algebraMap _ (ChartInc W t (k + 1)) q = 0 := by
      rw [← RingHom.mem_ker, h₃ F n (k + 1) W t hWp htW]; exact hqW
    change Ideal.Quotient.mk _ (rename Sum.inr q) = 0 at h0
    exact hJW (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have h𝔓q : algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
      (algebraMap _ (Localization.AtPrime p) q) ∈ 𝔓 := by
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply _ (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)]
    exact Ideal.mem_map_of_mem _ hqS
  have hcomap : (𝔓.comap (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (Localization.AtPrime p) ≤
        𝔓.comap (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [hp, Ideal.mem_span_singleton] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [Ideal.mem_comap, Ideal.mem_comap, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ h𝔓q
    rw [← (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ h𝔓prime.ne_top) hle]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t (k + 1) p) :=
    h₂ F n (k + 1) I f t p hI hf fun h => hqt (by rw [hp] at h; exact Ideal.mem_span_singleton.mp h)
  have h𝔓max : 𝔓.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔓 hcomap
  have h𝔓ker : 𝔓 ≤ RingHom.ker ψ := by
    rw [h𝔓def, chartIdeal, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro h hh
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, hψ, hΦIX, hdeh h hh, C_0, map_zero]
  have hker : RingHom.ker ψ = 𝔓 := (h𝔓max.eq_of_le (RingHom.ker_ne_top ψ) h𝔓ker).symm

  obtain ⟨t', hD', hrel⟩ := h₁ F n k W g c hWp hg hc'
  rw [← hξdef] at hrel
  set Dt : MvPolynomial (Fin (k + 1) × Fin n) F := ∑ l, C (t l) * pderiv (0, l) g with hDtdef
  have hωC : ∀ a : F, aeval (genSubst ξ c) (C a : MvPolynomial (Fin (k + 1) × Fin n) F) =
      C (algebraMap F K a) := fun a => by rw [aeval_C, MvPolynomial.algebraMap_apply]
  have hB : aeval (genSubst ξ c) (∑ l, C (t' l) * pderiv (0, l) g) ≠ 0 := fun h0 => hD' ((hIG _).mpr h0)
  generalize aeval (genSubst ξ c) (∑ l, C (t' l) * pderiv (0, l) g) = B at hrel hB
  generalize ∑ l, algebraMap F K (t' l) * ξ l = ℓ' at hrel
  obtain ⟨hAt', hη'⟩ := ratio ξ (fun l => algebraMap F K (t l))
    (fun m => aeval (genSubst ξ c) (pderiv (0, m) g)) B ℓ' hB (hℓsum ▸ hℓ) hrel
  have hDtω : aeval (genSubst ξ c) Dt =
      ∑ l, C (algebraMap F K (t l)) * aeval (genSubst ξ c) (pderiv (0, l) g) := by
    rw [hDtdef, map_sum]
    simp only [map_mul, hωC]
  have hAt : aeval (genSubst ξ c) Dt ≠ 0 := by rw [hDtω]; exact hAt'
  have hη : ∀ m, aeval (genSubst ξ c) (pderiv (0, m) g) = C (ξ m / ℓ) * aeval (genSubst ξ c) Dt := by
    intro m; rw [hDtω, hℓsum]; exact hη' m
  have hDt : Dt ∈ p.primeCompl := fun h => hAt ((hIG Dt).mp (by rw [← hpinc]; exact h))

  have hgoodS : ∀ h : MvPolynomial (Fin (k + 1) × Fin n) F,
      ψ (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)
          (algebraMap (MvPolynomial (Fin (k + 1) × Fin n) F) (ChartInc I t (k + 1)) h)) =
        ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
          (algebraMap (MvPolynomial (Fin (k + 1) × Fin n) F) (Localization.AtPrime p) h)) := by
    intro h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hgoodX : ∀ m, ψ (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p) (chartX I t (k + 1) (X m))) =
      ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
        (IsLocalization.mk' (Localization.AtPrime p) (pderiv (0, m) g) (⟨Dt, hDt⟩ : p.primeCompl))) := by
    intro m
    have hne : ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
        (algebraMap (MvPolynomial (Fin (k + 1) × Fin n) F) (Localization.AtPrime p) Dt)) ≠ 0 := by
      rw [hω]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr hAt
    apply mul_right_cancel₀ hne
    have hspec : IsLocalization.mk' (Localization.AtPrime p) (pderiv (0, m) g) (⟨Dt, hDt⟩ : p.primeCompl) *
        algebraMap (MvPolynomial (Fin (k + 1) × Fin n) F) (Localization.AtPrime p) Dt =
          algebraMap _ (Localization.AtPrime p) (pderiv (0, m) g) := IsLocalization.mk'_spec _ _ _
    rw [← map_mul ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p) (IsLocalization.mk' _ _ _)),
      ← map_mul (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)), hspec, hω, hω, hψ, hΦIX,
      aeval_X, ← map_mul, hη m]
  let χ : MvPolynomial (Fin n ⊕ Fin (k + 1) × Fin n) F →+* ChartLoc I t (k + 1) p :=
    (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)).comp
      (Ideal.Quotient.mk (chartIncIdeal I t (k + 1)))
  have hgP : ∀ P : MvPolynomial (Fin n ⊕ Fin (k + 1) × Fin n) F, ∃ o : Localization.AtPrime p,
      ψ (χ P) = ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p) o) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      refine ⟨algebraMap _ _ (C a : MvPolynomial (Fin (k + 1) × Fin n) F), ?_⟩
      rw [← hgoodS]
      show _ = ψ (χ (rename Sum.inr (C a)))
      rw [rename_C]
    | add P₁ P₂ ih₁ ih₂ =>
      obtain ⟨o₁, e₁⟩ := ih₁
      obtain ⟨o₂, e₂⟩ := ih₂
      refine ⟨o₁ + o₂, ?_⟩
      simpa only [map_add] using congrArg₂ (· + ·) e₁ e₂
    | mul_X P v ih =>
      obtain ⟨o₁, e₁⟩ := ih
      cases v with
      | inl m =>
        refine ⟨o₁ * IsLocalization.mk' (Localization.AtPrime p) (pderiv (0, m) g) (⟨Dt, hDt⟩ : p.primeCompl), ?_⟩
        have e₂ : ψ (χ (X (Sum.inl m))) = ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
            (IsLocalization.mk' (Localization.AtPrime p) (pderiv (0, m) g) (⟨Dt, hDt⟩ : p.primeCompl))) := by
          rw [← hgoodX m]
          show _ = ψ (χ (rename Sum.inl (X m)))
          rw [rename_X]
        simpa only [map_mul] using congrArg₂ (· * ·) e₁ e₂
      | inr ij =>
        refine ⟨o₁ * algebraMap _ _ (X ij : MvPolynomial (Fin (k + 1) × Fin n) F), ?_⟩
        have e₂ : ψ (χ (X (Sum.inr ij))) = ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
            (algebraMap _ _ (X ij : MvPolynomial (Fin (k + 1) × Fin n) F))) := by
          rw [← hgoodS (X ij)]
          show _ = ψ (χ (rename Sum.inr (X ij)))
          rw [rename_X]
        simpa only [map_mul] using congrArg₂ (· * ·) e₁ e₂
  have hgood : ∀ x : ChartLoc I t (k + 1) p, ∃ o : Localization.AtPrime p,
      ψ x = ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p) o) := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (ChartInc I t (k + 1)) p.primeCompl) x
    dsimp only
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t (k + 1)) a
    obtain ⟨s₀, hs₀, hs⟩ := s.2
    obtain ⟨o, ho⟩ := hgP P
    have ho' : ψ (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)
        (Ideal.Quotient.mk (chartIncIdeal I t (k + 1)) P)) =
          ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p) o) := ho
    have hne : ψ (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p) s) ≠ 0 := by
      rw [hψ]; exact (hunit s).ne_zero
    refine ⟨o * IsLocalization.mk' (Localization.AtPrime p) (1 : MvPolynomial (Fin (k + 1) × Fin n) F)
      ⟨s₀, hs₀⟩, mul_right_cancel₀ hne ?_⟩
    have hx : IsLocalization.mk' (R := ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)
        (Ideal.Quotient.mk (chartIncIdeal I t (k + 1)) P) s *
        algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p) s =
          algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)
            (Ideal.Quotient.mk (chartIncIdeal I t (k + 1)) P) := IsLocalization.mk'_spec _ _ _
    rw [← map_mul ψ, hx, ho', ← hs,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin (k + 1) × Fin n) F) (Localization.AtPrime p)
        (ChartLoc I t (k + 1) p), ← map_mul ψ, ← map_mul (algebraMap (Localization.AtPrime p) _), mul_assoc,
      IsLocalization.mk'_spec_mk, map_one, mul_one]

  refine length_quotient_eq_one 𝔓 hcomap fun x => ?_
  obtain ⟨o, ho⟩ := hgood x
  exact ⟨o, by rw [← hker, RingHom.mem_ker, map_sub, ho, sub_self]⟩
end ChartResidueDegree
end GroundTheory.Heights₂.Heights
