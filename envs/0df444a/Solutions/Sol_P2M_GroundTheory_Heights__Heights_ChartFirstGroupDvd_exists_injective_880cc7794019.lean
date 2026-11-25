-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_exists_injective_880cc7794019
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:51:57.491649+00:00
-- url     : https://prove2.me/submissions/314c70b5-f287-4136-8e88-53f0b17ed604

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFirstGroupDvd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_ker_aeval_eta_898fe41a71f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceGeneric_map_genSubst_b65b00dc21c1


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
open GroundTheory.Heights₂.Heights.ChartFirstGroupDvd
variable {F : Type} [Field F] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ChartFirstGroupDvd
theorem _root_.solution (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (t : Fin n → F) (e : ℕ)
    (hI : IsProjPrime I) (ht : linForm t ∉ I) :
    ∃ φ : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I)),
      Function.Injective φ ∧
      (∀ g, φ (chartX I t e g) = C (aeval ((aeval (genPt I) (linForm t))⁻¹ • genPt I) g)) ∧
      ∀ im, φ (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im)) =
        genSubst ((aeval (genPt I) (linForm t))⁻¹ • genPt I)
          (fun m => algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m)) im := by
  set K := FractionRing (MvPolynomial (Fin n) F ⧸ I)
  set η : Fin n → K := (aeval (genPt I) (linForm t))⁻¹ • genPt I with hη
  set ψ : MvPolynomial (Fin n) F →+* K := (aeval η).toRingHom with hψ
  have hJeq : RingHom.ker ψ = I ⊔ Ideal.span {linForm t - 1} := by
    rw [← ChartIncDomain.ker_aeval_eta I t hI ht]
    rfl
  set J := RingHom.ker ψ with hJ

  set q : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) F ⧸ J := Ideal.Quotient.mk J with hq
  set ζ : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (X m) with hζ
  set c : Fin n → MvPolynomial (Fin n) F ⧸ J := fun m => q (C (t m)) with hc'
  have hc : ∑ l, c l * ζ l = 1 := by
    have h1 : q (linForm t) = 1 := by
      rw [← sub_eq_zero, ← map_one q, ← map_sub, hq, Ideal.Quotient.eq_zero_iff_mem, hJeq]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
    rw [← h1, linForm, map_sum]
    simp only [map_mul, hζ, hc']

  set γ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) :=
    eval₂Hom (C.comp (q.comp C)) (Sum.elim (fun m => C (ζ m)) (genSubst ζ c)) with hγ
  have hγX : ∀ g, γ (rename Sum.inl g) = C (q g) := by
    intro g
    have : γ.comp (rename Sum.inl).toRingHom = C.comp q := by
      apply MvPolynomial.ringHom_ext
      · intro a; simp [hγ]
      · intro m; simp [hγ, hζ]
    exact RingHom.congr_fun this g
  have hker : chartIncIdeal I t e ≤ RingHom.ker γ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      rw [Ideal.mem_comap, RingHom.mem_ker, hγX, hq, (Ideal.Quotient.eq_zero_iff_mem).mpr (hJeq ▸ hg),
        map_zero]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      have hC : ∑ l, C (c l) * C (ζ l) = (1 : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J)) := by
        rw [← C_1, ← hc, map_sum]
        simp only [C_mul]
      simp only [map_sum, map_mul, hγ, coe_eval₂Hom, eval₂_X, Sum.elim_inl, Sum.elim_inr]
      simp only [genSubst, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum, hC, mul_one,
        sub_self]
  set γbar : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e →+* MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) :=
    Ideal.Quotient.lift (chartIncIdeal I t e) γ (fun a ha => RingHom.mem_ker.mp (hker ha)) with hγbar
  set χ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e :=
    (Ideal.Quotient.mk (chartIncIdeal I t e)).comp (rename Sum.inl).toRingHom with hχ
  have hJX : ∀ a ∈ J, χ a = 0 := by
    intro a ha
    rw [hJeq] at ha
    rw [hχ, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)

  set β : MvPolynomial (Fin e × Fin n) (MvPolynomial (Fin n) F ⧸ J) →+*
      MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e :=
    eval₂Hom (Ideal.Quotient.lift J χ hJX)
      (fun im => Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr im))) with hβ
  have hβγ : β.comp γ = Ideal.Quotient.mk (chartIncIdeal I t e) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [hβ, hγ, hq, hχ]
    · rintro (m | im)
      · simp [hβ, hγ, hζ, hq, hχ]
      · have h0 : Ideal.Quotient.mk (chartIncIdeal I t e)
            (∑ l, X (Sum.inr (im.1, l)) * X (Sum.inl l)) = 0 := by
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.subset_span ⟨im.1, rfl⟩)
        simp only [map_sum, map_mul] at h0
        simp [hβ, hγ, hζ, hc', hq, hχ, genSubst]
        rw [h0, zero_mul]
  have hleft : ∀ x : MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ chartIncIdeal I t e, β (γbar x) = x := by
    intro x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) x
    rw [hγbar, Ideal.Quotient.lift_mk]
    exact RingHom.congr_fun hβγ g
  have hinj : Function.Injective γbar := Function.LeftInverse.injective hleft

  have hjinj : Function.Injective (RingHom.kerLift ψ) := RingHom.kerLift_injective ψ
  refine ⟨(MvPolynomial.map (RingHom.kerLift ψ)).comp γbar, (map_injective _ hjinj).comp hinj, ?_, ?_⟩
  · intro g
    have h' : γbar (Ideal.Quotient.mk _ (rename Sum.inl g)) = C (q g) := by
      rw [hγbar, Ideal.Quotient.lift_mk]
      exact hγX g
    change MvPolynomial.map (RingHom.kerLift ψ) (γbar (Ideal.Quotient.mk _ (rename Sum.inl g))) = _
    rw [h', map_C, hq, RingHom.kerLift_mk]
    rfl
  · intro im
    have h' : γbar (Ideal.Quotient.mk _ (rename Sum.inr (X im))) = genSubst ζ c im := by
      rw [hγbar, Ideal.Quotient.lift_mk, rename_X]
      simp [hγ]
    change MvPolynomial.map (RingHom.kerLift ψ) (γbar (Ideal.Quotient.mk _ (rename Sum.inr (X im)))) = _
    rw [h', IncidenceGeneric.map_genSubst]
    congr 1
    · funext m
      change RingHom.kerLift ψ (Ideal.Quotient.mk _ (X m)) = _
      rw [RingHom.kerLift_mk, hψ]
      simp [η]
    · funext m
      change RingHom.kerLift ψ (Ideal.Quotient.mk _ (C (t m))) = _
      rw [RingHom.kerLift_mk, hψ]
      simp
      rfl
end GroundTheory.Heights₂.Heights.ChartFirstGroupDvd
