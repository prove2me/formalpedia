-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_proof_233a7424f562
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:29.13251+00:00
-- url     : https://prove2.me/submissions/2907b910-91bb-4a3c-ac70-67706e1c206c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartFirstGroupDvd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PIncidenceGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFirstGroupDvd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_dvd_sub_aeval_73ee1f5d5857
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFirstGroupDvd_exists_injective_880cc7794019
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartIncDomain_aeval_genPt_93dec95d46e3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incIdeal_iff_08da98833496


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
theorem _root_.solution (h₁ : IncidenceGeneric.Statement) : ChartFirstGroupDvd.Statement := by
  intro F _ n e I f t hI hf ht
  have := hI.isPrime
  obtain ⟨φ, hφinj, hφX, hφU⟩ := exists_injective I t e hI ht
  set τ : (FractionRing (MvPolynomial (Fin n) F ⧸ I)) := aeval (genPt I) (linForm t) with hτdef
  have hτ : τ ≠ 0 := by
    rw [hτdef, ChartIncDomain.aeval_genPt, Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact ht
  have hτsum : τ = ∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t l) * genPt I l := by
    simp [hτdef, linForm]
  set cK : Fin n → (FractionRing (MvPolynomial (Fin n) F ⧸ I)) := fun m => algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m) / τ with hcK
  have homogComponent_comm_first_action : ∑ j, cK j * genPt I j = 1 := by
    simp only [hcK, div_mul_eq_mul_div, ← Finset.sum_div, ← hτsum]
    exact div_self hτ
  have hcKm : ∀ m, cK m = τ⁻¹ * algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ I)) (t m) := fun m => by
    simp only [hcK]
    ring
  have hfI : f ∈ incIdeal I (e + 1) := mem_incIdeal_iff.mpr ((hf.2 f).mpr dvd_rfl)
  have hgen : aeval (genSubst (genPt I) cK) f = 0 := (h₁ F n (e + 1) I cK homogComponent_comm_first_action f).mp hfI
  set θ : MvPolynomial (Fin n) (ChartInc I t e) := ∑ m, X m * C (chartX I t e (X m)) with hθ
  set σ : Fin n → MvPolynomial (Fin n) (ChartInc I t e) :=
    fun m => X m - θ * C (chartX I t e (C (t m))) with hσ
  have hdvd := dvd_sub_aeval θ σ (fun m => ⟨-C (chartX I t e (C (t m))), by simp only [hσ]; ring⟩)
    (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f))
  suffices h0 : aeval σ (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (firstGroup f)) = 0 by
    rw [h0, sub_zero] at hdvd
    exact hdvd
  apply map_injective φ hφinj
  rw [map_zero]
  set ρ : MvPolynomial (Fin (e + 1) × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I)) →+* MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))) :=
    eval₂Hom (C.comp C) (fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))))
      (X ij.2) (fun i => C (X (i, ij.2))) ij.1) with hρ
  have key : (MvPolynomial.map φ).comp ((aeval σ).toRingHom.comp
      ((MvPolynomial.map (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e))).comp
        (aeval (fun ij : Fin (e + 1) × Fin n =>
          Fin.cases (motive := fun _ => MvPolynomial (Fin n) (MvPolynomial (Fin e × Fin n) F))
            (X ij.2) (fun i => C (X (i, ij.2))) ij.1)).toRingHom)) =
      ρ.comp (aeval (genSubst (genPt I) cK) :
        MvPolynomial (Fin (e + 1) × Fin n) F →ₐ[F] MvPolynomial (Fin (e + 1) × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ I))).toRingHom := by
    have hρ0 : ∀ m, ρ (X (0, m)) = X m := fun m => by simp [hρ]
    have hρs : ∀ (i : Fin e) m, ρ (X (i.succ, m)) = C (X (i, m)) := fun i m => by simp [hρ]
    have hρC : ∀ k, ρ (C k) = C (C k) := fun k => by simp [hρ]
    apply MvPolynomial.ringHom_ext
    · intro a
      have hCa : algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a) = chartX I t e (C a) := by
        change Ideal.Quotient.mk _ (rename Sum.inr (C a)) = Ideal.Quotient.mk _ (rename Sum.inl (C a))
        rw [rename_C, rename_C]
      simp [hρC, hCa, hφX]
    · rintro ⟨i, m⟩
      cases i using Fin.cases with
      | zero =>
        simp [hρ0, hσ, hθ, hφX, hρC, genSubst]
        rw [hcKm]
        simp only [map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
      | succ i =>
        simp [hρs, hρC, hφU, genSubst]
        rw [hcKm]
        simp only [map_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => by ring
  have := RingHom.congr_fun key f
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hgen, map_zero] at this
  exact this
end GroundTheory.Heights₂.Heights.ChartFirstGroupDvd
