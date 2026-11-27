-- Prove2me | solution 1 for PositivityTheory.FamInh.exists_lift_ine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:21:18.048128+00:00
-- url     : https://prove2.me/submissions/e2efe729-cd83-496a-aaa2-7332f4825f43

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_WeilBound_CoreStatements_PlaceConnectedComponents_ArtinA
import Theorems.Thm_PositivityTheory_FamInh_mem_Ine_of_integral
import Theorems.Thm_PositivityTheory_FamInh_coe_res_smul
import Theorems.Thm_PositivityTheory_FamInh_res_restrictScalars
import Theorems.Thm_PositivityTheory_FamInh_exists_lift_dec
import Theorems.Thm_ReciprocityTheory_Gal_continuousSMul_intCl
import Theorems.Thm_ReciprocityTheory_Gal_eq_of_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Gal_isInvariant_intCl
import Theorems.Thm_ReciprocityTheory_Gal_primeBelow_smul
import Theorems.Thm_ReciprocityTheory_Gal_under_primeBelow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open PositivityTheory PositivityTheory.FamInh
variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra L Ω]
  [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] [IsAlgClosure L Ω]
variable [IsGalois K L]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 L)}
namespace PositivityTheory.FamInh
theorem _root_.solution (hw : IsPlaceOver A w) {τ : L ≃ₐ[K] L} (hτ : τ ∈ w.asIdeal.inertia (L ≃ₐ[K] L)) :
    ∃ σ ∈ Ine (F := K) A, AlgEquiv.restrictNormalHom L σ = τ := by
  obtain ⟨σ, hσ, rfl⟩ := exists_lift_dec hw (Ideal.inertia_le_stabilizer _ hτ)
  letI : TopologicalSpace (IntCl L Ω) := ⊥
  haveI : DiscreteTopology (IntCl L Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl L Ω
  haveI := isInvariant_intCl L Ω
  set Q := primeBelow (F := L) A with hQ
  haveI : Q.LiesOver w.asIdeal := ⟨(under_primeBelow hw).symm⟩
  have hmap : Q = Q.map (intAut L σ : IntCl L Ω →+* IntCl L Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
    exact (valuation_apply_lt_one_iff ((Dec (F := K) A).inv_mem hσ) (b : Ω)).symm
  let φ : (IntCl L Ω ⧸ Q) ≃ₐ[𝓞 L ⧸ w.asIdeal] (IntCl L Ω ⧸ Q) :=
    AlgEquiv.ofRingEquiv (f := Ideal.quotientEquiv Q Q (intAut L σ) hmap) (by
      intro r
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
      change Ideal.Quotient.mk Q (intAut L σ (algebraMap (𝓞 L) (IntCl L Ω) x)) =
        Ideal.Quotient.mk Q (algebraMap (𝓞 L) (IntCl L Ω) x)
      rw [Ideal.Quotient.eq, mem_primeBelow]
      have h1 := (hw _).2 (hτ x)
      change A.valuation (σ (algebraMap L Ω (x : L)) - algebraMap L Ω (x : L)) < 1
      rw [← coe_res_smul, ← map_sub]
      exact h1)
  obtain ⟨⟨ρ, hρQ⟩, hρ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[L] Ω) w.asIdeal Q φ
  have hρQ' : ρ • Q = Q := hρQ
  have hcong : ∀ b : IntCl L Ω, A.valuation (σ (b : Ω) - ρ (b : Ω)) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (ρ • b) = Ideal.Quotient.mk Q (intAut L σ b) :=
      DFunLike.congr_fun hρ (Ideal.Quotient.mk Q b)
    exact Ideal.Quotient.eq.1 h1.symm
  have hdec : ρ • A = A := by
    refine eq_of_valuation_lt_one_iff L fun b hb => ?_
    let b' : IntCl L Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := L) (ρ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hρQ']
  have hρD : (ρ.restrictScalars K : G K Ω) ∈ Dec (F := K) A := hdec
  refine ⟨(ρ.restrictScalars K)⁻¹ * σ, mem_Ine_of_integral
    ((Dec (F := K) A).mul_mem ((Dec (F := K) A).inv_mem hρD) hσ) fun b hb => ?_, ?_⟩
  · rw [← valuation_apply_lt_one_iff hρD, map_sub, AlgEquiv.mul_apply, mul_inv_apply]
    exact hcong ⟨b, hb.tower_top⟩
  · rw [map_mul, map_inv, res_restrictScalars, inv_one, one_mul]
end PositivityTheory.FamInh
