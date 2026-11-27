-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_CurveRingFinite_proof_dccff349d400
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:34:45.026538+00:00
-- url     : https://prove2.me/submissions/657f3c1e-48f5-4ceb-a97e-39cf882a9475

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsCurveRingFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PCurveRingFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_mem_integralClosure_b8f04dd67a29
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_CurveRingFiniteAlt_charZero_4a83caadbcde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_X_mem_of_eq_zero_e9e44dbdbf54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_isAlgebraic_ratio_a456e2cba585
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open CurveRingFiniteAlt IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
namespace GroundTheory.Heights₂.Heights.Targets
namespace CurveRingFinite
theorem _root_.solution : CurveRingFinite.Statement := by
  intro K _ ι _ Ω _ y hy
  classical
  have := CurveRingFiniteAlt.charZero y hy.2.2.1
  choose c0 hc0 using hy.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k h => hc0 k (X_mem_of_eq_zero h)
  let r : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c0 p.1⟩
  let κ : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (Set.range r)
  have : FiniteDimensional ℚ κ := IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨p, rfl⟩ := hx
    exact (isAlgebraic_ratio hy c0 hy0 p).isIntegral
  have : NumberField κ :=
    { to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ κ).injective
      to_finiteDimensional := inferInstance }
  let z : (Σ k, ι k) → κ := fun p => ⟨r p, IntermediateField.subset_adjoin ℚ _ ⟨p, rfl⟩⟩
  have hzy : ∀ p q : Σ k, ι k, p.1 = q.1 → ((z p / z q : κ) : Ω) = y p / y q := by
    rintro ⟨k, i⟩ ⟨k', j⟩ h
    simp only at h
    subst h
    exact div_div_div_cancel_right₀ (hy0 k) _ _
  have hyz : ∀ p, z p ≠ 0 → y p ≠ 0 := fun p h hp => h (Subtype.ext (by
    show y p / y ⟨p.1, c0 p.1⟩ = 0
    rw [hp, zero_div]))
  let φ : κ →ₐ[ℤ] Ω := (IntermediateField.val κ).toRingHom.toIntAlgHom
  have hmap : ∀ c : ∀ k, ι k, chartRingZ y c = (chartRingZ z c).map φ := fun c => by
    rw [chartRingZ, chartRingZ, AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    funext p
    exact (hzy p ⟨p.1, c p.1⟩ rfl).symm
  have hκ : ∀ b ∈ curveRing y, b ∈ κ := fun b hb => by
    have h := mem_curveRing.mp hb c0 hy0
    rw [hmap, Subalgebra.mem_map] at h
    obtain ⟨x, -, rfl⟩ := h
    exact x.2
  have hint : ∀ b (hb : b ∈ curveRing y), (⟨b, hκ b hb⟩ : κ) ∈ integralClosure ℤ κ := fun b hb => by
    refine mem_integralClosure z c0 (fun k h => ?_) fun c hc => ?_
    · have h1 := congrArg (fun x : κ => (x : Ω)) h
      have h2 : y ⟨k, c0 k⟩ / y ⟨k, c0 k⟩ = 0 := h1
      exact one_ne_zero ((div_self (hy0 k)).symm.trans h2)
    · have h := mem_curveRing.mp hb c (fun k => hyz _ (hc k))
      rw [hmap, Subalgebra.mem_map] at h
      obtain ⟨x, hx, hxb⟩ := h
      have e : x = ⟨b, hκ b hb⟩ := Subtype.ext hxb
      exact e ▸ hx
  have : Module.Finite ℤ (integralClosure ℤ κ) := inferInstanceAs (Module.Finite ℤ (𝓞 κ))
  let f : curveRing y →ₗ[ℤ] integralClosure ℤ κ :=
    { toFun := fun b => ⟨⟨b, hκ b b.2⟩, hint b b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f fun a b h =>
    Subtype.ext (congrArg (fun w : integralClosure ℤ κ => ((w : κ) : Ω)) h)
end CurveRingFinite
end GroundTheory.Heights₂.Heights.Targets
