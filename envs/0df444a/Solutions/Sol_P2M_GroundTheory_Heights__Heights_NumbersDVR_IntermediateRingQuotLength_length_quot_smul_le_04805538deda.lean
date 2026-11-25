-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_IntermediateRingQuotLength_length_quot_smul_le_04805538deda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:24:08.463453+00:00
-- url     : https://prove2.me/submissions/88135a5d-d3ad-498a-8646-71b5cb3cf885

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBlowUpOrderLe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntermediateRingQuotLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntermediateRingQuotLength_smul_top_eq_span_79ee9c715187
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_isFiniteLength_of_torsion_7ebbc28a2765
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_quot_smul_eq_8287c0362885


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
universe u
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength
namespace GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength
theorem _root_.solution {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [Ring.KrullDimLE 1 A] {M : Type*} [AddCommGroup M] [Module A M] (φ : A →ₗ[A] M)
    (hφ : Function.Injective φ) (htor : ∀ x : M, ∃ c : A, c ≠ 0 ∧ c • x ∈ LinearMap.range φ)
    {a : A} (ha : a ≠ 0) (hreg : Function.Injective fun x : M => a • x) :
    Module.length A (M ⧸ (a • ⊤ : Submodule A M)) ≤ Module.length A (A ⧸ Ideal.span {a}) := by
  rw [← smul_top_eq_span]
  have hLtop : Module.length A (A ⧸ (a • ⊤ : Submodule A A)) ≠ ⊤ := by
    rw [smul_top_eq_span]
    exact Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton A (mem_nonZeroDivisors_of_ne_zero ha))
  let T : Submodule A M := a • ⊤
  have hfg : ∀ N : Submodule A M, N.FG → LinearMap.range φ ≤ N →
      Module.length A (N.map T.mkQ) ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := by
    intro N hN hφN
    have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
    let φN : A →ₗ[A] N := φ.codRestrict N fun y => hφN (LinearMap.mem_range_self φ y)
    have hφN' : Function.Injective φN := fun y z h => hφ (congrArg Subtype.val h)
    have hregN : Function.Injective fun x : N => a • x := fun x y h =>
      Subtype.ext (hreg (congrArg Subtype.val h))
    have hfin : IsFiniteLength A (N ⧸ LinearMap.range φN) := by
      refine GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.isFiniteLength_of_torsion _
        fun q => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨c, hc, y, hy⟩ := htor x
      refine ⟨c, hc, ?_⟩
      rw [← Quotient.mk_smul, Quotient.mk_eq_zero]
      exact ⟨y, Subtype.ext hy⟩
    have hle : (a • ⊤ : Submodule A N) ≤ LinearMap.ker (T.mkQ ∘ₗ N.subtype) := fun x hx => by
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
        Quotient.mk_eq_zero, Submodule.coe_smul, Submodule.subtype_apply]
      exact smul_mem_pointwise_smul _ a ⊤ mem_top
    have hmap : N.map T.mkQ = LinearMap.range ((a • ⊤ : Submodule A N).liftQ _ hle) := by
      rw [range_liftQ, LinearMap.range_comp, range_subtype]
    rw [hmap, ← GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength.length_quot_smul_eq φN hφN'
      hregN hfin]
    exact Module.length_le_of_surjective _ (LinearMap.surjective_rangeRestrict _)
  let S : Set ℕ := {n | ∃ N : Submodule A M, N.FG ∧ LinearMap.range φ ≤ N ∧
    Module.length A (N.map T.mkQ) = n}
  have hSb : BddAbove S := ⟨(Module.length A (A ⧸ (a • ⊤ : Submodule A A))).toNat, by
    rintro n ⟨N, hN, hφN, hn⟩
    have := hfg N hN hφN
    rw [hn] at this
    simpa using ENat.toNat_le_toNat this hLtop⟩
  have hφfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  have hne0 : Module.length A ((LinearMap.range φ).map T.mkQ) ≠ ⊤ :=
    ne_top_of_le_ne_top hLtop (hfg _ hφfg le_rfl)
  have hSne : S.Nonempty := ⟨_, LinearMap.range φ, hφfg, le_rfl, (ENat.natCast_toNat hne0).symm⟩
  obtain ⟨N₀, hN₀, hφN₀, hm⟩ := Nat.sSup_mem hSne hSb
  have htop : N₀.map T.mkQ = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_contra hx
    have hN₁ : (N₀ ⊔ span A {x}).FG := hN₀.sup (fg_span_singleton x)
    have hx1 : Submodule.Quotient.mk x ∈ (N₀ ⊔ span A {x}).map T.mkQ :=
      mem_map_of_mem (mem_sup_right (mem_span_singleton_self x))
    have hlt : N₀.map T.mkQ < (N₀ ⊔ span A {x}).map T.mkQ :=
      lt_of_le_of_ne (map_mono le_sup_left) fun h => hx (by rw [h]; exact hx1)
    have hne : Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) ≠ ⊤ :=
      ne_top_of_le_ne_top hLtop (hfg _ hN₁ (hφN₀.trans le_sup_left))
    have h1 := le_csSup hSb ⟨_, hN₁, hφN₀.trans le_sup_left, (ENat.natCast_toNat hne).symm⟩
    have h2 : Module.length A (N₀.map T.mkQ) < Module.length A ((N₀ ⊔ span A {x}).map T.mkQ) := by
      rw [Module.length_submodule, Module.length_submodule]
      refine Order.height_strictMono hlt ?_
      rw [← Module.length_submodule, hm]
      exact ENat.natCast_lt_top _
    rw [hm, ← ENat.natCast_toNat hne] at h2
    exact absurd (ENat.natCast_lt_natCast.mp h2) (not_lt.mpr h1)
  calc Module.length A (M ⧸ T) = Module.length A (N₀.map T.mkQ) := by
        rw [htop, Module.length_top]
    _ ≤ Module.length A (A ⧸ (a • ⊤ : Submodule A A)) := hfg N₀ hN₀ hφN₀
end GroundTheory.Heights₂.Heights.NumbersDVR.IntermediateRingQuotLength
