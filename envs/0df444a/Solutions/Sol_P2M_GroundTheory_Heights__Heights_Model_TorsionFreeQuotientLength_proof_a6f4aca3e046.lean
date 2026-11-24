-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_proof_a6f4aca3e046
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:39:51.116552+00:00
-- url     : https://prove2.me/submissions/9e6b9f39-9222-4579-ab29-dfc2e907af02

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_pi_quot_smul_top_69b4b0f38899
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Module Submodule
open scoped Pointwise
namespace GroundTheory.Heights₂.Heights.Model
namespace TorsionFreeQuotientLength
theorem _root_.solution : TorsionFreeQuotientLength.Statement := by
  intro R _ _ _ hdim M _ _ _ r hr a ha
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by rw [hdim]; rfl)
  rw [Submodule.ideal_span_singleton_smul, ← TorsionFreeQuotientLength.length_pi_quot_smul_top]

  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent_of_isDomain R M
  rw [hr] at hs
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hs
  let v : Fin r → M := fun i => (e.symm i : M)
  have hv : LinearIndependent R v := hli.comp e.symm e.symm.injective
  let φ : (Fin r → R) →ₗ[R] M :=
    Finsupp.linearCombination R v ∘ₗ (Finsupp.linearEquivFunOnFinite R R (Fin r)).symm.toLinearMap
  have hφ : Function.Injective φ :=
    (show Function.Injective (Finsupp.linearCombination R v) from hv).comp
      (Finsupp.linearEquivFunOnFinite R R (Fin r)).symm.injective
  have hrange : LinearMap.range φ = span R (Set.range v) := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Finsupp.range_linearCombination]
  have htor : ∀ x : M, ∃ c : R, c ≠ 0 ∧ c • x ∈ LinearMap.range φ := by
    have h1 := rank_quotient_add_rank_of_isDomain (span R (Set.range v))
    rw [rank_span hv, Cardinal.mk_range_eq v hv.injective, Cardinal.mk_fin, hr] at h1
    have h0 : Module.rank R (M ⧸ span R (Set.range v)) = 0 := by
      by_contra h
      have h2 := add_le_add_right (Cardinal.one_le_iff_ne_zero.mpr h) (r : Cardinal)
      rw [add_comm (r : Cardinal) (Module.rank _ _), h1] at h2
      exact absurd h2 (by exact_mod_cast Nat.not_succ_le_self r)
    intro x
    obtain ⟨c, hc, hcx⟩ := rank_eq_zero_iff.mp h0 (Submodule.Quotient.mk x)
    exact ⟨c, hc, hrange ▸ (Quotient.mk_eq_zero _).mp (by rwa [← Quotient.mk_smul] at hcx)⟩

  have hLtop : Module.length R ((Fin r → R) ⧸ (a • ⊤ : Submodule R (Fin r → R))) ≠ ⊤ := by
    rw [TorsionFreeQuotientLength.length_pi_quot_smul_top]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (Module.length_ne_top_iff.mpr
      (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero ha)))
  let T : Submodule R M := a • ⊤
  have hfg : ∀ N : Submodule R M, N.FG → LinearMap.range φ ≤ N →
      Module.length R (N.map T.mkQ) ≤ Module.length R ((Fin r → R) ⧸ (a • ⊤ : Submodule R (Fin r → R))) := by
    intro N hN hφN
    have : Module.Finite R N := Module.Finite.iff_fg.mpr hN
    let φN : (Fin r → R) →ₗ[R] N := φ.codRestrict N fun y => hφN (LinearMap.mem_range_self φ y)
    have hφN' : Function.Injective φN := fun y z h => hφ (congrArg Subtype.val h)
    have hreg : Function.Injective fun x : N => a • x := fun x y h =>
      Subtype.ext (smul_right_injective M ha (congrArg Subtype.val h))
    have hfin : IsFiniteLength R (N ⧸ LinearMap.range φN) := by
      refine TorsionFreeQuotientLength.isFiniteLength_of_torsion _ fun q => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨c, hc, y, hy⟩ := htor x
      refine ⟨c, hc, ?_⟩
      rw [← Quotient.mk_smul, Quotient.mk_eq_zero]
      exact ⟨y, Subtype.ext hy⟩
    have hle : (a • ⊤ : Submodule R N) ≤ LinearMap.ker (T.mkQ ∘ₗ N.subtype) := fun x hx => by
      obtain ⟨b, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, mkQ_apply,
        Quotient.mk_eq_zero, Submodule.coe_smul, Submodule.subtype_apply]
      exact smul_mem_pointwise_smul _ a ⊤ mem_top
    have hmap : N.map T.mkQ = LinearMap.range ((a • ⊤ : Submodule R N).liftQ _ hle) := by
      rw [range_liftQ, LinearMap.range_comp, range_subtype]
    rw [hmap, ← TorsionFreeQuotientLength.length_quot_smul_eq φN hφN' hreg hfin]
    exact Module.length_le_of_surjective _ (LinearMap.surjective_rangeRestrict _)

  let S : Set ℕ := {n | ∃ N : Submodule R M, N.FG ∧ LinearMap.range φ ≤ N ∧
    Module.length R (N.map T.mkQ) = n}
  have hSb : BddAbove S := ⟨(Module.length R ((Fin r → R) ⧸ (a • ⊤ : Submodule R (Fin r → R)))).toNat, by
    rintro n ⟨N, hN, hφN, hn⟩
    have := hfg N hN hφN
    rw [hn] at this
    simpa using ENat.toNat_le_toNat this hLtop⟩
  have hφfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  have hne0 : Module.length R ((LinearMap.range φ).map T.mkQ) ≠ ⊤ :=
    ne_top_of_le_ne_top hLtop (hfg _ hφfg le_rfl)
  have hSne : S.Nonempty := ⟨_, LinearMap.range φ, hφfg, le_rfl, (ENat.natCast_toNat hne0).symm⟩
  obtain ⟨N₀, hN₀, hφN₀, hm⟩ := Nat.sSup_mem hSne hSb
  have htop : N₀.map T.mkQ = ⊤ := by
    refine eq_top_iff.mpr fun q _ => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_contra hx
    have hN₁ : (N₀ ⊔ span R {x}).FG := hN₀.sup (fg_span_singleton x)
    have hx1 : Submodule.Quotient.mk x ∈ (N₀ ⊔ span R {x}).map T.mkQ :=
      mem_map_of_mem (mem_sup_right (mem_span_singleton_self x))
    have hlt : N₀.map T.mkQ < (N₀ ⊔ span R {x}).map T.mkQ :=
      lt_of_le_of_ne (map_mono le_sup_left) fun h => hx (by rw [h]; exact hx1)
    have hne : Module.length R ((N₀ ⊔ span R {x}).map T.mkQ) ≠ ⊤ :=
      ne_top_of_le_ne_top hLtop (hfg _ hN₁ (hφN₀.trans le_sup_left))
    have h1 := le_csSup hSb ⟨_, hN₁, hφN₀.trans le_sup_left, (ENat.natCast_toNat hne).symm⟩
    have h2 : Module.length R (N₀.map T.mkQ) < Module.length R ((N₀ ⊔ span R {x}).map T.mkQ) := by
      rw [Module.length_submodule, Module.length_submodule]
      refine Order.height_strictMono hlt ?_
      rw [← Module.length_submodule, hm]
      exact ENat.natCast_lt_top _
    rw [hm, ← ENat.natCast_toNat hne] at h2
    exact absurd (ENat.natCast_lt_natCast.mp h2) (not_lt.mpr h1)
  calc Module.length R (M ⧸ T) = Module.length R (N₀.map T.mkQ) := by
        rw [htop, Module.length_top]
    _ ≤ Module.length R ((Fin r → R) ⧸ (a • ⊤ : Submodule R (Fin r → R))) := hfg N₀ hN₀ hφN₀
end TorsionFreeQuotientLength
end GroundTheory.Heights₂.Heights.Model
