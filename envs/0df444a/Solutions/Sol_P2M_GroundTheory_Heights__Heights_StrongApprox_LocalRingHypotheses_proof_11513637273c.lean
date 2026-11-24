-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_StrongApprox_LocalRingHypotheses_proof_11513637273c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:34:42.764548+00:00
-- url     : https://prove2.me/submissions/f2a722e6-b768-4316-937f-a71616a34f12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StrongApproximation_PLocalRingHypotheses
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_SA_OFam_card_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.StrongApprox
open NumberField IsDedekindDomain TensorProduct ReciprocityTheory.ChartRestriction.G.SA
namespace GroundTheory.Heights₂.Heights.StrongApprox
namespace LocalRingHypotheses
theorem _root_.solution : LocalRingHypotheses.Statement := by
  intro F E _ _ _ _ _ c h2 hc v
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ h2

  have hcc : ∀ x, c (c x) = x := by
    have hcard : Fintype.card (E ≃ₐ[F] E) ≤ 2 := h2 ▸ AlgEquiv.card_le
    have hpos := orderOf_pos c
    have hle : orderOf c ≤ Fintype.card (E ≃ₐ[F] E) := orderOf_le_card_univ
    have hne : orderOf c ≠ 1 := fun h => hc (orderOf_eq_one_iff.mp h)
    have ho : orderOf c = 2 := by omega
    intro x
    have h := pow_orderOf_eq_one c
    rw [ho, pow_two] at h
    exact DFunLike.congr_fun h x
  have htmul : ∀ (a : v.adicCompletion F) (b : E), sigV c v (a ⊗ₜ b) = a ⊗ₜ c b := by
    intro a b
    simp [sigV]
  have hsig_incl : ∀ x : E, sigV c v (inclV E v x) = inclV E v (c x) := by
    intro x
    simp [inclV, htmul]

  have hinv : ∀ x, sigV c v (sigV c v x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rw [htmul, htmul, hcc]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

  obtain ⟨α, hα⟩ : ∃ α, c α ≠ α := by
    by_contra h
    push Not at h
    exact hc (AlgEquiv.ext h)
  set β : E := α - c α with hβdef
  have hcβ : c β = -β := by simp [hβdef, hcc]
  have hβ0 : β ≠ 0 := sub_ne_zero.mpr (Ne.symm hα)
  have h2F : (2 : F) ≠ 0 := two_ne_zero
  have h2k : (2 : v.adicCompletion F) ≠ 0 := by
    rw [← map_ofNat (algebraMap F (v.adicCompletion F)) 2]
    exact fun h => h2F ((algebraMap F (v.adicCompletion F)).injective (h.trans (map_zero _).symm))

  set t : Kv E v := (1 : v.adicCompletion F) ⊗ₜ β with htdef
  have ht : IsUnit t :=
    (isUnit_iff_ne_zero.mpr hβ0).map (Algebra.TensorProduct.includeRight : E →ₐ[F] Kv E v)
  have hσt : sigV c v t = -t := by rw [htdef, htmul, hcβ, TensorProduct.tmul_neg]

  have hli : LinearIndependent F ![(1 : E), β] := by
    rw [LinearIndependent.pair_iff]
    intro s u hsu
    have hsu' : algebraMap F E s + algebraMap F E u * β = 0 := by
      simpa [Algebra.smul_def] using hsu
    have hc' : algebraMap F E s + algebraMap F E u * -β = 0 := by
      have := congrArg c hsu'
      rwa [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hcβ, map_zero] at this
    have hs : algebraMap F E (2 * s) = 0 := by
      rw [map_mul, map_ofNat]
      linear_combination hsu' + hc'
    have hs0 : s = 0 := by
      have := (algebraMap F E).injective (hs.trans (map_zero _).symm)
      exact (mul_eq_zero.mp this).resolve_left h2F
    subst hs0
    rw [map_zero, zero_add] at hsu'
    have hu : algebraMap F E u = 0 := (mul_eq_zero.mp hsu').resolve_right hβ0
    exact ⟨rfl, (algebraMap F E).injective (hu.trans (map_zero _).symm)⟩
  let B : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hB : ∀ i, B i = ![(1 : E), β] i := fun i => by
    simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]
  let BK : Module.Basis (Fin 2) (v.adicCompletion F) (Kv E v) := Algebra.TensorProduct.basis _ B

  have hdecomp : ∀ x : Kv E v, ∃ a b : v.adicCompletion F,
      x = algebraMap _ _ a + algebraMap _ _ b * t := by
    intro x
    refine ⟨BK.repr x 0, BK.repr x 1, ?_⟩
    conv_lhs => rw [← BK.sum_repr x]
    rw [Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def]
    simp [BK, Algebra.TensorProduct.basis_apply, hB, htdef]
  have hinj : Function.Injective (algebraMap (v.adicCompletion F) (Kv E v)) := by
    have : Nontrivial (Kv E v) := ⟨⟨0, t, (ht.ne_zero).symm⟩⟩
    exact (algebraMap (v.adicCompletion F) (Kv E v)).injective

  have hfix : ∀ x, sigV c v x = x ↔ x ∈ Set.range (algebraMap (v.adicCompletion F) (Kv E v)) := by
    intro x
    constructor
    · intro hx
      obtain ⟨a, b, rfl⟩ := hdecomp x
      rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, hσt] at hx
      have h2b : algebraMap _ (Kv E v) (2 * b) * t = 0 := by
        rw [map_mul, map_ofNat]
        linear_combination -hx
      have hb : b = 0 := by
        have := (ht.mul_left_eq_zero).mp h2b
        rw [← map_zero (algebraMap (v.adicCompletion F) (Kv E v))] at this
        exact (mul_eq_zero.mp (hinj this)).resolve_left h2k
      exact ⟨a, by simp [hb]⟩
    · rintro ⟨a, rfl⟩
      exact AlgHom.commutes _ a

  have hrank : Module.finrank (v.adicCompletion F) (Kv E v) = 2 := by
    rw [Module.finrank_baseChange, h2]

  have hred : IsReduced (Kv E v) := by
    have : Algebra.IsSeparable F E := inferInstance
    have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
    exact Algebra.FormallyUnramified.isReduced_of_field (v.adicCompletion F) (Kv E v)
  refine ⟨hinv, hfix, hrank, hred, h2k, hsig_incl, ?_⟩
  intro N J x y
  simp only [hf, map_sum, map_mul, Matrix.map_apply, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, hsig_incl]
  rfl
end LocalRingHypotheses
end GroundTheory.Heights₂.Heights.StrongApprox
