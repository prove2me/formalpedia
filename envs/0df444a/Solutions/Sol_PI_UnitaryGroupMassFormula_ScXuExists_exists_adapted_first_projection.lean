-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScXuExists.exists_adapted_first_projection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:03:10.938184+00:00
-- url     : https://prove2.me/submissions/5ecf3e8b-3844-4475-b387-1f459e19bec9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicIndexEquality_SplitIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitGen
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso
variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]
namespace PI.UnitaryGroupMassFormula.ScXuExists
theorem _root_.solution (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2)
    (h2K : (2 : K) ≠ 0) (ε : K ⊗[F] E) (hsum : ε + sigT σ ε = 1) (horth : ε * sigT σ ε = 0) :
    ∃ p1 : K ⊗[F] E →+* K, (∀ c : K, p1 (algebraMap K (K ⊗[F] E) c) = c) ∧ p1 ε = 1 ∧
      p1 (sigT σ ε) = 0 ∧
      ∀ r : K ⊗[F] E, r = algebraMap K (K ⊗[F] E) (p1 r) * ε +
        algebraMap K (K ⊗[F] E) (p1 (sigT σ r)) * sigT σ ε := by
  classical
  have hσT : ∀ x : K ⊗[F] E, sigT σ (sigT σ x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul k e => simp [sigT, hσσ]
    | add x y hx hy => simp [map_add, hx, hy]
  have hσA : ∀ c : K, sigT σ (algebraMap K (K ⊗[F] E) c) = algebraMap K (K ⊗[F] E) c := by
    intro c
    simp [sigT, Algebra.TensorProduct.algebraMap_apply]
  have hε2 : ε * ε = ε := by
    calc ε * ε = ε * (ε + sigT σ ε) - ε * sigT σ ε := by ring
      _ = ε := by rw [hsum, horth, mul_one, sub_zero]
  have hfr : Module.finrank K (K ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange, h2]
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  haveI : FiniteDimensional K (K ⊗[F] E) := inferInstance
  haveI : Nontrivial (K ⊗[F] E) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hε0 : ε ≠ 0 := by
    intro h0
    rw [h0, map_zero, add_zero] at hsum
    exact zero_ne_one hsum
  have hδ0 : sigT σ ε ≠ 0 := by
    intro h0
    rw [h0, add_zero] at hsum
    rw [hsum, map_one] at h0
    exact one_ne_zero h0
  have hrn := LinearMap.finrank_range_add_finrank_ker (LinearMap.mulRight K ε)
  rw [hfr] at hrn
  have hker : Module.finrank K (LinearMap.ker (LinearMap.mulRight K ε)) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro h
    apply hδ0
    apply h
    rw [LinearMap.mem_ker, LinearMap.mulRight_apply, mul_comm, horth]
  have hmemε : ε ∈ LinearMap.range (LinearMap.mulRight K ε) :=
    ⟨ε, by rw [LinearMap.mulRight_apply, hε2]⟩
  have hran : Module.finrank K (LinearMap.range (LinearMap.mulRight K ε)) ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro h
    exact hε0 (h ε hmemε)
  have h1 : Module.finrank K (LinearMap.range (LinearMap.mulRight K ε)) = 1 := by omega
  have hex : ∀ r : K ⊗[F] E, ∃ c : K, algebraMap K (K ⊗[F] E) c * ε = r * ε := by
    intro r
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero'
      (⟨ε, hmemε⟩ : LinearMap.range (LinearMap.mulRight K ε))
      (fun h => hε0 (congrArg Subtype.val h))).mp h1 ⟨r * ε, ⟨r, rfl⟩⟩
    refine ⟨c, ?_⟩
    rw [← Algebra.smul_def]
    exact congrArg Subtype.val hc
  have huniq : ∀ c d : K, algebraMap K (K ⊗[F] E) c * ε = algebraMap K (K ⊗[F] E) d * ε →
      c = d := by
    intro c d h
    rw [← Algebra.smul_def, ← Algebra.smul_def, ← sub_eq_zero, ← sub_smul] at h
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hε0)
  choose p hp using hex
  have hpu : ∀ r c, algebraMap K (K ⊗[F] E) c * ε = r * ε → p r = c :=
    fun r c h => huniq _ _ ((hp r).trans h.symm)
  let p1 : K ⊗[F] E →+* K :=
    { toFun := p
      map_one' := hpu 1 1 (by rw [map_one])
      map_mul' := fun r s => hpu (r * s) (p r * p s) (by
        rw [map_mul, mul_assoc, hp s, mul_left_comm, hp r, ← mul_assoc, mul_comm s r])
      map_zero' := hpu 0 0 (by rw [map_zero])
      map_add' := fun r s => hpu (r + s) (p r + p s) (by
        rw [map_add, add_mul, hp r, hp s, add_mul]) }
  refine ⟨p1, fun c => hpu _ c rfl, hpu _ 1 (by rw [map_one, one_mul, hε2]),
    hpu _ 0 (by rw [map_zero, zero_mul, mul_comm, horth]), fun r => ?_⟩
  have h2' : algebraMap K (K ⊗[F] E) (p (sigT σ r)) * sigT σ ε = r * sigT σ ε := by
    have h3 : sigT σ (algebraMap K (K ⊗[F] E) (p (sigT σ r)) * ε) = sigT σ (sigT σ r * ε) := by
      rw [hp (sigT σ r)]
    rwa [map_mul, map_mul, hσA, hσT] at h3
  show r = algebraMap K _ (p r) * ε + algebraMap K _ (p (sigT σ r)) * sigT σ ε
  rw [hp r, h2', ← mul_add, hsum, mul_one]
end PI.UnitaryGroupMassFormula.ScXuExists
