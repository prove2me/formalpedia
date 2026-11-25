-- Prove2me | solution 1 for PI.Dv.Tr.choose_gh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:03:52.327526+00:00
-- url     : https://prove2.me/submissions/26ab0102-21d0-4809-afcd-ca0b9abdcd45

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SameFormAllLevels
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_ESMulESOfNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_CharacteristicPolynomialCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_NormAtAddLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_RankIdentity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_PerSAlg
import Theorems.Thm_PI_Dv_Tr_rank_one_sandwich
import Theorems.Thm_PI_Dv_Tr_select
import Theorems.Thm_PI_Dv_Tr_exists_map_to
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_PI_Dv_Tr_eps_idem
import Theorems.Thm_PI_Dv_Tr_mul_eS
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
open PI PI.Dv PI.Dv.Tr
open PI.Dv Module
variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
namespace PI.Dv.Tr
theorem _root_.solution (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (hM : nS T P0 s = 1) :
    ∃ (cB : MonoidAlgebra K G → K) (g h : Fin (nS T P s) → G),
      (∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s)) ∧
      IsUnit (Matrix.of fun j i => cB (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i))) := by
  classical
  set n := nS T P s with hn
  set τ := (T.tau s).asAlgebraHom with hτ
  set p := τ (eps P0) with hpdef
  have hp : p * p = p := by rw [hpdef, ← map_mul, eps_idem]
  have h1 : finrank K (LinearMap.range p) = 1 := hM
  choose cB hcB using fun a : MonoidAlgebra K G => rank_one_sandwich p hp h1 (τ a)
  have hcB' : ∀ a, τ (eps P0 * a * eps P0) = cB a • p := fun a => by
    rw [map_mul, map_mul]; exact hcB a
  have hlift : ∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s) := by
    intro a
    rw [mul_eS, hcB', map_smul, ← mul_eS]
  refine ⟨cB, ?_⟩
  obtain ⟨w0, hw0r, hw0⟩ : ∃ w0 ∈ LinearMap.range p, w0 ≠ 0 := by
    have : LinearMap.range p ≠ ⊥ := by
      intro h; rw [h, finrank_bot] at h1; exact zero_ne_one h1
    exact Submodule.exists_mem_ne_zero_of_ne_bot this
  have hpw0 : p w0 = w0 := by
    obtain ⟨y, rfl⟩ := hw0r
    rw [← Module.End.mul_apply, hp]
  set u : G → T.W s := fun g => τ (eps P * MonoidAlgebra.of K G g) w0 with hu
  have hallu : ∀ a, τ (eps P * a) w0 ∈ Submodule.span K (Set.range u) := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => exact Submodule.subset_span ⟨y, rfl⟩
    | add x y hx hy => rw [mul_add, map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
    | smul r x hx => rw [mul_smul_comm, map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ hx
  have hspanu : Submodule.span K (Set.range u) = LinearMap.range (τ (eps P)) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact ⟨τ (MonoidAlgebra.of K G y) w0, by rw [hu]; simp only [map_mul, Module.End.mul_apply]⟩
    · rintro _ ⟨w, rfl⟩
      obtain ⟨X, hX⟩ := exists_map_to (K := K) w0 w hw0
      obtain ⟨a, rfl⟩ := T.irr s X
      rw [← hX, ← Module.End.mul_apply, ← map_mul]
      exact hallu a
  have hfinu : finrank K (Submodule.span K (Set.range u)) = n := by rw [hspanu]; rfl
  obtain ⟨g, hgli, -⟩ := select u n hfinu
  set r : G → (Fin n → K) := fun h i => cB (MonoidAlgebra.of K G h * eps P * MonoidAlgebra.of K G (g i)) with hr
  have hkey : ∀ h i, p (τ (MonoidAlgebra.of K G h) (u (g i))) =
      cB (MonoidAlgebra.of K G h * eps P * MonoidAlgebra.of K G (g i)) • w0 := by
    intro h i
    have := congrArg (fun X : Module.End K (T.W s) => X w0)
      (hcB' (MonoidAlgebra.of K G h * eps P * MonoidAlgebra.of K G (g i)))
    simp only [LinearMap.smul_apply, hpw0] at this
    rw [← this, hu]
    simp only [map_mul, Module.End.mul_apply]
    rw [← hpdef, hpw0]
  have hspanr : Submodule.span K (Set.range r) = ⊤ := by
    by_contra hne
    obtain ⟨ψ, hψ0, hψ⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    set lam : Fin n → K := fun i => ψ (fun j => if i = j then 1 else 0) with hlam
    have hψr : ∀ h, ∑ i, r h i * lam i = 0 := by
      intro h
      have hmem : ψ (r h) ∈ (Submodule.span K (Set.range r)).map ψ :=
        Submodule.mem_map_of_mem (Submodule.subset_span ⟨h, rfl⟩)
      rw [hψ, Submodule.mem_bot] at hmem
      rw [LinearMap.pi_apply_eq_sum_univ ψ (r h)] at hmem
      simpa [smul_eq_mul, hlam] using hmem
    set u' := ∑ i, lam i • u (g i) with hu'
    have hpu : ∀ a, p (τ a u') = 0 := by
      intro a
      induction a using MonoidAlgebra.induction_on with
      | of h =>
        rw [hu', map_sum, map_sum]
        simp only [map_smul, hkey, smul_smul]
        rw [← Finset.sum_smul]
        have : ∑ i, lam i * cB (MonoidAlgebra.of K G h * eps P * MonoidAlgebra.of K G (g i)) = 0 := by
          rw [← hψr h]; refine Finset.sum_congr rfl fun i _ => ?_; rw [hr]; ring
        rw [this, zero_smul]
      | add x y hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, add_zero]
      | smul c x hx => rw [map_smul, LinearMap.smul_apply, map_smul, hx, smul_zero]
    have hu'0 : u' = 0 := by
      by_contra hne'
      obtain ⟨X, hX⟩ := exists_map_to (K := K) u' w0 hne'
      obtain ⟨a, rfl⟩ := T.irr s X
      have := hpu a
      rw [hX, hpw0] at this
      exact hw0 this
    have hlam0 : lam = 0 := by
      have := (Fintype.linearIndependent_iff.mp hgli) lam (by
        have h0 := hu'0
        rw [hu'] at h0
        simpa [Function.comp_apply] using h0)
      funext i; exact this i
    apply hψ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ ψ x]
    simp only [LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    have : ψ (fun j => if i = j then 1 else 0) = 0 := congrFun hlam0 i
    rw [this, smul_zero]
  have hfinr : finrank K (Submodule.span K (Set.range r)) = n := by
    rw [hspanr, finrank_top, Module.finrank_fin_fun]
  obtain ⟨h, hhli, -⟩ := select r n hfinr
  refine ⟨g, h, hlift, ?_⟩
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  exact hhli
end PI.Dv.Tr
