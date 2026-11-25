-- Prove2me | solution 1 for PI.Dv.Tr.deg_ge_of_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:54:47.209905+00:00
-- url     : https://prove2.me/submissions/20a04e9d-9eca-4dd1-b503-d2b3fd39fcd9

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_FinalCor
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IdempotentTransfer_DegGeOfInj
import Theorems.Thm_PI_Dv_Tr_real_ext
import Theorems.Thm_PI_Dv_Tr_mem_zl
import Theorems.Thm_Formalism_F_covolAntiSameRank
import Theorems.Thm_Formalism_F_covolEqGram
import Theorems.Thm_Formalism_F_covolPos
import Theorems.Thm_Formalism_F_gramDetLe


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.Tr
open Formalism.HN
variable {R : Type} [Ring R] {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
namespace PI.Dv.Tr
theorem _root_.solution (ρ : V →+ E) (ρ' : W →+ F) (L : Submodule R V) (M : Submodule R W)
    (hL : IsLat ρ L) (hM : IsLat ρ' M) (f : V →+ W) (hfM : ∀ x ∈ L, f x ∈ M)
    (hinj : ∀ x ∈ L, f x = 0 → x = 0) (hrk : rk ρ L = rk ρ' M) (C : ℝ) (hC : 0 < C)
    (hb : ∀ x ∈ L, ‖ρ' (f x)‖ ≤ C * ‖ρ x‖) :
    deg ρ L - (rk ρ L : ℝ) * Real.log C ≤ deg ρ' M := by
  classical
  have := hL.2
  have := hM.2
  set zL := zl ρ L with hzL
  set zM := zl ρ' M with hzM
  set n := Module.finrank ℤ zL with hn
  let b := Module.finBasis ℤ zL
  have hmemL : ∀ u : zL, ∃ x ∈ L, ρ x = (u : E) := fun u => mem_zl.mp u.2
  choose x hxL hxe using fun i => hmemL (b i)
  let w : Fin n → F := fun i => ρ' (f (x i))
  have hsumL : ∀ a : Fin n → ℤ, (∑ i, a i • x i) ∈ L := fun a =>
    L.sum_mem fun i _ => L.toAddSubgroup.zsmul_mem (hxL i) (a i)
  have hw_comb : ∀ a : Fin n → ℤ, ∑ i, a i • w i = ρ' (f (∑ i, a i • x i)) := by
    intro a
    simp [w, map_sum, map_zsmul]
  have hb_comb : ∀ a : Fin n → ℤ, ∑ i, a i • ((b i : zL) : E) = ρ (∑ i, a i • x i) := by
    intro a
    simp [map_sum, map_zsmul, hxe]
  have hbound : ∀ a : Fin n → ℤ, ‖∑ i, (a i : ℝ) • w i‖ ≤ C * ‖∑ i, (a i : ℝ) • ((b i : zL) : E)‖ := by
    intro a
    simp only [Int.cast_smul_eq_zsmul]
    rw [hw_comb, hb_comb]
    exact hb _ (hsumL a)
  have hreal := real_ext (fun i => ((b i : zL) : E)) w C hbound
  have hgram := Formalism.F.gramDetLe E F (Fin n) (fun i => ((b i : zL) : E)) w C hreal
  have hli : LinearIndependent ℤ w := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    rw [hw_comb] at ha
    have hy := hsumL a
    have h1 : f (∑ i, a i • x i) = 0 := hM.1 (hfM _ hy) M.zero_mem (by rw [ha, map_zero])
    have h2 := hinj _ hy h1
    have h3 : ∑ i, a i • b i = 0 := by
      apply Subtype.ext
      have : ((∑ i, a i • b i : zL) : E) = ∑ i, a i • ((b i : zL) : E) := by simp
      rw [this, hb_comb, h2, map_zero]
      rfl
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent) a h3
  set N' : Submodule ℤ F := Submodule.span ℤ (Set.range w) with hN'
  have hN'M : N' ≤ zM := by
    rw [hN', Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact mem_zl.mpr ⟨f (x i), hfM _ (hxL i), rfl⟩
  have hdisc : DiscreteTopology N' :=
    DiscreteTopology.of_continuous_injective (f := Submodule.inclusion hN'M)
      (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective _)
  let bN : Module.Basis (Fin n) ℤ N' := Module.Basis.span hli
  have hbN : ∀ i, ((bN i : N') : F) = w i := fun i => by
    first
    | exact Module.Basis.span_apply hli i
    | exact congrArg Subtype.val (Module.Basis.span_apply hli i)
    | simp [bN]
  have hcovN' := Formalism.F.covolEqGram F N' (Fin n) bN
  have hcovL := Formalism.F.covolEqGram E zL (Fin n) b
  have hrkN' : Formalism.F.rk N' = Formalism.F.rk zM := by
    have h1 : Formalism.F.rk N' = n := by
      unfold Formalism.F.rk
      rw [Module.finrank_eq_card_basis bN, Fintype.card_fin]
    rw [h1]
    exact hrk
  have hanti := Formalism.F.covolAntiSameRank F N' zM hM.2 hN'M hrkN'
  have hposM := Formalism.F.covolPos F zM hM.2
  have hposL := Formalism.F.covolPos E zL hL.2
  have hbNeq : (fun i => ((bN i : N') : F)) = w := funext hbN
  rw [hbNeq] at hcovN'
  have hGb : 0 ≤ (Matrix.gram ℝ (fun i => ((b i : zL) : E))).det := by
    by_contra hneg
    push Not at hneg
    rw [hcovL, Real.sqrt_eq_zero'.mpr hneg.le] at hposL
    exact lt_irrefl _ hposL
  have hle : Formalism.F.covol N' ≤ C ^ n * Formalism.F.covol zL := by
    rw [hcovN', hcovL]
    calc Real.sqrt (Matrix.gram ℝ w).det
        ≤ Real.sqrt (C ^ (2 * Fintype.card (Fin n)) * (Matrix.gram ℝ (fun i => ((b i : zL) : E))).det) :=
          Real.sqrt_le_sqrt hgram
      _ = C ^ n * Real.sqrt (Matrix.gram ℝ (fun i => ((b i : zL) : E))).det := by
          rw [Real.sqrt_mul (by positivity), Fintype.card_fin, pow_mul, ← pow_mul, mul_comm 2 n, pow_mul,
            Real.sqrt_sq (by positivity)]
  have hfin : Formalism.F.covol zM ≤ C ^ n * Formalism.F.covol zL := hanti.trans hle
  have hlog := Real.log_le_log hposM hfin
  rw [Real.log_mul (by positivity) hposL.ne', Real.log_pow] at hlog
  unfold deg rk Formalism.F.deg Formalism.F.rk
  rw [← hzL, ← hzM, ← hn]
  linarith
end PI.Dv.Tr
