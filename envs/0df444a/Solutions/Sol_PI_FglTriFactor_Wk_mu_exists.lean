-- Prove2me | solution 1 for PI.FglTriFactor.Wk.mu_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:41.184826+00:00
-- url     : https://prove2.me/submissions/eb8774a5-7beb-4c9d-9e63-a25ed97b505f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_PairSubstXZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_FormalGroupLawExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupTriangles_LiftedThirdRootSubXZeroNeZero
import Theorems.Thm_PI_FglTriFactor_Wk_lam_SerS
import Theorems.Thm_PI_AddIntG_Wk_mem_SerS
import Theorems.Thm_PI_AddIntG_Wk_mvsubst_mem_SerS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
private theorem coeff_pr_X_X (i j : Fin 3) (hij : i ≠ j) (f : MvPowerSeries (Fin 2) ℂ_[p]) (e : Fin 3 →₀ ℕ) :
    MvPowerSeries.coeff e (pr (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (MvPowerSeries.X j) f) =
      if e = Finsupp.single i (e i) + Finsupp.single j (e j) then
        MvPowerSeries.coeff (Finsupp.single 0 (e i) + Finsupp.single 1 (e j)) f else 0 := by
  classical
  have ha : MvPowerSeries.HasSubst
      (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries (Fin 3) ℂ_[p]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by fin_cases s <;> simp)
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s k => (![MvPowerSeries.X i, MvPowerSeries.X j] s : MvPowerSeries (Fin 3) ℂ_[p]) ^ k) =
        MvPowerSeries.monomial (Finsupp.single i (d 0) + Finsupp.single j (d 1)) 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, MvPowerSeries.X_pow_eq,
      MvPowerSeries.monomial_mul_monomial, mul_one]
  have hij' : j ≠ i := Ne.symm hij
  unfold pr
  rw [MvPowerSeries.coeff_subst ha]
  simp only [hprod, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  split_ifs with h
  · rw [finsum_eq_single _ (Finsupp.single 0 (e i) + Finsupp.single 1 (e j)) (fun d hd => by
      rw [if_neg]
      intro h'
      apply hd
      have hi := congrArg (fun f => f i) h'
      have hj := congrArg (fun f => f j) h'
      simp [Finsupp.single_apply, hij, hij'] at hi hj
      ext k
      fin_cases k
      · simp [hi]
      · simp [hj])]
    have e0 : (Finsupp.single (0 : Fin 2) (e i) + Finsupp.single 1 (e j) : Fin 2 →₀ ℕ) 0 = e i := by simp
    have e1 : (Finsupp.single (0 : Fin 2) (e i) + Finsupp.single 1 (e j) : Fin 2 →₀ ℕ) 1 = e j := by simp
    rw [if_pos (by rw [e0, e1]; exact h)]
  · rw [finsum_eq_zero_of_forall_eq_zero]
    intro d
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    simp [Finsupp.single_apply, hij, hij']
end PI.FglTriFactor.Wk
end
end

set_option autoImplicit false
noncomputable section
open PI PI.FglTriFactor PI.FglTriFactor.Wk
open PI.AddIntG.Wk (SerS mem_SerS mvsubst_mem_SerS lam nu wser wv Z3)
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 800000
namespace PI.FglTriFactor.Wk
theorem _root_.solution {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hwq : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∃ μ ∈ SerS S (Fin 3), Lac wq - Lab wq = (MvPowerSeries.X 2 - MvPowerSeries.X 1) * μ := by
  classical
  obtain ⟨μ, hμc⟩ : ∃ μ : MvPowerSeries (Fin 3) ℂ_[p], ∀ e, MvPowerSeries.coeff e μ =
      MvPowerSeries.coeff (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1 + e 2 + 1)) (lam wq) :=
    ⟨fun e => MvPowerSeries.coeff (Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1 + e 2 + 1)) (lam wq),
      fun e => by simp only [MvPowerSeries.coeff_apply]; exact MvPowerSeries.coeff_apply _ _⟩
  have hlam : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d (lam wq) = PowerSeries.coeff (d 0 + d 1 + 1) (wser wq) :=
    fun d => by rw [MvPowerSeries.coeff_apply]; rfl
  refine ⟨μ, (mem_SerS S _).2 (fun e => ?_), ?_⟩
  · rw [hμc]
    exact (mem_SerS S _).1 (lam_SerS hwq) _
  · ext e
    have h02 : (e = Finsupp.single 0 (e 0) + Finsupp.single 2 (e 2)) ↔ e 1 = 0 := by
      constructor
      · intro h
        rw [h]
        simp [Finsupp.single_apply]
      · intro h
        ext k
        fin_cases k <;> simp [Finsupp.single_apply, h]
    have h01 : (e = Finsupp.single 0 (e 0) + Finsupp.single 1 (e 1)) ↔ e 2 = 0 := by
      constructor
      · intro h
        rw [h]
        simp [Finsupp.single_apply]
      · intro h
        ext k
        fin_cases k <;> simp [Finsupp.single_apply, h]
    have hX : ∀ k : Fin 3, (MvPowerSeries.X k : MvPowerSeries (Fin 3) ℂ_[p]) =
        MvPowerSeries.monomial (Finsupp.single k 1) 1 := fun k => by
      rw [← MvPowerSeries.X_pow_eq, pow_one]
    rw [map_sub, Lac, Lab, coeff_pr_X_X 0 2 (by decide), coeff_pr_X_X 0 1 (by decide), sub_mul, map_sub, hX 2, hX 1,
      MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, hμc, hμc, hlam, hlam, hlam, hlam]
    simp only [Finsupp.single_le_iff, h02, h01, one_mul]
    have hidx : ∀ a b : ℕ, a = b → PowerSeries.coeff a (wser wq) = PowerSeries.coeff b (wser wq) :=
      fun a b h => by rw [h]
    by_cases h1 : e 1 = 0 <;> by_cases h2 : e 2 = 0
    · rw [if_pos h1, if_pos h2, if_neg (by omega), if_neg (by omega), sub_self, sub_eq_zero]
      apply hidx
      simp [Finsupp.single_apply, h1, h2]
    · rw [if_pos h1, if_neg h2, if_pos (by omega), if_neg (by omega), sub_zero, sub_zero]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply, h1]
      omega
    · rw [if_neg h1, if_pos h2, if_neg (by omega), if_pos (by omega), zero_sub, zero_sub, neg_inj]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply, h2]
      omega
    · rw [if_neg h1, if_neg h2, if_pos (by omega), if_pos (by omega), sub_self, eq_comm, sub_eq_zero]
      apply hidx
      simp [Finsupp.single_apply, Finsupp.tsub_apply]
      omega
end PI.FglTriFactor.Wk
