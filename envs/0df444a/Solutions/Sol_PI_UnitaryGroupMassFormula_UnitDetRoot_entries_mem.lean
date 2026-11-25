-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnitDetRoot.entries_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:00:33.057124+00:00
-- url     : https://prove2.me/submissions/9bfd4c21-a273-4a3a-a9fd-ed41dcf93367

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_NsmulRelIdxMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitDeterminantRoot_DetMemOfEntries
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_theta_mem
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnitDetRoot_single_mem_stdLat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnitDetRoot
open PI
namespace PI.UnitaryGroupMassFormula.UnitDetRoot
theorem _root_.solution {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
    {m : Type} [Fintype m] [DecidableEq m] {Λa : AddSubgroup (m → ℂ)}
    (hH : Hyp a b c d ha hd lam hlam m Λa) {δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)} (hA : admitted a b d ha hd lam hlam m Λa δ)
    (i j : m) : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j ∈ KF b d := by
  have he : Pi.single j (lam * a) ∈ UnitDetRootDefs.stdLat (UnitDetRootDefs.cmL a b d ha hd lam hlam) m :=
    single_mem_stdLat j
  obtain ⟨n1, hn1, -, h1⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hH.2.2.2.2 he
  have h2 : (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (n1 • Pi.single j (lam * a)) ∈
      UnitDetRootDefs.imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa :=
    AddSubgroup.mem_map_of_mem _ h1.1
  obtain ⟨n2, hn2, -, h3⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero hA.2.1 h2
  have h4 := (AddSubgroup.mem_inf.mp h3).1
  rw [UnitDetRootDefs.stdLat, AddSubgroup.mem_pi] at h4
  have h5 := h4 i (Set.mem_univ _)
  rw [Submodule.mem_toAddSubgroup, PeriodPair.mem_lattice] at h5
  obtain ⟨p, q, hpq⟩ := h5
  have hs : Pi.single j (lam * (a : ℂ)) = (lam * (a : ℂ)) • Pi.single j (1 : ℂ) := by
    ext k
    simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  rw [hs, map_nsmul, map_smul, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
    nsmul_eq_mul, nsmul_eq_mul] at hpq
  change (p : ℂ) * (lam * a) + q * (lam * UnitDetRootDefs.cmTheta b d) = _ at hpq
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hN : (n2 : ℂ) * n1 * a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by exact_mod_cast hn2.ne') (by exact_mod_cast hn1.ne')) ha0
  have hM : LinearMap.toMatrix' (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) i j =
      ((p : ℂ) * a + q * UnitDetRootDefs.cmTheta b d) / ((n2 : ℂ) * n1 * a) := by
    rw [LinearMap.toMatrix'_apply, eq_div_iff hN]
    apply mul_left_cancel₀ hlam
    simp only [LinearEquiv.coe_coe] at hpq ⊢
    linear_combination -hpq
  rw [hM]
  exact div_mem (add_mem (mul_mem (intCast_mem _ _) (natCast_mem _ _))
    (mul_mem (intCast_mem _ _) (theta_mem b d)))
    (mul_mem (mul_mem (natCast_mem _ _) (natCast_mem _ _)) (natCast_mem _ _))
end PI.UnitaryGroupMassFormula.UnitDetRoot
