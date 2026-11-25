-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.stdLat_smul_idx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:54:26.757385+00:00
-- url     : https://prove2.me/submissions/738399fd-28a4-423c-82d3-c126ee5bf4be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_relIdx_ne_zero_of_cover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply
section
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
section Idx
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
end Idx
private theorem mem_lattice_iff_exists_int_comb (L : PeriodPair) (z : ℂ) :
    z ∈ L.lattice ↔ ∃ p q : ℤ, (p : ℂ) * L.ω₁ + (q : ℂ) * L.ω₂ = z := by
  exact PeriodPair.mem_lattice
section Theta
variable {a : ℕ} {b c : ℤ} {d : ℕ}
end Theta
end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution (L : PeriodPair) (m : Type*) [Fintype m] {N : ℕ} (hN : N ≠ 0) :
    ((stdLat L m).map (smulHom (N : ℂ))).relIndex (stdLat L m) ≠ 0 := by
  have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hN1 : (N : ℤ) ≠ 0 := hN0.ne'
  refine relIdx_ne_zero_of_cover (ι := m → (Set.Ico (0 : ℤ) N × Set.Ico (0 : ℤ) N))
    (fun f j => (((f j).1 : ℤ) : ℂ) * L.ω₁ + (((f j).2 : ℤ) : ℂ) * L.ω₂) ?_ ?_
  · intro f
    simp only [PI.ULS.stdLat, AddSubgroup.mem_pi]
    intro j _
    exact (mem_lattice_iff_exists_int_comb L _).mpr ⟨_, _, rfl⟩
  · intro b hb
    simp only [PI.ULS.stdLat, AddSubgroup.mem_pi] at hb
    have hb' : ∀ j, ∃ p q : ℤ, (p : ℂ) * L.ω₁ + (q : ℂ) * L.ω₂ = b j :=
      fun j => (mem_lattice_iff_exists_int_comb L (b j)).mp (hb j (Set.mem_univ _))
    choose p q hpq using hb'
    refine ⟨fun j => (⟨p j % N, Set.mem_Ico.mpr ⟨Int.emod_nonneg _ hN1, Int.emod_lt_of_pos _ hN0⟩⟩,
      ⟨q j % N, Set.mem_Ico.mpr ⟨Int.emod_nonneg _ hN1, Int.emod_lt_of_pos _ hN0⟩⟩), ?_⟩
    refine ⟨fun j => ((p j / N : ℤ) : ℂ) * L.ω₁ + ((q j / N : ℤ) : ℂ) * L.ω₂, ?_, ?_⟩
    · simp only [PI.ULS.stdLat, AddSubgroup.mem_pi]
      intro j _
      exact (mem_lattice_iff_exists_int_comb L _).mpr ⟨_, _, rfl⟩
    · funext j
      simp only [smulHom_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← hpq j]
      have d1 : (N : ℤ) * (p j / N) + p j % N = p j := by
        first
        | exact Int.ediv_add_emod _ _
        | exact EuclideanDomain.div_add_mod _ _
        | exact Int.mul_ediv_add_emod _ _
        | (rw [add_comm]; exact Int.emod_add_ediv _ _)
        | (rw [Int.emod_def]; ring)
        | (have e := Int.emod_def (p j) (N : ℤ); linarith)
      have d2 : (N : ℤ) * (q j / N) + q j % N = q j := by
        first
        | exact Int.ediv_add_emod _ _
        | exact EuclideanDomain.div_add_mod _ _
        | exact Int.mul_ediv_add_emod _ _
        | (rw [add_comm]; exact Int.emod_add_ediv _ _)
        | (rw [Int.emod_def]; ring)
        | (have e := Int.emod_def (q j) (N : ℤ); linarith)
      have c1 : (N : ℂ) * ((p j / N : ℤ) : ℂ) + ((p j % N : ℤ) : ℂ) = (p j : ℂ) := by
        exact_mod_cast d1
      have c2 : (N : ℂ) * ((q j / N : ℤ) : ℂ) + ((q j % N : ℤ) : ℂ) = (q j : ℂ) := by
        exact_mod_cast d2
      try dsimp only
      linear_combination L.ω₁ * c1 + L.ω₂ * c2
end PI.UnitaryGroupMassFormula.UnimodLocStd
