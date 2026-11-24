-- Prove2me | solution 1 for PI.FockOneDegW.exists_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:40.508372+00:00
-- url     : https://prove2.me/submissions/13ae3f08-f265-450a-9fdd-581d7ea17eb8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_RaisingLoweringSplit
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_SameBlockOfPosC
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_left
import Theorems.Thm_FockRaiseLowInner_fockInner_sum_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
namespace PI.FockOneDegW
theorem _root_.solution {σ : Type} {V N : Submodule ℂ (MvPolynomial σ ℂ)} [FiniteDimensional ℂ V]
    (hNV : N < V) : ∃ c ∈ V, c ≠ 0 ∧ ∀ n ∈ N, fockInner n c = 0 := by
  classical
  have : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le hNV.le
  set k := Module.finrank ℂ N
  let b := Module.finBasis ℂ N
  let Φ : MvPolynomial σ ℂ →ₗ[ℂ] (Fin k → ℂ) := LinearMap.pi (fun i => innerL ((b i : N) : MvPolynomial σ ℂ))
  let Ψ := Φ.domRestrict V
  have h1 := LinearMap.finrank_range_add_finrank_ker Ψ
  have h2 : Module.finrank ℂ (LinearMap.range Ψ) ≤ k := by
    have := Submodule.finrank_le (LinearMap.range Ψ)
    simpa [Module.finrank_fin_fun] using this
  have h3 : k < Module.finrank ℂ V := Submodule.finrank_lt_finrank_of_lt hNV
  have h4 : LinearMap.ker Ψ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h4
  refine ⟨(x : MvPolynomial σ ℂ), x.2, fun h => hx0 (Subtype.ext h), fun n hn => ?_⟩
  have hx' : ∀ i, fockInner ((b i : N) : MvPolynomial σ ℂ) (x : MvPolynomial σ ℂ) = 0 := by
    intro i
    have := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [Ψ, Φ, innerL] using this
  have hsum := b.sum_repr ⟨n, hn⟩
  have hn' : n = ∑ i, (b.repr ⟨n, hn⟩ i) • ((b i : N) : MvPolynomial σ ℂ) := by
    conv_lhs => rw [show n = ((⟨n, hn⟩ : N) : MvPolynomial σ ℂ) from rfl, ← hsum]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  rw [hn', fockInner_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [fockInner_smul_left, hx' i, mul_zero]
end PI.FockOneDegW
