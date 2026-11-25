-- Prove2me | solution 1 for PI.ScRefExists.ApP.isLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:29:58.704255+00:00
-- url     : https://prove2.me/submissions/b131dc1e-b340-4de4-810a-759f8b1d4c27

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PPAssemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Theorems.Thm_PI_ScRefExists_ApP_natCast_not_mem
import Theorems.Thm_PI_ScRefExists_ApP_inv_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
namespace PI.ScRefExists.ApP
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
private theorem mem_Ap_lemma (p : ℕ) (x : I.E) :
    x ∈ Ap I p ↔ ∃ s : ℕ, Nat.Coprime s p ∧ ∃ a : 𝓞 I.E, (s : I.E) * x = (a : I.E) :=
  Iff.rfl
private theorem coe_algebraMap_int_ringOfIntegers (n : ℤ) :
    ((algebraMap ℤ (𝓞 I.E) n : 𝓞 I.E) : I.E) = (n : I.E) := by
  rw [algebraMap_int_eq, eq_intCast]
  exact map_intCast (algebraMap (𝓞 I.E) I.E) n
end PI.ScRefExists.ApP
end
end

set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.S IsDedekindDomain
open scoped TensorProduct nonZeroDivisors
open PI PI.ScRefExists PI.ScRefExists.ApP
open PI.ScRefExists.Sk
variable (I : Formalism.MainNotions.S.AutInst)
namespace PI.ScRefExists.ApP
theorem _root_.solution {p : ℕ} [hpf : Fact p.Prime] :
    IsLocalization (Algebra.algebraMapSubmonoid (𝓞 I.E) (Pz p).primeCompl) (Ap I p) := by
  constructor
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨n, hn, rfl⟩ := hy
    have hnd : ¬ (p : ℤ) ∣ n := fun h => hn (Ideal.mem_span_singleton.mpr h)
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hnd (dvd_zero _)
    refine isUnit_iff_exists_inv.mpr ⟨⟨((n : I.E))⁻¹, inv_mem I hpf.out hnd⟩, ?_⟩
    apply Subtype.ext
    show ((algebraMap ℤ (𝓞 I.E) n : 𝓞 I.E) : I.E) * (n : I.E)⁻¹ = 1
    rw [coe_algebraMap_int_ringOfIntegers]
    exact mul_inv_cancel₀ (Int.cast_ne_zero.mpr hn0)
  · intro z
    obtain ⟨s, hs, a, ha⟩ := (mem_Ap_lemma I p z).mp z.2
    refine ⟨(a, ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
      (⟨(s : ℤ), natCast_not_mem hpf.out hs⟩ : (Pz p).primeCompl)⟩), ?_⟩
    apply Subtype.ext
    show (z : I.E) * ((algebraMap ℤ (𝓞 I.E) (s : ℤ) : 𝓞 I.E) : I.E) = (a : I.E)
    rw [coe_algebraMap_int_ringOfIntegers]
    push_cast
    linear_combination ha
  · intro x y h
    refine ⟨1, ?_⟩
    have h2 : (x : I.E) = y := by
      have h3 := congrArg (fun z : Ap I p => (z : I.E)) h
      exact h3
    have hxy : x = y := NumberField.RingOfIntegers.ext h2
    subst hxy
    rfl
end PI.ScRefExists.ApP
