-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_exists_local_mult_e9c2278c58f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:08:05.906689+00:00
-- url     : https://prove2.me/submissions/c79f5dc8-f72d-470d-9daf-1d2545466e94

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLocallyPrincipalCoprime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLocallyPrincipalCoprime
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_mem_span_of_local_4d6d182557f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocallyPrincipalCoprimeAlt_ne_zero_of_local_415062e9e0fd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
variable {L : Type} [Field L]
namespace GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
theorem _root_.solution {B : Subring L} {M : AddSubgroup L} {ι : Type} [Fintype ι] {a : ι → L}
    (haM : ∀ i, a i ∈ M)
    (hloc : ∀ m : Ideal B, m.IsMaximal → ∃ i, ∀ z ∈ M, ∃ b c : B, b ∉ m ∧ (b : L) * z = c * a i)
    (hM : M ≠ ⊥) (m : Ideal B) (hm : m.IsMaximal) :
    ∃ (g : L) (i : ι), (∀ z ∈ M, g * z ∈ B) ∧ ∃ y : B, (y : L) = g * a i ∧ y ∉ m := by
  obtain ⟨i, hi⟩ := hloc m hm
  have hai := ne_zero_of_local hi hM
  set P := Submodule.span B {a i}
  have hK : ¬ (Finset.univ.inf fun j => P.colon {a j}) ≤ m := by
    rw [hm.isPrime.inf_le']
    rintro ⟨j, -, hj⟩
    obtain ⟨b, c, hbm, hbc⟩ := hi (a j) (haM j)
    apply hbm
    apply hj
    have e : b • a j = c • a i := by rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul, hbc]
    rw [Submodule.mem_colon_singleton, e]
    exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
  obtain ⟨t, htK, htm⟩ := SetLike.not_le_iff_exists.mp hK
  refine ⟨t / a i, i, ?_, t, by field_simp, htm⟩
  intro z hz
  have hzN := mem_span_of_local hloc hz
  have hle : Submodule.span B (Set.range a) ≤ P.comap (t • LinearMap.id) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := Submodule.mem_colon_singleton.mp
      ((Finset.inf_le (f := fun j => P.colon {a j}) (Finset.mem_univ j)) htK)
    simpa using this
  have htz : t • z ∈ P := by simpa using hle hzN
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp htz
  rw [Subring.smul_def, Subring.smul_def, smul_eq_mul, smul_eq_mul] at hc
  have : t / a i * z = c := by
    field_simp
    linear_combination -hc
  rw [this]
  exact c.2
end GroundTheory.Heights₂.Heights.LocallyPrincipalCoprimeAlt
