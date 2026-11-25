-- Prove2me | solution 1 for UpperTheory.HF.diff_mult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:47:00.658173+00:00
-- url     : https://prove2.me/submissions/2019292f-e170-4aaa-abca-157a7603f168

import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_GrpBridge
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_VdTameWild
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDifferentExponentDenominator
import Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffMult
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
import Theorems.Thm_GlobalTheory_DifferentElement_mult_ratio
import Theorems.Thm_UpperTheory_HF_Formalism_HC_HostRaw_el_pos
import Theorems.Thm_UpperTheory_HF_grp_bridge
import Theorems.Thm_UpperTheory_HF_vd_tame_wild
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open UpperTheory.HF
open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise
namespace UpperTheory.HF
theorem _root_.solution :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})], (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l ∧ multiplicity P (span {(l : 𝓞 H.E)}) = H.el l ∧ (¬ l ∣ H.el l → multiplicity P (differentIdeal ℤ (𝓞 H.E)) = H.el l - 1) ∧ (l ∣ H.el l → H.el l ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E))) := by
  intro φ H l hl P _ _
  haveI := H.galois
  obtain ⟨-, -, hram, -⟩ := grp_bridge H hl P
  have hmap : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) = span {(l : 𝓞 H.E)} := by
    simp [Ideal.map_span]
  have hne : (span {(l : ℤ)}).map (algebraMap ℤ (𝓞 H.E)) ≠ ⊥ :=
    map_ne_bot_of_ne_bot (by simp [hl.ne_zero])
  have hmult : multiplicity P (span {(l : 𝓞 H.E)}) = H.el l := by
    rw [← hmap, ← IsDedekindDomain.ramificationIdx_eq_multiplicity _ _ hne, hram]
  have hmem : (l : 𝓞 H.E) ∈ P := by
    have hle : span {(l : 𝓞 H.E)} ≤ P := by
      rw [← hmap]
      exact map_le_of_le_comap (Ideal.LiesOver.over (P := P) (p := span {(l : ℤ)})).le
    exact hle (Ideal.mem_span_singleton_self _)
  have hrat := GlobalTheory.DifferentElement.mult_ratio H.E l hl P inferInstance hmem
  rw [hmult, Nat.factorization_def _ hl] at hrat
  have hel0 : (0 : ℝ) < H.el l := by exact_mod_cast HostRaw.el_pos _ l
  have hvd : H.vdH l = (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) / H.el l := by
    have hr := congrArg (fun q : ℚ => (q : ℝ)) hrat
    push_cast at hr
    simp only [HostRaw.vdH]
    exact hr.symm
  have h1 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = H.el l * H.vdH l := by
    rw [hvd]
    field_simp
  obtain ⟨htw1, htw2, -⟩ := vd_tame_wild H hl
  refine ⟨h1, hmult, fun hnd => ?_, fun hd => ?_⟩
  · have hv := htw1 hnd
    have hle : 1 ≤ H.el l := HostRaw.el_pos _ l
    have h2 : (multiplicity P (differentIdeal ℤ (𝓞 H.E)) : ℝ) = ((H.el l - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle, h1, hv]
      field_simp
      push_cast
      ring
    exact_mod_cast h2
  · have hv := htw2 hd
    have h2 : (H.el l : ℝ) ≤ multiplicity P (differentIdeal ℤ (𝓞 H.E)) := by
      rw [h1]
      nlinarith
    exact_mod_cast h2
end UpperTheory.HF
