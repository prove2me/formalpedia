-- Prove2me | solution 1 for PI.VolStabW.IdxHW.ker_redH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:27:16.752988+00:00
-- url     : https://prove2.me/submissions/1fab9e4d-59ed-4efd-87da-5b97bb183b70

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensIdxH
import Theorems.Thm_PI_VolStabW_IdxHW_crdS_smul
import Theorems.Thm_PI_VolStabW_IdxHW_unifV_ne_zero
import Theorems.Thm_PI_VolStabW_IdxHW_val_of_res
import Theorems.Thm_PI_VolStabW_IdxHW_res_of_val
import Theorems.Thm_PI_VolStabW_mem_smulSub
import Theorems.Thm_PI_VolStabW_unifV_val


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing
open PI.VolStabW.IdxHW
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)
namespace PI.VolStabW.IdxHW
theorem _root_.solution :
    (redH b v σ a).ker = (hF b v σ a 0).addSubgroupOf (hermO b v σ a) := by
  ext S
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  have hπ := unifV_val v
  have hπ0 := unifV_ne_zero v
  constructor
  · intro h
    have hc : ∀ i j k, Valued.v (crdS b v σ a S i j k) ≤ WithZero.exp (-1 : ℤ) := by
      intro i j k
      have h1 : residue _ (⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ :
          v.adicCompletionIntegers F) = 0 := congrFun (congrFun (congrFun h i) j) k
      have h2 := val_of_res v _ h1
      exact h2
    refine (mem_smulSub _ _ _).2 ⟨(unifV v)⁻¹ • (S : HermR (Fv F v) σ a), ?_, ?_⟩
    · refine (mem_hermO_iff b v σ a _).2 fun i j k => ?_
      rw [crdS_smul, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hπ]
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v (crdS b v σ a S i j k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := mul_le_mul_right (hc i j k) _
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [zero_add, pow_one, smul_smul, mul_inv_cancel₀ hπ0, one_smul]
  · intro h
    obtain ⟨p, hp, hpS⟩ := (mem_smulSub _ _ _).1 h
    funext i j k
    have hlt : Valued.v (crdS b v σ a S i j k) < 1 := by
      rw [← hpS, zero_add, pow_one, crdS_smul, map_mul, hπ]
      have hp1 : Valued.v (crdS b v σ a p i j k) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((mem_hermO_iff b v σ a p).1 hp i j k)
      calc WithZero.exp (-1 : ℤ) * Valued.v (crdS b v σ a p i j k) ≤ WithZero.exp (-1 : ℤ) * 1 :=
            mul_le_mul_right hp1 _
        _ < 1 := by
          rw [mul_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
          norm_num
    have h3 := res_of_val v ⟨crdS b v σ a S i j k, (mem_hermO_iff b v σ a S).1 S.2 i j k⟩ hlt
    exact h3
end PI.VolStabW.IdxHW
