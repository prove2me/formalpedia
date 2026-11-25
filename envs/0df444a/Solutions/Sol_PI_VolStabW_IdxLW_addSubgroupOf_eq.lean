-- Prove2me | solution 1 for PI.VolStabW.IdxLW.addSubgroupOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:02:37.19465+00:00
-- url     : https://prove2.me/submissions/76984e5f-f555-4fe8-95ff-4723974f46f3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHI
import Definitions.Def_ReciprocityTheory_Automorphisms_InstMainA
import Definitions.Def_ReciprocityTheory_ResidueCardinality_ArtinOntoB
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_LocDensHIL
import Theorems.Thm_P2M_PI_VolStabW_IdxLW_crd_smul__252fb73e95c5
import Theorems.Thm_PI_VolStabW_mem_smulSub
import Theorems.Thm_PI_VolStabW_unifV_spec
import Theorems.Thm_PI_VolStabW_unifV_val
import Theorems.Thm_ReciprocityTheory_Aut_mem_maxIdeal_iff
import Theorems.Thm_ReciprocityTheory_Aut_val_le_exp_neg_one_of_lt_one


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
open PI.VolStabW.IdxLW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)
namespace PI.VolStabW.IdxLW
theorem _root_.solution :
    (lamF b v a M 0).addSubgroupOf (latSub b v a M) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin M × Fin d =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (crdL v b a M) := by
  have hv := unifV_val v
  have h0 := (unifV_spec v).1
  ext x
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, ReciprocityTheory.Aut.mem_maxIdeal_iff]
  constructor
  · intro hx q
    simp only [lamF, mem_smulSub, zero_add, pow_one] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    show Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
      ((x : Fin a → Fin M → Fv F v ⊗[F] E) q.1 q.2.1) q.2.2) < 1
    rw [← hpx]
    simp only [Pi.smul_apply]
    rw [crd_smul', map_mul, hv]
    have hp' : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr (p q.1 q.2.1) q.2.2) ≤ 1 := by
      have h := hp q.1 q.2.1 q.2.2
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    calc WithZero.exp (-1 : ℤ) * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
          (p q.1 q.2.1) q.2.2) ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; decide
  · intro hx
    simp only [lamF, mem_smulSub, zero_add, pow_one]
    refine ⟨(unifV v)⁻¹ • (x : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_⟩
    · intro i j k
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Pi.smul_apply]
      rw [crd_smul', map_mul, map_inv₀, hv]
      have := ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v (hx (i, j, k))
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
            ((x : Fin a → Fin M → Fv F v ⊗[F] E) i j) k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := by gcongr; exact this
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]
end PI.VolStabW.IdxLW
